module KarmaBrief where

import System.Random 
import Control.Monad.State
import Data.List 
import Data.Ord
-- check this is allowed TODO
import Data.Maybe (listToMaybe)
import Control.Monad (when)
import Debug.Trace
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent (threadDelay)
import System.IO (hFlush, stdout)
import Data.Maybe (fromMaybe)

-- Cards
data Suit = Clubs | Diamonds | Hearts | Spades
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Rank = R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | RJ | RQ | RK | RA
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- TODO check that you can add the Ord here
data Card = Card { rank :: Rank, suit :: Suit }
  deriving (Eq, Show, Read, Ord)

type Deck = [Card]
type Pile = [Card]  

-- Players
type PlayerId   = Int
type PlayerName = String

data Player = Player
  { pId       :: PlayerId
  , pName     :: PlayerName
  , hand      :: [Card]
  , faceUp    :: [Card]
  , faceDown  :: [Card]
  , strategy  :: String
  } deriving (Show)

-- Game state 
data GameState = GameState
  { players       :: [Player]    -- clockwise order
  , currentIx     :: Int         -- index into players
  , drawPile      :: Deck
  , discardPile   :: Pile
  , burnedPiles   :: [Pile]
  , rng           :: StdGen      -- random number generator
  , finishedOrder :: [PlayerId]
  , messages      :: String
  , order         :: Bool
  , nines         :: Bool  -- rule extensions
  , threes        :: Bool
  , eights        :: Bool
  } deriving (Show)


-- Different extension rules we can toggle
data Extension = ExtReverse8 | ExtThree3s | ExtNineClubs
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Step 1 
--------------------------------------------------------------------------------
legalPlay :: Maybe Card -> Card -> Bool
-- Determines if legal play. Legal if discard pile empty, or higher than top of
-- discard. If 7, go below instead. If 2, always legal. If 8, ignore 8. If 10,
-- remove discard.
legalPlay Nothing _ = True
legalPlay (Just (Card pileRank _)) (Card cardRank _)
  | cardRank == R2 || cardRank == R8 || cardRank == R10 = True
  | cardRank >= pileRank = True
  | pileRank == R7 && cardRank <= pileRank = True
  | pileRank == R8 = True
  | otherwise = False

validPlays :: Maybe Card -> Deck -> Deck
validPlays pile deck = [x | x <- deck, legalPlay pile x]

dealCards :: Int -> State GameState Deck
-- We take in BOTH Int and GameState, it takes in the gamestate and returns the new deck (gross why is it like this)
dealCards 0 = pure []
dealCards n = do
  drawPile <- gets drawPile
  case drawPile of
    [] -> pure []
    (card:rest) -> do
      modify (\x -> x {drawPile = rest })
      rest <- dealCards (n-1)
      pure (card:rest)


giveWastePileTo :: Player -> State GameState ()
giveWastePileTo player = do
  discard <- gets discardPile
  let updatedPlayer = player { hand = hand player ++ discard }
  updatePlayer updatedPlayer
  modify $ \gs -> gs { discardPile = [] }

updatePlayer :: Player -> State GameState ()
updatePlayer updatedPlayer = modify $ \gs ->
  gs { players = map (\p -> if pId p == pId updatedPlayer then updatedPlayer else p) (players gs) }

replenishCards :: Player -> State GameState ()
replenishCards player = do
  draw <- gets drawPile
  let handCards = hand player
      nToDraw = max 0 (3 - length handCards)
      (drawn, rest) = splitAt nToDraw draw
      updatedPlayer = player { hand = handCards ++ drawn }
  updatePlayer updatedPlayer
  modify $ \gs -> gs { drawPile = rest }


shuffleDeck :: StdGen -> Deck -> Deck
shuffleDeck gen deck = [x | (x, _) <- sortBy (comparing snd) (zip deck (randoms gen :: [Int]))]

--------------------------------------------------------------------------------
-- Step 2 
--------------------------------------------------------------------------------
-- Selects smallest legal card, returns it
basicStrategy :: State GameState Deck
basicStrategy = do
  players <- gets players
  currentIx <- gets currentIx
  discardPile <- gets discardPile
  let player = players!!currentIx
  case hand player of
    [] -> case faceUp player of
            [] -> pure $ [head (faceDown player)]
            _ -> case filter (legalPlay (head' discardPile)) (faceUp player) of
                   [] -> pure []
                   legal -> pure [minimum legal]
    _ -> case filter (legalPlay (head' discardPile)) (hand player) of
           [] -> pure []
           legal -> pure [minimum legal]

-- used to get the head of the discardPile for legalPlay checks
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

applyStrategy :: State GameState ()
applyStrategy = do
  -- select the cards, deal with consequences of it
  currentIx <- gets currentIx
  firstPlayers <- gets players

  result <- case strategy $ firstPlayers!!currentIx of
    "basic" -> basicStrategy
    "basicSets" -> basicStrategySets
    -- backup
    _ -> basicStrategy

  if result == [] then
    giveWastePileTo $ firstPlayers!!currentIx
  else do
    removeCard result
    updatedPlayers <- gets players
    replenishCards (updatedPlayers!!currentIx)

  discardPile <- gets discardPile
  modify $ \x -> x {discardPile = result ++ discardPile}
  
  -- check after play effects
  -- https://stackoverflow.com/questions/59778472/guard-inside-do-block-haskell
  -- TODO might want to check all actions accounted for, need to add to burnedPiles
  -- nines need to be outside
  let action | discardPile /= [] && rank (head discardPile) == R10 = modify (\x -> x {discardPile = []})
             | checkTopFour discardPile = modify (\x -> x {discardPile = []})
             | discardPile /= [] && rank (head discardPile) == R8 = do
                                                                        order <- gets order
                                                                        modify $ \gs -> gs { order = not order}
             | checkTopThree discardPile = modify $ \gs -> gs {discardPile = []} 
             | discardPile /= [] && rank (head discardPile) == R9 = stealCard
             | otherwise = pure ()
  action
  

-- removes card played from hand
removeCard :: [Card] -> State GameState ()
removeCard card = do
  currentIx <- gets currentIx
  players <- gets players
  let player = players!!currentIx
  let updatedPlayer = player {hand = filter (`notElem` card) (hand player),
                              faceUp = filter (`notElem` card) (faceUp player),
                              faceDown = filter (`notElem` card) (faceDown player)}
  updatePlayer updatedPlayer

-- steals card from next player
stealCard :: State GameState ()
stealCard = do
  currentIx <- gets currentIx
  players <- gets players
  gs <- get
  case hand $ players!!(nextPlayer gs) of
    [] -> pure ()
    _ -> do gen <- gets rng
            let player = players!!currentIx
                updatedPlayer = player {hand = hand player ++ (shuffleDeck gen (hand $ players!!(nextPlayer gs))) }
            updatePlayer updatedPlayer

-- returns index of the next player
-- does not modify, as used for seeing the next player as well
nextPlayer :: GameState -> Int
nextPlayer gs = 
  let current = currentIx gs
      playersList = players gs
  in if current == (length playersList) - 1 
       then 0
       else current + 1
  
-- checks if top three cards are threes
checkTopThree :: Pile -> Bool
checkTopThree (c1:c2:c3:_) = rank c1 == R3 && rank c2 == R3 && rank c3 == R3
checkTopThree _             = False

-- checks if top four cards are the same
checkTopFour :: Pile -> Bool
checkTopFour discard
  | length discard >= 4 = rank (discard!!0) == rank (discard!!1) && rank (discard!!1) == rank (discard!!2) && rank (discard!!2) == rank (discard!!3)
  | otherwise = False

-- TODO 100% not sure that this is implemented correctly
gameLoop :: State GameState String
gameLoop = do
  applyStrategy
  currentIx <- gets currentIx
  playerList <- gets players
  ogFinishedOrder <- gets finishedOrder
  discard <- gets discardPile --TODO remove this line

  -- figures out if there is a winner yet or not
  if length (hand (playerList!!currentIx)) == 0 && 
     length (faceUp (playerList!!currentIx)) == 0 && 
     length (faceDown (playerList!!currentIx)) == 0 then do
      modify $ \x -> x { finishedOrder = ogFinishedOrder ++ [pId (playerList!!currentIx)]}
      modify $ \x -> x {players = filter (\p -> pId p /= (pId $ playerList!!currentIx)) playerList}
      players <- gets players
      modify (\x -> x {currentIx = if currentIx >= length players then 0 else currentIx})
      case players of
        [x] -> do
          finishedOrder <- gets finishedOrder
          -- traceM $ "last player: " ++ show (map pId players)
          -- traceM $ "finished order + last player: " ++ show(finishedOrder ++ (map pId players))
          let order = show(finishedOrder ++ (map pId players))
          -- traceM $ "order: " ++ order
          pure $ order
        _ -> do
          gameLoop
  else do
    -- draw <- gets drawPile
    -- traceM $ "CurrentIx: " ++ show currentIx
    -- traceM $ "Player hands: " ++ show (map (length . hand) playerList)
    -- traceM $ "Discard pile size: " ++ show (length discard)
    -- traceM $ "Discard pile top: " ++ show(head' discard)
    -- traceM $ "Draw pile size: " ++ show (length draw)
    gs <- get
    modify (\x -> x {currentIx = nextPlayer gs })
    gameLoop

playOneGame :: IO ()
playOneGame = do
  -- get player names
  putStrLn "Player 1 name: "
  name1 <- getLine
  
  putStrLn "Player 2 name: "
  name2 <- getLine
  
  putStrLn "Player 3 name: "
  name3 <- getLine

  -- create the deck
  gen <- newStdGen
  let deck = [Card r s | s <- [Clubs .. Spades], r <- [R2 .. RA]]
  let shuffledDeck = shuffleDeck gen deck

  -- create players
  let initialPlayers = [ Player 0 name1 [] [] [] "basic"
                       , Player 1 name2 [] [] [] "basic"
                       , Player 2 name3 [] [] [] "basic"
                       ]

          

  -- create gameState
  let initialState = GameState { players = initialPlayers
    , currentIx = 0
    , drawPile = shuffledDeck
    , discardPile = []
    , burnedPiles = []
    , rng = gen
    , finishedOrder = []
    , messages = []
    }

  let (result, finalState) = runState setupAndPlay initialState
  putStrLn $ "Game over! Winner order: " ++ result


setupAndPlay :: State GameState String
setupAndPlay = do
  players <- gets players
  dealToPlayer $ players!!0
  dealToPlayer $ players!!1
  dealToPlayer $ players!!2
  
  -- Choose starting player
  chooseStartingPlayer
  
  -- Play the game
  gameLoop

-- Works correctly
dealToPlayer :: Player -> State GameState Deck
dealToPlayer player = do
  drawPile <- gets drawPile
  
  let (drawnCards1, rest1) = splitAt 3 drawPile
  let (drawnCards2, rest2) = splitAt 3 rest1
  let (drawnCards3, rest3) = splitAt 3 rest2
  
  -- Update the player
  let updatedPlayer = player { hand = drawnCards1
                             , faceUp = drawnCards2
                             , faceDown = drawnCards3
                             }
  
  modify (\x -> x { players = map (\p -> if pId p == pId player 
                                           then updatedPlayer 
                                           else p) 
                                    (players x) })
  
  dealCards 9

chooseStartingPlayer :: State GameState ()
chooseStartingPlayer = do
  findStartPlayer R3

findStartPlayer :: Rank -> State GameState ()
findStartPlayer n = do
  -- gets players, filters hand to number of rank n, sorts based on that number
  -- if first card is of right rank, then it will give them first turn
  players <- gets players
  let playersOrdRank = [(y, x) | x <- players, let y = length . filter (== n) . map rank $ hand x, y > 0]
  case playersOrdRank of
    [] -> findStartPlayer $ succ n
    _ -> do
          if (rank . head . hand . snd . head) playersOrdRank == n then do
            modify $ \gs -> gs { currentIx = pId (snd (head playersOrdRank)) }
            pure ()
          else
            findStartPlayer $ succ n

  

--------------------------------------------------------------------------------
-- Step 3 
--------------------------------------------------------------------------------
basicStrategySets:: State GameState Deck
basicStrategySets = do
  players <- gets players
  currentIx <- gets currentIx
  discardPile <- gets discardPile
  let player = players!!currentIx
  case hand player of
    [] -> case faceUp player of
            [] -> pure $ [head (faceDown player)]
            _ -> case filter (legalPlay (head' discardPile)) (faceUp player) of
                   [] -> pure []
                   legal -> pure [minimum legal]
    _ -> case filter (legalPlay (head' discardPile)) (hand player) of
           [] -> pure []
           legal -> let minRank = rank (minimum legal)
                    in pure [x | x <- legal, rank x == minRank]

-- TODO 100% not sure that this is implemented correctly
gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  -- should print it at the end of the game
  applyStrategy
  currentIx <- gets currentIx
  playerList <- gets players
  ogFinishedOrder <- gets finishedOrder
  discard <- gets discardPile --TODO remove this line

  -- figures out if there is a winner yet or not
  if length (hand (playerList!!currentIx)) == 0 && 
     length (faceUp (playerList!!currentIx)) == 0 && 
     length (faceDown (playerList!!currentIx)) == 0 then do
      modify $ \x -> x { finishedOrder = ogFinishedOrder ++ [pId (playerList!!currentIx)]}
      modify $ \x -> x {players = filter (\p -> pId p /= (pId $ playerList!!currentIx)) playerList}
      messages <- gets messages
      modify $ \gs -> gs { messages = messages ++ "player out" ++ show(playerList!!currentIx) ++ "\n"}
      players <- gets players
      modify (\x -> x {currentIx = if currentIx >= length players then 0 else currentIx})
      case players of
        [x] -> do
          finishedOrder <- gets finishedOrder
          -- traceM $ "last player: " ++ show (map pId players)
          -- traceM $ "finished order + last player: " ++ show(finishedOrder ++ (map pId players))
          let order = show(finishedOrder ++ (map pId players))
          -- traceM $ "order: " ++ order
          pure $ order
        _ -> do
          outputStats
          gameLoopWithHistory
  else do
    -- draw <- gets drawPile
    -- traceM $ "CurrentIx: " ++ show currentIx
    -- traceM $ "Player hands: " ++ show (map (length . hand) playerList)
    -- traceM $ "Discard pile size: " ++ show (length discard)
    -- traceM $ "Discard pile top: " ++ show(head' discard)
    -- traceM $ "Draw pile size: " ++ show (length draw)
    modify (\x -> x {currentIx = if currentIx == (length playerList) - 1 then
                      0
                    else
                      currentIx + 1})
    outputStats
    gameLoopWithHistory
  

outputStats :: State GameState ()
outputStats = do
  -- start player
  drawPile <- gets drawPile
  players <- gets players
  currentIx <- gets currentIx
  let drawSize = (52 - (length players) * 9)
  case length drawPile of
    drawSize -> do 
      messages <- gets messages
      modify $ \gs -> gs { messages = messages ++ "Start player: " ++ show(players!!currentIx) ++ "\n"}
  messages' <- gets messages
  modify $ \gs -> gs { messages = messages' ++ "current player state: " ++ show(players!!currentIx) ++ "\n"}
  discard <- gets discardPile
  messages'' <- gets messages
  modify $ \gs -> gs { messages = messages'' ++ "current discard: " ++ show(discard)  ++ "\n"}
  messages''' <- gets messages
  case discard of 
    [] -> modify $ \gs -> gs { messages = messages''' ++ "discard burned" ++ "\n"}
    _ -> pure ()
  

runOneGameWithHistory :: IO ()
runOneGameWithHistory = do
  -- get player names
  putStrLn "Player 1 name: "
  name1 <- getLine
  
  putStrLn "Player 2 name: "
  name2 <- getLine
  
  putStrLn "Player 3 name: "
  name3 <- getLine

  -- create the deck
  gen <- newStdGen
  let deck = [Card r s | s <- [Clubs .. Spades], r <- [R2 .. RA]]
  let shuffledDeck = shuffleDeck gen deck

  -- create players
  let initialPlayers = [ Player 0 name1 [] [] [] "basic"
                       , Player 1 name2 [] [] [] "basic"
                       , Player 2 name3 [] [] [] "basicSets"
                       ]

          

  -- create gameState
  let initialState = GameState { players = initialPlayers
    , currentIx = 0
    , drawPile = shuffledDeck
    , discardPile = []
    , burnedPiles = []
    , rng = gen
    , finishedOrder = []
    , messages = []
    }

  let (result, finalState) = runState setupAndPlayWithHistory initialState
  putStrLn $ messages finalState
  putStrLn $ "Game over! Winner order: " ++ result

setupAndPlayWithHistory :: State GameState String
setupAndPlayWithHistory = do
  players <- gets players
  dealToPlayer $ players!!0
  dealToPlayer $ players!!1
  dealToPlayer $ players!!2
  
  -- Choose starting player
  chooseStartingPlayer
  
  -- Play the game
  gameLoopWithHistory

-- --------------------------------------------------------------------------------
-- -- Step 4 
-- --------------------------------------------------------------------------------
playOneGameStep4 :: [Extension] -> IO ()
playOneGameStep4 xs = do
  -- get player names
  putStrLn "Player 1 name: "
  name1 <- getLine
  putStrLn "Player 2 name: "
  name2 <- getLine
  putStrLn "Player 3 name: "
  name3 <- getLine
  -- create the deck
  gen <- newStdGen
  let deck = [Card r s | s <- [Clubs .. Spades], r <- [R2 .. RA]]
  let shuffledDeck = shuffleDeck gen deck
  -- create players
  let initialPlayers = [ Player 0 name1 [] [] [] "basic"
                       , Player 1 name2 [] [] [] "basic"
                       , Player 2 name3 [] [] [] "basicSets"
                       ]
  -- create gameState
  let baseState = GameState { players = initialPlayers
      , currentIx = 0
      , drawPile = shuffledDeck
      , discardPile = []
      , burnedPiles = []
      , rng = gen
      , finishedOrder = []
      , messages = []
      , order = True
      , nines = False
      , threes = False
      , eights = False
      }
      modifiedState = if elem ExtReverse8 xs
                      then baseState { eights = True }
                      else baseState
      modifiedState' = if elem ExtThree3s xs
                       then modifiedState { threes = True }
                       else modifiedState
      modifiedState'' = if elem ExtNineClubs xs
                        then modifiedState' { nines = True }
                        else modifiedState'
      (result, finalState) = runState setupAndPlayWithHistory modifiedState''
  putStrLn $ messages finalState
  putStrLn $ "Game over! Winner order: " ++ result
-- --------------------------------------------------------------------------------
-- -- Step 5 — Smart Player and Tournaments
-- --------------------------------------------------------------------------------
-- smartStrategy :: State GameState Deck
-- smartStrategy

-- playTournament :: Int -> IO [(String, Int)]
-- playTournament

