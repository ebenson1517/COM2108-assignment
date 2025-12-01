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
  cId <- gets currentIx
  discardPile <- gets discardPile
  let player = players!!cId
  -- if hand empty, check faceUp
  -- if faceUp empty, check faceDown
  case hand player of
    [] -> case faceUp player of
            -- winner
            [] -> pure  $ [head  $ faceDown player]
            _ -> pure $ [minimum [x | x <- faceUp player, legalPlay (Just $ head discardPile) x]]
    _ -> do
      let card = [x | x <- hand player, legalPlay (Just $ head discardPile) x]
      case card of 
        -- if hand has no legal cards, pickup deck
        [] -> pure []
        _ -> pure $ [minimum card]

applyStrategy :: State GameState ()
applyStrategy = do
  players <- gets players
  discardPile <- gets discardPile
  currentIx <- gets currentIx
  let player = players !! currentIx
      legalCards = [c | c <- hand player, legalPlay (listToMaybe discardPile) c]
  case legalCards of
    [] -> giveWastePileTo player  -- no legal play, pick up cards
    (card:_) -> do
      let updatedPlayer = player { hand = filter (/= card) (hand player) }
      updatePlayer updatedPlayer
      modify $ \gs -> gs { discardPile = card : discardPile}

      -- delete if 10
      if discardPile /= [] && (rank (head discardPile) == R10) then
        modify $ \gs -> gs { discardPile = [] }
      else pure ()

  -- check after play effects
  -- https://stackoverflow.com/questions/59778472/guard-inside-do-block-haskell
  -- TODO might want to check all actions accounted for, need to add to burnedPiles
  
  let action | discardPile /= [] && rank (head discardPile) == R10 = modify (\x -> x {discardPile = []})
             | checkTopFour discardPile = modify (\x -> x {discardPile = []})
             | otherwise = pure ()
  action

checkTopFour :: Pile -> Bool
checkTopFour discard
  | length discard >= 4 = rank (discard!!0) == rank (discard!!1) && rank (discard!!1) == rank (discard!!2) && rank (discard!!2) == rank (discard!!3)
  | otherwise = False

-- TODO 100% not sure that this is implemented correctly
gameLoop :: State GameState String
gameLoop = do
  applyStrategy
  currentIx <- gets currentIx
  players <- gets players
  finishedOrder <- gets finishedOrder
  discard <- gets discardPile --TODO remove this line
  modify (\x -> x {currentIx = if currentIx == (length players) - 1 then
                      0
                    else
                      currentIx + 1})
  -- calls game loop at the end unless there is a winner
  if length (hand (players!!currentIx)) == 0 && 
     length (faceUp (players!!currentIx)) == 0 && 
     length (faceDown (players!!currentIx)) == 0 then do
    modify $ \x -> x {finishedOrder = finishedOrder ++ [pId (players!!currentIx)]}
    pure "winner"
  else do
    -- traceM $ "CurrentIx: " ++ show currentIx
    -- traceM $ "Player hands: " ++ show (map (length . hand) players)
    -- traceM $ "Discard pile size: " ++ show (length discard)
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
  let initialPlayers = [ Player 0 name1 [] [] []
                       , Player 1 name2 [] [] []
                       , Player 2 name3 [] [] []
                       ]

          

  -- create gameState
  let initialState = GameState { players = initialPlayers
    , currentIx = 0
    , drawPile = shuffledDeck
    , discardPile = []
    , burnedPiles = []
    , rng = gen
    , finishedOrder = []
    }

  let finalState = execState setupAndPlay initialState
  putStrLn $ "Game over! Winner: " ++ show (finishedOrder finalState)


setupAndPlay :: State GameState String
setupAndPlay = do
  players <- gets players
  dealToPlayer $ players!!0
  dealToPlayer $ players!!1
  dealToPlayer $ players!!2
  
  -- Choose starting player
  startIdx <- chooseStartingPlayer
  modify $ \gs -> gs { currentIx = startIdx }
  
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

chooseStartingPlayer :: State GameState Int
chooseStartingPlayer = do
  findStartPlayer R3

findStartPlayer :: Rank -> State GameState Int
findStartPlayer n = do
  -- gets players, filters hand to number of rank n, sorts based on that number
  -- if first card is of right rank, then it will give them first turn
  players <- gets players
  let playersOrdRank = [(y, x) | x <- players, let y = length . filter (== n) . map rank $ hand x]
  if (rank . head . hand . snd . head) playersOrdRank == n then
    pure $ pId (snd (head playersOrdRank))
  else
    findStartPlayer $ succ n
  

--------------------------------------------------------------------------------
-- Step 3 
--------------------------------------------------------------------------------
basicStrategySets:: State GameState Deck
basicStrategySets = do
-- easiest thing to do is just to sort the hand according to rank each time
  players <- gets players
  currentIx <- gets currentIx
  let player = players!!currentIx
  discardPile <- gets discardPile
  case hand player of
    [] -> do
      drawPile <- gets drawPile
      if drawPile == [] then
        case faceUp player of
          [] -> pure [head (shuffleDeck (mkStdGen 1234) (faceDown player))]
          xs -> pure [minimum [x | x <- (hand player), legalPlay (Just $ head discardPile) x]]
      else do
        -- they need to pickup then
        replenishCards player
        pure []
    xs -> let xs = [x | x <- (hand player), legalPlay (Just (head discardPile)) x] in
          pure (filter (== minimum xs) xs)

gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  --ouputStats
  applyStrategy
  currentIx <- gets currentIx
  players <- gets players
  modify (\x -> x {currentIx = if currentIx == (length players) then
                      0
                    else
                      currentIx + 1})
  -- calls game loop at the end unless there is a winner
  if length (faceDown (players!!currentIx)) /= 0 then
    gameLoop 
  else
    pure ""

-- outputStats :: State GameState IO 
-- outputStats = do
--   putStrLn "Start Player" ++ "h"


-- runOneGameWithHistory :: IO ()
-- runOneGameWithHistory

-- --------------------------------------------------------------------------------
-- -- Step 4 
-- --------------------------------------------------------------------------------
-- playOneGameStep4 :: [Extension] -> IO ()
-- playOneGameStep4 xs
-- --------------------------------------------------------------------------------
-- -- Step 5 — Smart Player and Tournaments
-- --------------------------------------------------------------------------------
-- smartStrategy :: State GameState Deck
-- smartStrategy

-- playTournament :: Int -> IO [(String, Int)]
-- playTournament

