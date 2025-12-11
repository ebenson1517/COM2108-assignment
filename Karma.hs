module KarmaBrief where

import System.Random
import Control.Monad.State
import Data.List
import Data.Ord
import Data.Maybe ( listToMaybe, fromMaybe )
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
  , finishedOrder :: [Player]
  , messages      :: String
  , order         :: Bool
  , nines         :: Bool  -- rule extensions
  , threes        :: Bool
  , eights        :: Bool
  , forcedPickup  :: Bool
  , iterations    :: Int
  } deriving (Show)


-- Different extension rules we can toggle
data Extension = ExtReverse8 | ExtThree3s | ExtNineClubs
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Step 1 
--------------------------------------------------------------------------------
-- Determines if legal play. Legal if discard pile empty, or higher than top of
-- discard. If 7, go below instead. If 2, always legal. If 8, ignore 8. If 10,
-- remove discard.
legalPlay :: Maybe Card -> Card -> Bool
legalPlay Nothing _ = True
legalPlay (Just (Card pileRank _)) (Card cardRank _)
  | pileRank == R7 = cardRank <= pileRank
  | cardRank == R2 || cardRank == R8 || cardRank == R10 = True
  | cardRank >= pileRank = True
  | otherwise = False

-- Returns a list of the legal cards to play on top of a card
validPlays :: Maybe Card -> Deck -> Deck
validPlays pile = filter (legalPlay pile)

-- removes the top n cards from the drawPile
dealCards :: Int -> State GameState Deck
dealCards 0 = pure []
dealCards n = do
  drawPile <- gets drawPile
  case drawPile of
    [] -> pure []
    (card:rest) -> do
      modify (\x -> x {drawPile = rest })
      rest <- dealCards (n-1)
      pure (card:rest)

-- gives the wastePile to the player, sets the discardPile to empty
giveWastePileTo :: Player -> State GameState ()
giveWastePileTo player = do
  discard <- gets discardPile
  let updatedPlayer = player { hand = hand player ++ discard }
  updatePlayer updatedPlayer
  modify $ \gs -> gs { discardPile = [] }

-- searches through the player list for the player with the same pId as the one passed in
-- and replaces it
updatePlayer :: Player -> State GameState ()
updatePlayer updatedPlayer = modify $ \gs ->
  gs { players = map (\p -> if pId p == pId updatedPlayer then updatedPlayer else p) (players gs) }

-- adds cards to a players hand until they have three cards again
replenishCards :: Player -> State GameState ()
replenishCards player = do
  draw <- gets drawPile
  let handCards = hand player
      -- compares to 0, so if the length of handCards is greater than 3, won't draw any
      nToDraw = max 0 (3 - length handCards)
      (drawn, rest) = splitAt nToDraw draw
      updatedPlayer = player { hand = handCards ++ drawn }
  updatePlayer updatedPlayer
  modify $ \gs -> gs { drawPile = rest }

-- shuffles a deck passed in
shuffleDeck :: StdGen -> Deck -> Deck
shuffleDeck gen deck = [x | (x, _) <- sortBy (comparing snd) (zip deck (randoms gen :: [Int]))]

--------------------------------------------------------------------------------
-- Step 2 
--------------------------------------------------------------------------------
-- Selects smallest legal card, returns it
-- checks hand first, then faceUp, then faceDown
basicStrategy :: State GameState Deck
basicStrategy = do
  players <- gets players
  currentIx <- gets currentIx
  discardPile <- gets discardPile
  let player = players!!currentIx
  case hand player of
    [] -> case faceUp player of
            [] -> pure [head (faceDown player)]
            _ -> case validPlays (head' discardPile) (faceUp player) of
                   [] -> pure []
                   legal -> pure [minimum legal]
    _ -> case validPlays (head' discardPile) (hand player) of
           [] -> pure []
           legal -> pure [minimum legal]

-- gets head of discardPile, but checks that it isn't empty
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

-- executes a player's turn
-- applies their strategy
-- applies any rules that come from the card they played
applyStrategy :: State GameState ()
applyStrategy = do
  -- select the cards, deal with consequences of it
  currentIx <- gets currentIx
  players' <- gets players
  threes <- gets threes
  forcedPickup <- gets forcedPickup
  discard <- gets discardPile

  -- check forcedPickup
  when (threes && forcedPickup) $ let updatedPlayer = (players'!!currentIx) {hand = hand (players'!!currentIx) ++ discard}
                                  in do updatePlayer updatedPlayer
                                        modify $ \gs -> gs {discardPile = [], forcedPickup = False}

  result <- case strategy $ players'!!currentIx of
    "basic" -> basicStrategy
    "basicSets" -> basicStrategySets
    "smart" -> smartStrategy

    -- backup
    _ -> basicStrategy

  if null result then
    giveWastePileTo $ players'!!currentIx
  else do
    removeCard result
    updatedPlayers <- gets players
    replenishCards (updatedPlayers!!currentIx)

  discard <- gets discardPile
  modify $ \x -> x {discardPile = result ++ discard}
  discard' <- gets discardPile
  -- check after play effects
  -- https://stackoverflow.com/questions/59778472/guard-inside-do-block-haskell
  -- TODO might want to check all actions accounted for, need to add to burnedPiles
  -- nines need to be outside
  nines <- gets nines
  eights <- gets eights
  burnedPiles <- gets burnedPiles
  --when (nines && discard' /= [] && rank (head discard') == R9) stealCard
  let action | discard' /= [] && rank (head discard') == R10 = do modify (\x -> x {discardPile = [], burnedPiles = burnedPiles ++ [discard']})
             | checkTopFour discard' = modify (\x -> x {discardPile = [], burnedPiles = burnedPiles ++ [discard'] })
             | eights && discard' /= [] && rank (head discard') == R8 = do
                                                                        order <- gets order
                                                                        modify $ \gs -> gs { order = not order}
              -- checks top four first so must only be top three threes
             | checkTopThree discard' = modify $ \gs -> gs {forcedPickup = True}
             | otherwise = pure ()
  action

-- found bug where actions were not using current discardPile.
-- applyStrategy doesn't update playerIx, gameLoop does
-- removes card played from a player
removeCard :: [Card] -> State GameState ()
removeCard card = do
  currentIx <- gets currentIx
  players <- gets players
  let player = players!!currentIx
  let updatedPlayer = player {hand = filter (`notElem` card) (hand player),
                              faceUp = filter (`notElem` card) (faceUp player),
                              faceDown = filter (`notElem` card) (faceDown player)}
  updatePlayer updatedPlayer

-- steals card from next player, if their hand isn't empty
stealCard :: State GameState ()
stealCard = do
  currentIx <- gets currentIx
  players <- gets players
  gs <- get
  case hand $ players!!nextPlayer gs of
    [] -> pure ()
    _ -> do gen <- gets rng
            let player = players!!currentIx
                victim = players!!nextPlayer gs
                result = shuffleDeck gen (hand victim)
                updatedPlayer = player {hand = hand player ++ result}
                updatedPlayer' = player {hand = filter (`notElem` result) (hand victim)}
            updatePlayer updatedPlayer
            updatePlayer victim

-- returns index of the next player in turn
nextPlayer :: GameState -> Int
nextPlayer gs =
  let current = currentIx gs
      playersList = players gs
      len = length playersList
  in if order gs
     then
      if current == len - 1 then 0 else current + 1
     else
      if current == 0 then len - 1 else current - 1

-- checks if top three cards are threes
checkTopThree :: Pile -> Bool
checkTopThree (c1:c2:c3:_) = rank c1 == R3 && rank c2 == R3 && rank c3 == R3
checkTopThree _             = False

-- checks if top four cards are the same
checkTopFour :: Pile -> Bool
checkTopFour discard
  | length discard >= 4 = rank (head discard) == rank (discard!!1) && rank (discard!!1) == rank (discard!!2) && rank (discard!!2) == rank (discard!!3)
  | otherwise = False

-- game Loop, executes a full turn
-- applies strategy, decides if the player has one yet
-- checks if end of game
-- otherwise calls again
gameLoop :: State GameState String
gameLoop = do
  applyStrategy
  currentIx <- gets currentIx
  playerList <- gets players
  ogFinishedOrder <- gets finishedOrder


  iterations <- gets iterations
  modify $ \gs -> gs {iterations = iterations + 1}

  -- figures out if there is a winner yet or not
  if null (hand (playerList!!currentIx)) &&
     null (faceUp (playerList!!currentIx)) &&
     null (faceDown (playerList!!currentIx)) then do
      modify $ \x -> x { finishedOrder = ogFinishedOrder ++ [playerList!!currentIx]}
      modify $ \x -> x {players = filter (\p -> pId p /= pId (playerList!!currentIx)) playerList}
      players <- gets players
      modify (\x -> x {currentIx = if currentIx >= length players then 0 else currentIx})
      case players of
        [x] -> do
          finishedOrder <- gets finishedOrder
          let order = show (finishedOrder ++ players)
          pure order
        _ -> do
          gameLoop
  else if iterations >= 150 then
    pure $ show ogFinishedOrder
  else do
    modify (\gs -> gs {currentIx = nextPlayer gs })
    gameLoop

-- sets up a game with three players and plays one, outputs the result
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
    , order = True
    , nines = False
    , threes = False
    , eights = False
    , forcedPickup = False
    , iterations = 0
    }

  let (result, finalState) = runState setupAndPlay initialState
  putStrLn $ "Game over! Winner order: " ++ result

-- deals to players, chooses the starting player, starts the gameLoop
setupAndPlay :: State GameState String
setupAndPlay = do
  players <- gets players
  mapM_ dealToPlayer players

  -- Choose starting player
  chooseStartingPlayer

  -- Play the game
  gameLoop

-- deals cards to players, at the start of the game
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

  updatePlayer updatedPlayer

  dealCards 9

-- chooses the starting player, based on who has the most of the lowest cards
chooseStartingPlayer :: State GameState ()
chooseStartingPlayer = do
  findStartPlayer R3

-- recursively checks cards, sorts the players by who has the most of a rank,
-- if none have the rank, moves to the next rank. Otherwise will return the player
-- with the most
findStartPlayer :: Rank -> State GameState ()
findStartPlayer n
  -- catch all, should never be possible to happen
  | n == RA = modify $ \gs -> gs { currentIx = 0 }
  -- gets players, filters hand to number of rank n, sorts based on that number
  -- if first card is of right rank, then it will give them first turn
  | otherwise = do
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
-- gets the smallest legal card, but returns all cards of that rank
-- checks hand first, then faceUp, then faceDown
basicStrategySets:: State GameState Deck
basicStrategySets = do
  players <- gets players
  currentIx <- gets currentIx
  discardPile <- gets discardPile
  let player = players!!currentIx
  case hand player of
    [] -> case faceUp player of
            [] -> pure [head (faceDown player)]
            _ -> case filter (legalPlay (head' discardPile)) (faceUp player) of
                   [] -> pure []
                   legal -> pure [minimum legal]
    _ -> case filter (legalPlay (head' discardPile)) (hand player) of
           [] -> pure []
           legal -> let minRank = rank (minimum legal)
                    in pure [x | x <- legal, rank x == minRank]

-- game Loop, executes a full turn
-- applies strategy, decides if the player has one yet
-- checks if end of game
-- otherwise calls again
-- updates the gameState with messges to be output at end of the game
gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  -- should print it at the end of the game
  applyStrategy
  currentIx <- gets currentIx
  playerList <- gets players
  ogFinishedOrder <- gets finishedOrder


  iterations <- gets iterations
  modify $ \gs -> gs {iterations = iterations + 1}

  -- figures out if there is a winner yet or not
  if null (hand (playerList!!currentIx)) &&
     null (faceUp (playerList!!currentIx)) &&
     null (faceDown (playerList!!currentIx)) then do
      modify $ \x -> x { finishedOrder = ogFinishedOrder ++ [playerList!!currentIx]}
      modify $ \x -> x {players = filter (\p -> pId p /= pId (playerList!!currentIx)) playerList}
      messages <- gets messages
      modify $ \gs -> gs { messages = messages ++ "player out" ++ show (playerList!!currentIx) ++ "\n"}
      players <- gets players
      modify (\x -> x {currentIx = if currentIx >= length players then 0 else currentIx})
      case players of
        [x] -> do
          finishedOrder <- gets finishedOrder
          let order = show (finishedOrder ++ players)
          pure order
        _ -> do
          outputStats
          gameLoopWithHistory
  else if iterations >= 150 then
    pure $ show ogFinishedOrder
  else do
    modify (\gs -> gs {currentIx = nextPlayer gs })
    outputStats
    gameLoopWithHistory

-- during gameLoop, this records stats, and adds it to messages in the gameState
outputStats :: State GameState ()
outputStats = do
  -- start player
  drawPile <- gets drawPile
  players <- gets players
  currentIx <- gets currentIx
  let drawSize = 52 - length players * 9
  case length drawPile of
    drawSize -> do
      messages <- gets messages
      modify $ \gs -> gs { messages = messages ++ "Start player: " ++ show (players!!currentIx) ++ "\n"}
  messages' <- gets messages
  modify $ \gs -> gs { messages = messages' ++ "current player state: " ++ show (players!!currentIx) ++ "\n"}
  discard <- gets discardPile
  messages'' <- gets messages
  modify $ \gs -> gs { messages = messages'' ++ "current discard: " ++ show discard  ++ "\n"}
  messages''' <- gets messages
  case discard of
    [] -> modify $ \gs -> gs { messages = messages''' ++ "discard burned" ++ "\n"}
    _ -> pure ()

-- setup and runs a game, using gameLoopWithHistory.
-- outputs the messages in gameState at the end
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
    , order = True
    , nines = False
    , threes = False
    , eights = False
    , forcedPickup = False
    , iterations = 0
    }

  let (result, finalState) = runState setupAndPlayWithHistory initialState
  putStrLn $ messages finalState
  putStrLn $ "Game over! Winner order: " ++ result

-- deals to players, starts the game
setupAndPlayWithHistory :: State GameState String
setupAndPlayWithHistory = do
  players <- gets players
  mapM_ dealToPlayer players

  -- Choose starting player
  chooseStartingPlayer

  -- Play the game
  gameLoopWithHistory

-- --------------------------------------------------------------------------------
-- -- Step 4 
-- --------------------------------------------------------------------------------
-- plays a game, takes in list of extensions to use
-- sets the fields in gameState to the true if extensions are active
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
      , forcedPickup = False
      , iterations = 0
      }
      modifiedState = if ExtReverse8 `elem` xs
                      then baseState { eights = True }
                      else baseState
      modifiedState' = if ExtThree3s `elem` xs
                       then modifiedState { threes = True }
                       else modifiedState
      modifiedState'' = if ExtNineClubs `elem` xs
                        then modifiedState' { nines = True }
                        else modifiedState'
      (result, finalState) = runState setupAndPlayWithHistory modifiedState''
  putStrLn $ messages finalState
  putStrLn $ "Game over! Winner order: " ++ result
-- --------------------------------------------------------------------------------
-- -- Step 5 — Smart Player and Tournaments
-- --------------------------------------------------------------------------------
smartStrategy :: State GameState Deck
smartStrategy = do
  players <- gets players
  currentIx <- gets currentIx
  discardPile <- gets discardPile
  drawPile <- gets drawPile
  let player = players!!currentIx
      nextPlayerIx = (currentIx + 1) `mod` length players
      nextPlayer = players!!nextPlayerIx
      nextPlayerCardCount = length (hand nextPlayer) + length (faceUp nextPlayer) + length (faceDown nextPlayer)
      isNextPlayerLow = nextPlayerCardCount <= 3
  case hand player of
    [] -> case faceUp player of
            [] -> pure [head (faceDown player)]
            _ -> case filter (legalPlay (head' discardPile)) (faceUp player) of
                  [] -> pure []
                  legal -> pure [minimumByCardRank legal]
    _ -> case filter (legalPlay (head' discardPile)) (hand player) of
          [] -> pure []
          legal -> let -- If next player is low, play highest rank card, otherwise lowest
                   targetCard = if isNextPlayerLow
                                then maximumByCardRank legal
                                else minimumByCardRank legal
                   targetRank = rank targetCard
                   targetRankCards = [x | x <- legal, rank x == targetRank]
                   isPowerCard c = cardRank (rank c) >= 10
                   -- If draw pile is empty, play all matching cards, so catch up
                   -- If card selected is powercard and don't need to catch up, play one at a time
               in if null drawPile
                  then pure targetRankCards
                  else if isPowerCard targetCard
                       then pure [targetCard]
                       else pure targetRankCards

-- returns the maximum card by my special cardRank
maximumByCardRank :: [Card] -> Card
maximumByCardRank = maximumBy (comparing (cardRank . rank))

-- returns the minimum card by my special cardRank
minimumByCardRank :: [Card] -> Card
minimumByCardRank = minimumBy (comparing (cardRank . rank))

cardRank :: Rank -> Int
cardRank RA = 13
cardRank R8 = 12
cardRank R10 = 11
cardRank R2 = 10
cardRank RK = 9
cardRank RQ = 8
cardRank RJ = 7
cardRank R9 = 6
cardRank R7 = 5
cardRank R6 = 4
cardRank R5 = 3
cardRank R4 = 2
cardRank R3 = 1

-- runs n games, tallies results up, outputs them
playTournament :: Int -> IO [(String, Int)]
playTournament nGames = do
  results <- runTournament nGames
  let unique = nub results
      talliedResults = [(x, tally results x) | x <- unique]
  pure talliedResults

-- runs the tournament, by recursively playing the games,
-- and returning the result
runTournament :: Int -> IO [String]
runTournament 0 = pure []
runTournament nGames = do
  result <- playOneGameTourney [ExtReverse8, ExtThree3s, ExtNineClubs]
  rest <- runTournament (nGames - 1)
  pure (result ++ rest)

-- tallies the number of times something appears in a list
tally :: [String] -> String -> Int
tally xs x = length [y | y <- xs, y == x]

-- plays a single game in the tournament
playOneGameTourney :: [Extension] -> IO [String]
playOneGameTourney xs = do
  -- create the deck
  gen <- newStdGen
  let deck = [Card r s | s <- [Clubs .. Spades], r <- [R2 .. RA]]
  let shuffledDeck = shuffleDeck gen deck
  -- create players
  let initialPlayers = [ Player 0 "p1" [] [] [] "smart"
                       , Player 1 "p2" [] [] [] "basicSets"
                       , Player 2 "p3" [] [] [] "basic"
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
      , forcedPickup = False
      , iterations = 0
      }
      modifiedState = if ExtReverse8 `elem` xs
                      then baseState { eights = True }
                      else baseState
      modifiedState' = if ExtThree3s `elem` xs
                       then modifiedState { threes = True }
                       else modifiedState
      modifiedState'' = if ExtNineClubs `elem` xs
                        then modifiedState' { nines = True }
                        else modifiedState'
      (result, finalState) = runState setupAndPlay modifiedState''

      finished = finishedOrder finalState
  case finished of
    [] -> pure []
    x -> pure [strategy $ head x]


