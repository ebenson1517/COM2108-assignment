module KarmaBrief where

import System.Random 
import Control.Monad.State
import Data.List 
import Data.Ord 


-- Cards
data Suit = Clubs | Diamonds | Hearts | Spades
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Rank = R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | RJ | RQ | RK | RA
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

data Card = Card { rank :: Rank, suit :: Suit }
  deriving (Eq, Show, Read)

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
  }

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
  | cardRank == 2 || cardRank == 8 || cardRank == 10 = True
  | cardRank >= pileRank = True
  | pileRank == 7 && cardRank <= pileRank = True
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
  let player = players!!currentIx
  case hand player of
    [] -> do
      drawPile <- gets drawPile
      if drawPile == [] then
        case faceUp player of
          [] -> pure (head (shuffleDeck (mkStdGen 1234) (faceDown $ hand player)))
          xs -> pure (minimum [x | x <- hand player, legalPlay x])
      else
        -- they need to pickup then
        replenishCards player
        pure basicStrategy
    _ -> pure (minimum [x | x <- (hand player), legalPlay x])

applyStrategy :: State GameState ()
applyStrategy = do
  playersList <- gets players
  currentIx <- gets currentIx
  let player = playersList !! currentIx
      legalCards = [c | c <- hand player, legalPlay (listToMaybe discardPile) c]
  case legalCards of
    [] -> replenishCards player  -- no legal play, pick up cards
    (card:_) -> do
      let updatedPlayer = player { hand = filter (/= card) (hand player) }
      updatePlayer updatedPlayer
      modify $ \gs -> gs { discardPile = card : discardPile gs }

      -- delete if 10
      discard <- gets discardPile
      when (rank (head discard) == R10) $
        modify $ \gs -> gs { discardPile = [] }

  -- advance turn
  nPlayers <- gets (length . players)
  modify $ \gs -> gs { currentIx = (currentIx + 1) `mod` nPlayers }

  -- check after play effects
  -- https://stackoverflow.com/questions/59778472/guard-inside-do-block-haskell
  discard <- gets discardPile
  -- TODO might want to check all actions accounted for, need to add to burnedPiles
  let action | rank  $ head discard == R10 = modify (\x -> x {discard = []})
             | checkTopFour discard = modify (\x -> x {discard = []})
             | otherwise = ()
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
  modify (\x -> x {currentIx = if currentIx == (length players) then
                      0
                    else
                      currentIx + 1})
  -- calls game loop at the end unless there is a winner
  if length (faceDown (players!!currentIx)) /= 0 then
    gameLoop 
  else
    pure "Winner found"

playOneGame :: IO ()
playOneGame = do
  let deck = [Card rank suit| suit <- [Clubs..Spades], rank <- [R2..RA]]
  -- pretty sure this is 3 players
  -- deck will always be 52 cards
  let players = [Player id ("player"++id) [] [] [] | id <- [1..3]]
  putStrLn "Player name: "
  line <- getLine
  pName <- pName players!!0
  modify (\x -> x {pName = line})
  dealToPlayer players!!0

  putStrLn "Player name: "
  line <- getLine
  pName <- pName players!!1
  modify (\x -> x {pName = line})
  dealToPlayer players!!1

  putStrLn "Player name: "
  line <- getLine
  pName <- pName players!!2
  modify (\x -> x {pName = line})
  dealToPlayer players !! 2
  dealCards 9

  let gameState = GameState  players 0 deck [] (StdGen 1234) []
  modify (\x -> x {currentIx = chooseStartingPlayer})
  evalState gameLoop gameState



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
                                    (players gs) })
  
  dealCards 9

chooseStartingPlayer :: State GameState ()
chooseStartingPlayer = do
  findStartPlayer R3

findStartPlayer :: Rank -> State GameState Int
findStartPlayer n = do
  players <- gets players
  let players = [(y, x) | x <- players, y <- ((length . filter (== n) . map rank) (hand x))]
  if head (hand (head players)) == n then
    pure $ pId player - 1
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
  player <- players!!currentIx
  case hand player of
    [] -> do
      drawPile <- gets drawPile
      if drawPile == [] then
        case faceUp player of
          [] -> pure (head (shuffleDeck (mkStdGen 1234) (faceDown player)))
          xs -> pure (minimum [x | x <- (hand player), legalPlay x])
      else
        -- they need to pickup then
        replenishCards player
        pure (basicStrategy gameState)
    xs -> let xs = [x | x <- (hand player), legalPlay x] in
          pure (filter (== minimum xs) xs)

gameLoopWithHistory :: State GameState String
gameLoopWithHistory = do
  ouputStats
  applyStrategy
  currentIx <- gets currentIx
  players <- gets players
  modify (\x -> x {currentIx = if currentIx == (length players) then
                      0
                    else
                      currentIx + 1})
  -- calls game loop at the end unless there is a winner
  if length (faceDown (players!!currentIx)) != 0 then
    gameLoop 
  else
    pure

-- outputStats :: State GameState IO 
-- outputStats = do
--   putStrLn "Start Player" ++ "h"


runOneGameWithHistory :: IO ()
runOneGameWithHistory

--------------------------------------------------------------------------------
-- Step 4 
--------------------------------------------------------------------------------
playOneGameStep4 :: [Extension] -> IO ()
playOneGameStep4 xs
--------------------------------------------------------------------------------
-- Step 5 — Smart Player and Tournaments
--------------------------------------------------------------------------------
smartStrategy :: State GameState Deck
smartStrategy

playTournament :: Int -> IO [(String, Int)]
playTournament

