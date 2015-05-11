-- | This module provdides a default solver state.
module SLogic.SolverState
  (
  SolverState (..)
  , SolverSt
  , SolverStM
  , solveStM
  , initialState
  , setFormat
  , assert
  , assertM
  , fresh


  -- * bool & int functions
  , bvarM'

  , ivar, nvar
  , ivarM', nvarM', sivarM', snvarM'
  , ivarMO, nvarMO, sivarMO, snvarMO
  ) where


import Control.Monad.State.Strict

import SLogic.Logic
import SLogic.Result
import SLogic.Solver


-- | Specialised 'Solver' type.
type SolverSt m prob = Solver m (SolverState prob)

-- | Specialised 'SolverM' type.
type SolverStM prob = SolverM (SolverState prob)

-- | Like 'solveM', but 'initialState' already set.
solveStM :: MonadIO m => 
  SolverSt m prob
  -> SolverStM prob (Decoder res)
  -> m (Result res)
solveStM solver = solveM solver initialState

-- | A solver state parametric in the problem.
data SolverState prob = SolverState
  { format  :: String  -- ^ format specification; effect depends on the solver.
  , asserts :: [prob]  -- ^ assertions to check.
  , next    :: !Int    -- ^ counter.
  } deriving (Eq, Ord, Show)

-- | Default 'SolverState'.
initialState :: SolverState e
initialState = SolverState
  { format   = ""
  , asserts = []
  , next    = 0 }

-- | Sets the format.
setFormat :: String -> SolverStM e ()
setFormat s = do
  st <- get
  put st { format = s }

-- | Adds an assertions.
assert :: e -> SolverStM e ()
assert e = modify k
  where k st = st { asserts = e:asserts st }

-- | Monadic version of 'assert'.
assertM :: SolverStM e e -> SolverStM e ()
assertM e = e >>= assert

-- | Returns a fresh symbol @f:i@.
fresh :: SolverStM e String
fresh = do
  st <- get
  let i = next st
  put $ st{ next=i+1 }
  return ("fF" ++ show i)


-- * convenience functions

-- | Returns a 'fresh' Boolean variable.
bvarM' :: SolverStM (Formula e) (Formula e)
bvarM' = bvar `liftM` fresh

{-bvarMO:: Ord a => a -> MemoSolverM a (Formula e) (Formula e)-}
{-bvarMO = memoized $ \_ -> lift bvarM'-}


-- | Returns a 'fresh' numeric variable.
--
-- * i .. integer
-- * n .. natural
-- * s .. with assertion v in {-1,0,1}
ivarM', nvarM', sivarM', snvarM' :: SolverStM (Formula IFormula) IExpr
ivarM' = ivar `liftM` fresh

nvarM' = do
  n <- fresh
  let v = nvar n
  assert $ nvar .>= zero
  return v

sivarM' = do
  n <- fresh
  let v = ivar n
  assert $ v .== neg one .|| v .== zero .|| v .== one
  return v

snvarM' = do
  l <- fresh
  let v = nvar l
  assert $ v .== zero .|| v .== one
  return v

ivarMO, nvarMO, sivarMO, snvarMO :: Ord a => a -> MemoSolverM a (SolverState (Formula IFormula)) IExpr
ivarMO  = memoized $ \_ -> lift ivarM'
nvarMO  = memoized $ \_ -> lift nvarM'
sivarMO = memoized $ \_ -> lift sivarM'
snvarMO = memoized $ \_ -> lift snvarM'

