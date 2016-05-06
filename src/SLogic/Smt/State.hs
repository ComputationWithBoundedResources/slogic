{-# LANGUAGE TypeFamilies #-}
-- | This module provdides a (specialised) solver for SMT.
-- Allows to generate fresh variables.
module SLogic.Smt.State
  (
    Logic (..)
  , SmtState (..)
  , SmtSolver
  , smtSolve
  , SmtSolverSt
  , smtSolveSt

  , initialState
  , setLogic
  , assert
  , assertM

  , Fresh (..)
  , fresh

  -- * bool & int functions
  , bvarM'
  , ivarM', nvarM', sivarM', snvarM'
  , ivarMO, nvarMO, sivarMO, snvarMO
  ) where


import Control.Monad.State.Strict
import Data.Word

import SLogic.Logic.Logic
import SLogic.Data.Result
import SLogic.Data.Solver
import SLogic.Logic.Formula


data Logic = QF_NIA | QF_LIA deriving (Eq, Ord, Show)

-- | Specialised 'Solver' type.
type SmtSolver m v = Solver m v (SmtState v)

-- | Specialised 'SolverM' type.
type SmtSolverSt v = SolverSt (SmtState v)

-- | Like solve.
smtSolve :: Functor f => SmtSolver f v -> Logic -> Formula v -> Decoder v res -> f (Result res)
smtSolve solver l f = solve solver $ initialState { logic = l, asserts = [f] }

-- | Like 'solveM', but 'initialState' already set.
smtSolveSt :: Functor f =>
  SmtSolver f v
  -> SmtSolverSt v (Decoder v res)
  -> f (Result res)
smtSolveSt solver = solveSt solver initialState

-- | A solver state parametric in the problem.
data SmtState v = SmtState
  { logic   :: Logic        -- ^ format specification; effect depends on the solver.
  , asserts :: [Formula v]  -- ^ assertions to check.
  , next    :: !Int         -- ^ counter.
  } deriving (Eq, Ord, Show)


-- | Default 'SmtState'.
initialState :: SmtState e
initialState = SmtState
  { logic   = QF_NIA
  , asserts = []
  , next    = 0 }

-- | Sets the format.
setLogic :: Logic -> SmtSolverSt e ()
setLogic s = modify $ \st -> st { logic = s }

-- | Adds an assertions.
assert :: Formula v -> SmtSolverSt v ()
assert e = modify k
  where k st = st { asserts = e:asserts st }

-- | Monadic version of 'assert'.
assertM :: SmtSolverSt v (Formula v) -> SmtSolverSt v ()
assertM e = e >>= assert


--- * fresh ----------------------------------------------------------------------------------------------------------

class Fresh v where
  freshVar :: Int -> v

instance Fresh Int where
  freshVar = id

instance Fresh Word8 where
  freshVar = fromIntegral

instance Fresh Word16 where
  freshVar = fromIntegral

instance Fresh String where
  freshVar = fromVar

instance Enum v => Fresh (EnumVar v) where
  freshVar = toEnum

-- | Returns a fresh symbol @f:i@.
fresh :: Fresh v => SmtSolverSt e v
fresh = do
  st <- get
  let i = next st
  put $ st{ next=i+1 }
  return (freshVar i)


-- * convenience functions

-- | Returns a 'fresh' Boolean variable.
bvarM' :: Fresh v => SmtSolverSt v (Formula v)
bvarM' = bvar `liftM` fresh

{-bvarMO:: Ord a => a -> MemoSolverM a (Formula e) (Formula e)-}
{-bvarMO = memoized $ \_ -> lift bvarM'-}


-- | Returns a 'fresh' numeric variable.
--
-- * i .. integer
-- * n .. natural
-- * s .. with assertion v in {-1,0,1}
ivarM', nvarM', sivarM', snvarM' :: Fresh v => SmtSolverSt v (IExpr v)
ivarM' = ivar `liftM` fresh

nvarM' = do
  n <- fresh
  let v = ivar n
  assert $ v .>= zero
  return v

sivarM' = do
  n <- fresh
  let v = ivar n
  assert $ v .== neg one .|| v .== zero .|| v .== one
  return v

snvarM' = do
  l <- fresh
  let v = ivar l
  assert $ v .== zero .|| v .== one
  return v

ivarMO, nvarMO, sivarMO, snvarMO :: (Ord a, Fresh v) => a -> MemoSolverSt a (SmtState v) (IExpr v)
ivarMO  = memoized $ \_ -> lift ivarM'
nvarMO  = memoized $ \_ -> lift nvarM'
sivarMO = memoized $ \_ -> lift sivarM'
snvarMO = memoized $ \_ -> lift snvarM'

