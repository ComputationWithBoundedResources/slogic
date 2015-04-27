-- | This module provides the solver type and the solve function.
module SLogic.Solver
  (
  -- * Generic Solver
  Solver
  , Decoder
  , solve

  -- * Monadic Solver
  , SolverM (..)
  , solveM
  , runSolverM

  -- * Memoization
  , Memo (..)
  , MemoSolverM
  , memo
  , memoized
  ) where


import           Control.Applicative        (Applicative)
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict            as M

import           SLogic.Logic.Core
import           SLogic.Result


-- | Generic solver type.
type Solver m prob = prob -> m (Result (M.Map Var Value))

-- | Generic decoder type.
type Decoder res = Reader (M.Map Var Value) res


-- | Generic solve function.
solve :: MonadIO m => Solver m prob -> prob -> Decoder res -> m (Result res)
solve solver problem decoder = do
  result <- solver problem
  case result of
    Sat valuation -> return . Sat $ runReader decoder valuation
    Unsat         -> return Unsat
    Unknown       -> return Unknown
    (Error s)     -> return (Error s)


-- * monadic interface

-- | Generic Solver (State) monad.
newtype SolverM st res = SolverM (State st res)
  deriving (Functor, Applicative, Monad, MonadState st)

runSolverM :: SolverM s a -> s -> (a, s)
runSolverM (SolverM st) = runState st

-- | Solve function for 'SolverM'.
solveM :: MonadIO m => 
  Solver m prob
  -> prob -- ^ initial state/problem.
  -> SolverM prob (Decoder res)
  -> m (Result res)
solveM solver initial build = do
  let (decoder, problem) = runSolverM build initial
  solve solver problem decoder


-- * memoization

-- | Memo Monad.
newtype Memo a e m r =  Memo { runMemo :: StateT (M.Map a e) m r}
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadState (M.Map a e))

-- | Memo 'SolverM' Monad.
type MemoSolverM a e r = Memo a r (SolverM e) r

-- | Evaluates 'Memo' monad.
memo :: Monad m => Memo a e m r -> m (r, M.Map a e)
memo m = runStateT (runMemo m) M.empty

-- | Memoization function.
memoized :: (Monad m, Ord a) => (a -> Memo a e m e) -> a -> Memo a e m e
memoized f a = do
  ls <- get
  case M.lookup a ls of
    Nothing -> do
      b <- f a
      modify (M.insert a b)
      return b
    Just b -> return b

