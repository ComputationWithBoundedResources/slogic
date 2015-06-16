{-# LANGUAGE TypeFamilies #-}
-- | This module provides a generic solver type and solver function.
module SLogic.Data.Solver
  (
  -- * Variable
  Var (..)
  , EnumVar (..)
  , Storing (..)

  -- * Generic Solver
  , Solver
  , Decoder
  , solve

  -- * Stateful Solver
  , SolverSt (..)
  , solveSt
  , runSolverSt

  -- * Memoization
  , Memo (..)
  , MemoSolverSt
  , memo
  , memoized
  ) where


import           Control.Applicative        hiding (empty)
import           Control.Arrow              (first)
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Foldable              as F
import qualified Data.IntMap.Strict         as IM
import qualified Data.Map.Strict            as M

import           SLogic.Data.Result


--- * variable -------------------------------------------------------------------------------------------------------

-- | A Var type can be serialised/de-serialised.
class Ord v => Var v where
  toVar   :: String -> v
  fromVar :: v -> String

instance Var Int where
  toVar ('f':'F':i) = read i :: Int
  toVar _           = error "SLogic.Smt.State.fromVar.Int: not an Int"
  fromVar i         = "fF" ++ show i

instance Var String where
  toVar s   = s
  fromVar s = s

newtype EnumVar v = EnumVar v deriving (Eq, Ord, Enum)

instance (Ord v, Enum v) => Var (EnumVar v) where
  toVar   = toEnum . toVar
  fromVar = fromVar . fromEnum


--- * store ----------------------------------------------------------------------------------------------------------

-- | The 'Storing' class specialises the decoding environment wrt. to a variable type.
class Storing v where
  data Store v :: *
  empty  :: Store v
  insert :: v -> Value -> Store v -> Store v
  find   :: v -> Store v -> Maybe Value
  fill   :: F.Foldable f => f (v, Value) -> Store v

instance Storing Int where
  newtype Store Int            = IntStore (IM.IntMap Value)
  empty                        = IntStore IM.empty
  insert var val (IntStore im) = IntStore $ IM.insert var val im
  find var (IntStore im)       = IM.lookup var im
  fill                         = IntStore . IM.fromList . F.toList

instance Storing String where
  newtype Store String           = StringStore (M.Map String Value)
  empty                          = StringStore M.empty
  insert var val (StringStore m) = StringStore $ M.insert var val m
  find var (StringStore m)       = M.lookup var m
  fill                           = StringStore . M.fromList . F.toList

instance (Ord v, Enum v) => Storing (EnumVar v) where
  newtype Store (EnumVar v)     = EnumStore (IM.IntMap Value)
  empty                         = EnumStore IM.empty
  insert var val (EnumStore im) = EnumStore $ IM.insert (fromEnum var) val im
  find var (EnumStore im)       = IM.lookup (fromEnum var) im
  fill                          = EnumStore . IM.fromList . map (first fromEnum) . F.toList


--- * solver ---------------------------------------------------------------------------------------------------------

-- | Generic solver type.
type Solver m v prob = prob -> m (Result (Store v))

-- | Generic decoder type.
type Decoder v res = Reader (Store v) res

-- | Generic solve function.
solve :: Functor f => Solver f v prob -> prob -> Decoder v res -> f (Result res)
solve solver problem decoder = fmap (runReader decoder) <$> solver problem


--- * state interface ------------------------------------------------------------------------------------------------

-- | Specialised statefule solver.
newtype SolverSt st res = SolverSt (State st res)
  deriving (Functor, Applicative, Monad, MonadState st)

runSolverSt :: SolverSt s a -> s -> (a, s)
runSolverSt (SolverSt st) = runState st

-- | Solve function for 'SolverSt'.
solveSt :: Functor f =>
  Solver f v prob
  -> prob -- ^ initial state/problem.
  -> SolverSt prob (Decoder v res)
  -> f (Result res)
solveSt solver initial build = solve solver problem decoder
  where (decoder, problem) = runSolverSt build initial


--- * memoization ----------------------------------------------------------------------------------------------------

-- | Memo Monad.
newtype Memo a e m r =  Memo { runMemo :: StateT (M.Map a e) m r}
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadState (M.Map a e))

-- | Memo 'SolverM' Monad.
type MemoSolverSt a e r = Memo a r (SolverSt e) r

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

