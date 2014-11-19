module SLogic.Smt.SmtM 
  (
  SmtM (..)
  , SmtState (..) 
  
  , setLogic
  , assert 
  , fresh

  , run
  , solve

  , Memo (..)
  , memo
  , memoized
  ) where 


import Control.Applicative (Applicative)
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Control.Monad.Reader

import SLogic.Solver
import SLogic.Logic.Core

newtype SmtM e r = SmtM { runSmtM :: State (SmtState e) r }
  deriving (Functor, Applicative, Monad, MonadState (SmtState e))

data SmtState e = SmtState
  { logic    :: String
  , asserts  :: [Expr e]
  , next     :: !Int
  } deriving (Eq, Ord, Show)

setLogic :: String -> SmtM e ()
setLogic s = do 
  st <- get
  put st { logic = s }

assert :: Expr e -> SmtM e ()
assert e = modify k
  where k st = st { asserts = e:asserts st }

fresh :: SmtM e String
fresh = do
  st <- get
  let i = next st
  put $ st{ next=i+1 }
  return ("f" ++ show i) 


initial :: String -> SmtState e
initial s = SmtState 
  { logic   = s
  , asserts = []
  , next    = 0 }
  
run :: SmtM e r -> SmtState e -> SmtState e
run smtM = execState (runSmtM smtM)

solve :: 
  Solver (SmtState e)
  -> SmtM e (Reader (M.Map Var Value) a)
  -> IO (Result a)
solve solver build = do
  let (decoder, problem) = runState (runSmtM build) (initial "")
  result <- solver problem
  case result of
    Sat valuation -> return . Sat $ runReader decoder valuation
    Unsat         -> return Unsat
    Unknown       -> return Unknown
    (Error s)     -> return (Error s)


-- memoization
newtype Memo a e m r =  Memo { runMemo :: StateT (M.Map a e) m r}
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadState (M.Map a e))

memo :: Monad m => Memo a e m r -> m (r, M.Map a e)
memo m = runStateT (runMemo m) M.empty

memoized :: (Monad m, Ord a) => (a -> Memo a e m e) -> a -> Memo a e m e
memoized f a = do 
  ls <- get
  case M.lookup a ls of 
    Nothing -> do
      b <- f a
      modify (M.insert a b)
      return b
    Just b -> return b


