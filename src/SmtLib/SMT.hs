{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# language FlexibleInstances #-}
module SmtLib.SMT where

import qualified SMTLib2 as SL
import SmtLib.PP

import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State.Lazy
import Control.Monad.Reader

import System.IO
{-import Control.Monad (liftM,liftM2,foldM,mapM,sequence)-}
{-import Control.Monad.Identity-}


type Variable = Int

data Literal = 
    LBool Bool
  | LInt Int
  | LVar Variable
  deriving (Eq, Ord, Show)

class Formula a where
  fm :: a -> SL.Expr

instance Formula SL.Expr where
  fm = id

instance Formula Literal where
  fm (LBool b) 
    | b         = fun "true" Nothing
    | otherwise = fun "false" Nothing
  fm (LInt i)  = SL.Lit (SL.LitNum $ toInteger i)
  fm (LVar i)  = fun funSymb (Just i)

data Constant = 
    CBool Bool 
  | CInt Int deriving (Eq, Ord, Show)

instance Read Constant where
  readsPrec _ r = readsBool1 ++ readsBool2  ++ readsInt where
    readsBool1 = [(CBool b, "") | (b,_)  <- reads r :: ([(Bool, String)])]
    readsBool2 = [(CBool True, "") | ("true", _) <- lex r] ++ [(CBool False, "") | ("false", _) <- lex r]
    readsInt   = [(CInt i, "") | (i,_)  <- reads r :: ([(Int, String)])]

name :: Literal -> SL.Name
name (LVar v) = SL.N (funSymb++show v)
name _        = error "SMT.name: unexpected case"

typeOf :: Type -> SL.Type
typeOf TBool = "Bool"
typeOf TNat  = "Nat"
typeOf TInt  = "Int"

funSymb :: String
funSymb = "f"

fun :: String -> Maybe Int -> SL.Expr
fun pre i = SL.App (SL.I nm []) Nothing []
  where nm = SL.N $ pre ++  maybe "" show i


data Type = TBool | TNat | TInt deriving (Eq, Ord, Show)

class Monad m => Decode m c a where
  decode :: c -> m a

newtype SMT m a = SMT { runSMT :: (StateT SMTState m) a }
  deriving (Functor, Monad, MonadIO, MonadState SMTState)

data SMTState = SMTState {
    logic    :: String
  , funs     :: S.Set (Literal, Type)
  , asserts  :: [SL.Expr]
  , next     :: Int
  , comments :: [String]
  } deriving (Eq, Ord, Show)

setLogic :: Monad m => String -> SMT m ()
setLogic s = do 
  st <- get
  put st { logic = s }

declare :: Monad m => Literal -> Type -> SMT m ()
declare nm ty = modify k
  where k st = st{ funs = S.insert (nm,ty) (funs st) }

assert :: Monad m => SL.Expr -> SMT m ()
assert e = modify k
  where k st = st { asserts = e:asserts st }

comment :: Monad m => String -> SMT m ()
comment c = modify k
  where k st = st { comments = c:comments st }

initial :: String -> SMTState
initial s = SMTState s S.empty [] 0 []

run :: Monad m => SMT m a -> SMTState -> m SL.Script
run smtM ist = do
  st <- execStateT (runSMT smtM) ist
  return $ script st

script :: SMTState -> SL.Script
script (SMTState l fs as _ _) = SL.Script $ 
  SL.CmdSetLogic (SL.N l)
  : S.fold (\(nm,ty) -> (SL.CmdDeclareFun (name nm) [] (typeOf ty) :) ) [] fs
  ++ reverse (map SL.CmdAssert as)
  ++ [SL.CmdCheckSat]

fresh :: Monad m => SMT m Literal
fresh = do
  st <- get
  let i = next st
  put $ st{ next=i+1 }
  return $ LVar i


-- inspired by satchmo library 

data Sat a = Sat a | Unsat | Unknown deriving (Eq,Show)

type Solver = String -> IO (Sat (M.Map String Constant))

solve :: 
  Solver
  -> SMT IO (Reader (M.Map String Constant) a)
  -> IO (Sat a)
solve solver build = do
  (problem, decoder) <- smt build
  result <- solver problem
  case result of
    Sat valuation -> do
      --hPutStrLn stderr "SMT.solve: satisfiable"
      return . Sat $ runReader decoder valuation
    Unsat -> do
      --hPutStrLn stderr "SMT.solve: unsatisfiable"
      return Unsat
    Unknown -> do
      --hPutStrLn stderr "SMT.solve: unknown"
      return Unknown

smt :: Monad m => SMT m a -> m (String, a)
smt m = do
  (a,s) <- runStateT (runSMT m) (initial "")
  let
    skript = render . SL.pp $ script s
    remark = unlines $ map (';':) (comments s)
  {-return $ (concat . lines . render . SL.pp $ script s, a)-}
  return (skript ++ remark, a)



instance Decode (Reader (M.Map String Constant)) Literal Constant where
  decode c = case c of
    (LBool b) -> return $ CBool b
    (LInt i)  -> return $ CInt i
    (LVar i)  -> asks $ \m -> err `fromMaybe` M.lookup (funSymb ++ show i) m
    where err = error "SmtLib.SMT.decode.asks: not found"

instance Monad m => Decode m () () where
    decode () = return ()
    
instance (Decode m c a, Decode m d b) => Decode m (c,d) (a,b) where
    decode (c,d) = do a <- decode c; b <- decode d; return (a,b)

instance (Decode m c a) => Decode m [c] [a] where
    decode = mapM decode

instance Decode m a b => Decode m (Maybe a) (Maybe b) where
  decode (Just b) = liftM Just (decode b)
  decode Nothing  = return Nothing

instance (Ord i, Decode m c a) => Decode m (M.Map i c) (M.Map i a) where
  decode x = do
    pairs <- sequence $ do 
      (i,e) <- M.assocs x
      return $ do
        f <- decode e
        return (i,f)
    return $ M.fromList pairs


-- memoization

newtype Memo a m r =  Memo { runMemo :: StateT (M.Map a Literal) m r}
  deriving (Functor, Monad, MonadTrans, MonadIO, MonadState (M.Map a Literal))

type MemoSMT a m r = Memo a (SMT m) r

memo :: Monad m => Memo a m r -> m (r, M.Map a Literal)
memo m = runStateT (runMemo m) M.empty

memoized :: (Monad m, Ord arg) => (arg -> Memo arg m Literal) -> arg -> Memo arg m Literal
memoized f a = do 
  ls <- get
  case M.lookup a ls of 
    Nothing -> do
      b <- f a
      modify (M.insert a b)
      return b
    Just b -> return b
