{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module SLogic.Smt.Int
  (
  module SLogic.Logic.Int

  , nia, lia
  , tInt, tNat

  , ivarM', nvarM', sivarM', snvarM'
  , ivarMO, nvarMO, sivarMO, snvarMO
  ) where


import Control.Monad.Reader
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M

import SLogic.Decode
import SLogic.Solver
import SLogic.Logic.Core
import SLogic.Logic.Int
import SLogic.Smt.SmtM


type Smt = SmtM IAtom

nia,lia :: String
nia = "QF_NIA"
lia = "QF_LIA"

tInt :: String
tInt = "Int"

tNat :: String
tNat = "Nat"

ivarM', nvarM', sivarM', snvarM' :: Smt IExpr
ivarM' = ivar `liftM` fresh

nvarM' = nvar `liftM` fresh

sivarM' = do
  n <- fresh
  let v = IVar n tInt
  assert $ v .>= neg one .&&  v .=< one
  return v

snvarM' = do
  l <- fresh
  let v = IVar l tNat
  assert $ v .=< one
  return v

ivarMO, nvarMO, sivarMO, snvarMO :: Ord a => a -> Memo a IExpr Smt IExpr
ivarMO  = memoized $ \_ -> lift ivarM'
nvarMO  = memoized $ \_ -> lift nvarM'
sivarMO = memoized $ \_ -> lift sivarM'
snvarMO = memoized $ \_ -> lift snvarM'


instance Decode (Reader (M.Map String Value)) IExpr Value where
  decode c = case c of
    IVal i   -> return (IntVal i) 
    IVar v _ -> get v
    _        -> return Other
    where get v = asks $ \m -> Other `fromMaybe` M.lookup v  m

instance Decode (Reader (M.Map String Value)) IAtom Value where
  decode c = case c of
    IExpr e -> decode e
    _       -> err
    where  err = error "SmtLib.Smt.Int.decode: not a literal"

instance Monad m => Decode m Value Int where
  decode c = case c of
    IntVal i -> return i
    _        -> error "SmtLib.Smt.Int.decode: not an int"


