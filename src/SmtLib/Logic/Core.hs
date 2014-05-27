{-# LANGUAGE OverloadedStrings #-}
module SmtLib.Logic.Core 
  ( module SMTLib2.Core
  , module SMTLib2
  , top, bot
  , bvar
  , bvarm
  , (.&&), (.||)
  , bigAnd
  , bigOr
  , (.==>)
  , (.==),(./=)
  )
where

import SmtLib.SMT
import SmtLib.Logic.Data

import SMTLib2.Core hiding (and,or,true,false)
import qualified SMTLib2.Core as B (and,or,true,false)
import qualified SMTLib2 as S
import SMTLib2 (Expr)

import Control.Monad.State.Lazy (lift)

infixr 3 .&&
infixr 2 .||
infixr 1 .==>
infix 4 .==,./=

bvar :: Monad m => SMT m Literal
bvar = do
  l <- fresh
  declare l TBool
  return $ l

bvarm :: (Monad m, Ord a) => a -> Memo a (SMT m) Literal
bvarm = memoized $ \a -> lift bvar


(.&&), (.||) :: S.Expr -> S.Expr -> S.Expr
a .&& b
  | a == bot || b == bot = bot
  | a == top = b
  | b == top = a
  | otherwise = shallow "and" a b
a .|| b
  | a == top || b == top = top
  | a == bot = b
  | b == bot =a
  | otherwise = shallow "or" a b

(.==>) :: S.Expr -> S.Expr -> S.Expr
p .==> q = S.app "implies" [p,q]

top :: S.Expr
top = B.true

bot :: S.Expr
bot = B.false

bigAnd :: [S.Expr] -> S.Expr
bigAnd = foldr (.&&) top

bigOr :: [S.Expr] -> S.Expr
bigOr = foldr (.||) bot

(.==),(./=) :: S.Expr -> S.Expr -> S.Expr
(.==) = (===)
(./=) = (=/=)


