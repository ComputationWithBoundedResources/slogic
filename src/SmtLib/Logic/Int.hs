{-# LANGUAGE OverloadedStrings #-}
module SmtLib.Logic.Int 
  ( module SMTLib2.Int
  , nvar, ivar, svar
  , nvarm, ivarm, svarm
  , (.*), (.+), (.-)
  , (.=<),(.<),(.>),(.>=)
  , bigPlus
  , bigProd
  )
where

import SmtLib.Logic.Core ((.==), (./=), (.||))
import SmtLib.SMT
import SmtLib.Logic.Data

import SMTLib2.Int
import qualified SMTLib2 as S 

import Control.Monad.State.Lazy (lift)

infixl 7  .*
infixl 6  .+, .-
infix 4 .=<,.<,.>,.>=

ivar :: Monad m => SMT m Literal
ivar = do
  l <- fresh
  declare l TInt
  return $ l

nvar :: Monad m => SMT m Literal
nvar = do
  l <- fresh
  declare l TNat 
  {-assert $ (fm l .> num 0)-}
  return $ l

zero :: S.Expr
zero = num 0

one :: S.Expr
one = num 1

svar :: Monad m => SMT m Literal
svar = do
  l <- fresh
  declare l TNat
  let e = fm l
  assert $ (e .== zero) .|| (e .== one)
  return $ l

ivarm :: (Monad m, Ord a) => a -> Memo a (SMT m) Literal
ivarm = memoized $ \a -> lift ivar

nvarm :: (Monad m, Ord a) => a -> Memo a (SMT m) Literal
nvarm = memoized $ \a -> lift nvar

svarm :: (Monad m, Ord a) => a -> Memo a (SMT m) Literal
svarm = memoized $ \a -> lift svar


(.*),(.+),(.-) :: S.Expr -> S.Expr -> S.Expr
a .* b
  | a == zero || b == zero = zero
  | a == num 1 = b
  | b == num 1 = a
  | otherwise = shallow "*" a b
a .+ b 
  | a == num 0 = b
  | b == num 0 = a 
  | otherwise = shallow "+" a b
a .- b = nSub a b

(.<),(.=<),(.>=),(.>) :: S.Expr -> S.Expr -> S.Expr
(.<)  = nLt
(.=<) = nLeq
(.>=) = nGeq
(.>)  = nGt


bigPlus :: [S.Expr] -> S.Expr
bigPlus = foldr (.+) zero

bigProd :: [S.Expr] -> S.Expr
bigProd = foldr (.*) one
