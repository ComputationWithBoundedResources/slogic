{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import SmtLib.Solver.MiniSmt

import SmtLib.Logic.Core
import SmtLib.Logic.Int
import SmtLib.PP
import SmtLib.SMT
{-import SmtLib.Logic.QF_NIA-}

import qualified SMTLib2 as SL
import Control.Monad.State.Lazy 
import qualified Data.Set as S
import qualified Data.Map as M

import System.IO

data A = A | B | C Int deriving (Eq, Ord, Show)

{-type Enc = M.Map A Literal-}
{-type Dec = M.Map A Constant-}



{-dom :: Monad m => [A] -> SMT m (Enc, Dec)-}
{-dom ax = do-}
  {-a <- nvar-}
  {-b <- nvar-}
  {-let-}
    {-ma = M.fromList [(A, a), (B, b)]-}
    {-mb = M.fromList [(a,A), (b,B)]-}
  {-(m1,m2) <- foldM k (ma, mb) as-}
  {-return (m1,m2)-}
  {-where-}
    {-as = S.toList $ S.fromList ax-}
    {-k (m1,m2) A = return (m1,m2)-}
    {-k (m1,m2) B = return (m1,m2)-}
    {-k (m1,m2) c@(C i) = do-}
      {-v <- nvar-}
      {-return (M.insert c v m1, M.insert v c m2)-}

{-type Enc = A -> Literal-}
{-type Dec = Literal -> A-}



{-dom :: Monad m => [A] -> SMT m (Enc, Dec)-}
{-dom ax = do-}
  {-a <- nvar-}
  {-b <- nvar-}
  {-let-}
    {-ma = M.fromList [(A, a), (B, b)]-}
    {-mb = M.fromList [(a,A), (b,B)]-}
  {-(m1, m2) <- foldM k (ma, mb) as-}
  {-return (\a -> (m1 M.! a), \a -> (m2 M.! a))-}
  {-where-}
    {-as = S.toList $ S.fromList ax-}
    {-k (m1,m2) A = return (m1,m2)-}
    {-k (m1,m2) B = return (m1,m2)-}
    {-k (m1,m2) c@(C i) = do-}
      {-v <- nvar-}
      {-return (M.insert c v m1, M.insert v c m2)-}

type Enc = M.Map A Literal
      
dom :: Monad m => [A] -> SMT m (Enc)
dom ax = do
  a <- nvar
  b <- nvar
  let
    ma = M.fromList [(A,a), (B,b)]
  foldM k ma as
  where
    as = S.toList $ S.fromList ax
    k m1 A = return m1
    k m1 B = return m1
    k m1 c@(C i) = do
      v <- nvar
      return $ M.insert c v m1


en :: Monad m => SMT m (M.Map A Literal)
en = snd `liftM`  (memo $ mapM nvarm [A,B])

main :: IO ()
main = do
  res :: Maybe (M.Map A Constant) <- solve minismt $ do
    setLogic "QF_NIA"
    (a,m) <- memo $ do
      nvarm A
      nvarm A
      nvarm B
      svarm (C 1)
      svarm (C 2)
    let 
      a = m M.! A
      b = m M.! B
      c = m M.! (C 1) 
      d = m M.! (C 2) 
    {-assert $ toExpr a .== toExpr b-}
    assert $ fm c .== fm d
    return $ decode m
  print res

  {-res :: Maybe (M.Map A Constant) <- solve minismt $ do-}
    {-setLogic "QF_NIA"-}
    {-a <- nvar' A-}
    {-b <- nvar' B-}
    {-c1 <- nvar' (C 1)-}
    {-c2 <- nvar' (C 1)-}
     
    {-let (b,en) = runm bigAnd [ a .== b ]-}
    {-assert b-}
    {-return $ decode en-}
  {-print res-}


