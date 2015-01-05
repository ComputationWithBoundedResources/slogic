{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
-- | This module provides 'Solver' implementations for SMT - Formula IFormula
--
module SLogic.Smt.Solver
  (
  minismt
  , minismt'

  , yices
  , yices'

  , z3
  , z3'
  ) where

import Data.Monoid
import qualified Data.DList as DL
import qualified Data.List                    as L
import qualified Data.Map.Strict              as M
import qualified Data.Set                     as S
import           System.Exit
import           System.Process

import           SLogic.Logic.Core
import           SLogic.Logic.Int
import           SLogic.Result
import           SLogic.Solver
import           SLogic.SolverState


type DString = DL.DList Char

ppParens :: DString -> DString
ppParens s = "(" <> s <> ")"

ppList :: (a -> DString) -> [a]-> DString
ppList _ []     = ""
ppList f [a]    = f a
ppList f (a:as) = f a <> " " <> ppList f as

ppSExpr :: DString -> (a -> DString) -> [a]-> DString
ppSExpr s f as = ppParens $ s <> " " <> ppList f as

ppIExpr :: IExpr -> DString
ppIExpr e = case e of
  IVar v _ -> DL.fromList v
  IVal i   -> DL.fromList (show i)
  Neg e1   -> ppParens $ "- " <> ppIExpr e1
  Add es   -> ppSExpr "+" ppIExpr es
  Mul es   -> ppSExpr "*" ppIExpr es

ppIFormula :: IFormula -> DString
ppIFormula e = case e of
  Lt e1 e2  -> pp "<" e1 e2
  Lte e1 e2 -> pp "<=" e1 e2
  IEq e1 e2 -> pp "=" e1 e2
  Gte e1 e2 -> pp ">=" e1 e2
  Gt e1 e2  -> pp ">" e1 e2
  where pp s e1 e2 = ppSExpr s ppIExpr [e1,e2]

ppExpr' :: Bool -> (e -> DString) -> Formula e -> DString
ppExpr' isImplies ppAtom e = case e of
  Atom a        -> ppAtom a
  BVar v        -> DL.fromList v
  BVal b        -> if b then "true" else "false"
  Not e1        -> pp "not" [e1]
  And es        -> pp "and" es
  Or es         -> pp "or" es
  Ite e1 e2 e3  -> pp "ite" [e1,e2,e3]
  Implies e1 e2 -> pp (if isImplies then "implies" else "=>") [e1,e2]
  Eq e1 e2      -> pp "=" [e1, e2]
  where pp s = ppSExpr s (ppExpr' isImplies ppAtom) 


-- pretty printing of smt commands
ppSetLogic :: String -> DString
ppSetLogic s = "(set-logic " <> DL.fromList s <> ")"

ppDeclareFun :: (Var, String) -> DString
ppDeclareFun (v,ty) = "(declare-fun " <> DL.fromList v <> " () " <> DL.fromList ty <> ")"

ppDeclareFuns :: [(Var,String)] -> DString
ppDeclareFuns [] = ""
ppDeclareFuns as = foldr k "" as
  where k a acc = acc <> "\n" <> ppDeclareFun a

ppAssert :: (a -> DString) -> a -> DString
ppAssert f a = "(assert " <> f a <> ")"

ppAsserts :: (a -> DString) -> [a] -> DString
ppAsserts _ [] = ""
ppAsserts f as = foldr k "" as
  where k a acc = "\n" <> ppAssert f a <> acc

ppCheckSat :: DString
ppCheckSat = "\n(check-sat)"

ppGetValues :: [Var] -> DString
ppGetValues [] = ""
ppGetValues vs = "\n(get-value " <> ppParens (ppList DL.fromList vs) <> ")"
  


-- MS:
-- minismt format differs a bit from the smt2 standard
-- * supports Nat type
-- * implication: "implies" instead of "=>"
-- * (get-value (fn)) returns a parse error; to get a model use -m
-- * since minismt 0.6; the second line displays the time
--
-- TODO: insert version check


ppMinismt :: SolverState (Formula IFormula) -> String
ppMinismt st = DL.toList $ 
  ppSetLogic (format st)
  <> ppDeclareFuns allvars
  <> ppAsserts (ppExpr' True ppIFormula) (asserts st)
  <> ppCheckSat
  where allvars = S.toList $ foldl (\s -> S.union s . vars) S.empty (asserts st)

-- | Default minismt solver.
minismt :: Solver (SolverState (Formula IFormula))
minismt = minismt' ["-m","-v2"]

-- | Minismt solver. Constructs the problem from 'SolverState'.
minismt' :: [String] -> Solver (SolverState (Formula IFormula))
minismt' args st = do
  let input = ppMinismt st
  writeFile "/tmp/fm.smt2" input
  (code , stdout, stderr) <- readProcessWithExitCode "minismt" args input
  return $ case code of
    ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
    ExitSuccess   -> case lines stdout of
      "sat"   : _ : xs -> Sat . M.fromList $ map parse xs
      "unsat" : _      -> Unsat
      "unknown" : _    -> Unknown
      _                -> Error stdout
  where
    parse line = (var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line


-- smt2lib Standard
-- does not support Nat as available in Formula IFormula
-- hence, we declare each Nat variable as Int and add an additional assertion
ppSmt2 ::  SolverState (Formula IFormula) -> String
ppSmt2 st = DL.toList $ 
    ppSetLogic (format st)
    <> ppDeclareFuns varsL
    <> ppDeclareFuns natsL
    <> ppAsserts (ppExpr' False ppIFormula) (asserts st)
    <> ppAsserts (ppExpr' False ppIFormula) (map nat natsL)
    <> ppCheckSat
    <> ppGetValues (map fst varsL)
    <> ppGetValues (map fst natsL)
    where
      allvarsS      = foldl (\s -> S.union s . vars) S.empty (asserts st)
      (natsS,varsS) = S.partition ((== "Nat") . snd) allvarsS
      varsL = S.toList varsS
      natsL = map (\(v,_) -> (v,"Int")) $ S.toList natsS
      nat (v,ty) = IVar v ty .>= IVal 0

smt2 :: String -> [String] -> Solver (SolverState (Formula IFormula))
smt2 p args st = do
  let input = ppSmt2 st
  writeFile "/tmp/fm.smt2" input
  (code , stdout, stderr) <- readProcessWithExitCode p args input
  return $ case code of
    ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
    ExitSuccess   -> case lines stdout of
      "sat"   : xs  -> Sat . M.fromList $ map parse xs
      "unsat" : _   -> Unsat
      "unknown" : _ -> Unknown
      _             -> Error stdout
  where
    parse line = (var, read (tail val)::Value)
      where (var,val) = break (== ' ') . filter (`L.notElem` "()") $ dropWhile (==' ') line


yices :: Solver (SolverState (Formula IFormula))
yices = yices' []

yices' :: [String] -> Solver (SolverState (Formula IFormula))
yices' = smt2 "yices-smt2"

z3 :: Solver (SolverState (Formula IFormula))
z3 = z3' ["-smt2","-in"]

z3' :: [String] -> Solver (SolverState (Formula IFormula))
z3' = smt2 "z3"

