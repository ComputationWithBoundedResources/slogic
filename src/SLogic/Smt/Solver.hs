{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides 'Solver' implementations for SMT - Formula IFormula
module SLogic.Smt.Solver
  (
  minismt
  , minismt'

  , yices
  , yices'

  , z3
  , z3'
  ) where

import System.IO.Temp (withSystemTempFile)
import System.IO (hFlush, hClose)
import Data.Monoid
import qualified Data.ByteString.Char8 as BS
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


type DString = BS.ByteString -> BS.ByteString

toDString :: String -> DString
toDString s d = BS.pack s <> d

asDString :: BS.ByteString -> DString
asDString s d = s <> d

ppParens :: DString -> DString
ppParens s = tLpa . s . tRpa

ppList :: (a -> DString) -> [a]-> DString
ppList _ []     = temp
ppList f [a]    = f a
ppList f (a:as) = f a . tspc . ppList f as

ppSExpr :: DString -> (a -> DString) -> [a]-> DString
ppSExpr s f as = ppParens $ s . tspc . ppList f as

ppIExpr :: IExpr -> DString
ppIExpr e = case e of
  IVar v _ -> asDString v
  IVal i   -> toDString (show i)
  Neg e1   -> ppSExpr tSub ppIExpr [e1]
  Add es   -> ppSExpr tAdd ppIExpr es
  Mul es   -> ppSExpr tMul ppIExpr es

temp, tspc, tLpa, tRpa :: DString
temp = toDString ""
tspc = toDString " "
tLpa = toDString "("
tRpa = toDString ")"
tSub, tAdd, tMul :: DString
tSub = toDString "-"
tAdd = toDString "+"
tMul = toDString "*"
tLt, tLte, tEq, tGte, tGt :: DString
tLt  = toDString "<"
tLte = toDString "<="
tEq  = toDString "="
tGte = toDString ">="
tGt  = toDString ">"
tt, tf, tnot, tor, tand, tite, tip1, tip2 :: DString
tt = toDString "true"
tf = toDString "false"
tnot = toDString "not"
tor = toDString "or"
tand = toDString "and"
tite = toDString "ite"
tip1 = toDString "implies"
tip2 = toDString "=>"

ppIFormula :: IFormula -> DString
ppIFormula e = case e of
  Lt e1 e2  -> pp tLt e1 e2
  Lte e1 e2 -> pp tLte e1 e2
  IEq e1 e2 -> pp tEq e1 e2
  Gte e1 e2 -> pp tGte e1 e2
  Gt e1 e2  -> pp tGt e1 e2
  where pp s e1 e2 = ppSExpr s ppIExpr [e1,e2]

ppExpr' :: Bool -> (e -> DString) -> Formula e -> DString
ppExpr' isImplies ppAtom e = case e of
  Atom a        -> ppAtom a
  BVar v        -> asDString v
  BVal b        -> if b then tt else tf
  Not e1        -> pp tnot [e1]
  And es        -> pp tand es
  Or es         -> pp tor es
  Ite e1 e2 e3  -> pp tite [e1,e2,e3]
  Implies e1 e2 -> pp (if isImplies then tip1 else tip2) [e1,e2]
  Eq e1 e2      -> pp tEq [e1, e2]
  where pp s = ppSExpr s (ppExpr' isImplies ppAtom)


-- pretty printing of smt commands
ppSetLogic :: String -> DString
ppSetLogic s = toDString "(set-logic " . toDString s . tRpa

ppDeclareFun :: (Var, VType) -> DString
ppDeclareFun (v,ty) = toDString "(declare-fun " . asDString v . toDString " () " . asDString ty . tRpa

ppDeclareFuns :: [(Var, VType)] -> DString
ppDeclareFuns [] = temp 
ppDeclareFuns as = foldr k temp as
  where k a acc = acc . toDString "\n" . ppDeclareFun a

ppAssert :: (a -> DString) -> a -> DString
ppAssert f a = toDString "(assert " . f a . tRpa

ppAsserts :: (a -> DString) -> [a] -> DString
ppAsserts _ [] = temp
ppAsserts f as = foldr k temp as
  where k a acc = toDString "\n" . ppAssert f a . acc

ppCheckSat :: DString
ppCheckSat = toDString "\n(check-sat)"

ppGetValues :: [Var] -> DString
ppGetValues [] = temp
ppGetValues vs = toDString "\n(get-value " . ppParens (ppList asDString vs) . toDString ")"
  


-- MS:
-- minismt format differs a bit from the smt2 standard
-- * supports Nat type
-- * implication: "implies" instead of "=>"
-- * (get-value (fn)) returns a parse error; to get a model use -m
-- * since minismt 0.6; the second line displays the time
--
-- TODO: insert version check


ppMinismt :: SolverState (Formula IFormula) -> DString
ppMinismt st = 
  ppSetLogic (format st)
  . ppDeclareFuns allvars
  . ppAsserts (ppExpr' True ppIFormula) (asserts st)
  . ppCheckSat
  where allvars = S.toList $ foldl (\s -> S.union s . vars) S.empty (asserts st)

-- | Default minismt solver.
minismt :: Solver (SolverState (Formula IFormula))
minismt = minismt' ["-m","-v2"]

-- | Minismt solver. Constructs the problem from 'SolverState'.
minismt' :: [String] -> Solver (SolverState (Formula IFormula))
minismt' args st = do
  let input = ppMinismt st BS.empty
  withSystemTempFile "smt2x" $ \file hfile -> do
    BS.hPutStr hfile input
    hFlush hfile
    hClose hfile
    (code , stdout, stderr) <- readProcessWithExitCode "minismt" (args ++ [file]) ""
    return $ case code of
      ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
      ExitSuccess   -> case lines stdout of
        "sat"   : _ : xs -> Sat . M.fromList $ map parse xs
        "unsat" : _      -> Unsat
        "unknown" : _    -> Unknown
        _                -> Error stdout
  where
    parse line = (strVar var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line


-- smt2lib Standard
-- does not support Nat as available in Formula IFormula
-- hence, we declare each Nat variable as Int and add an additional assertion
ppSmt2 ::  SolverState (Formula IFormula) -> DString
ppSmt2 st = 
    ppSetLogic (format st)
    . ppDeclareFuns varsL
    . ppDeclareFuns natsL
    . ppAsserts (ppExpr' False ppIFormula) (asserts st)
    . ppAsserts (ppExpr' False ppIFormula) (map nat natsL)
    . ppCheckSat
    . ppGetValues (map fst varsL)
    . ppGetValues (map fst natsL)
    where
      allvarsS      = foldl (\s -> S.union s . vars) S.empty (asserts st)
      (natsS,varsS) = S.partition ((== BS.pack "Nat") . snd) allvarsS
      varsL = S.toList varsS
      natsL = map (\(v,_) -> (v, BS.pack "Int")) $ S.toList natsS
      nat (v,ty) = IVar v ty .>= IVal 0

smt2 :: String -> [String] -> Solver (SolverState (Formula IFormula))
smt2 p args st = do
  let input = ppSmt2 st BS.empty
  withSystemTempFile "smt2x" $ \file hfile -> do
    BS.hPutStr hfile input
    hFlush hfile
    hClose hfile
    (code , stdout, stderr) <- readProcessWithExitCode p (args ++ [file]) ""
    return $ case code of
      ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
      ExitSuccess   -> case lines stdout of
        "sat"   : xs  -> Sat . M.fromList $ map parse xs
        "unsat" : _   -> Unsat
        "unknown" : _ -> Unknown
        _             -> Error stdout
    where
      parse line = (strVar var, read (tail val)::Value)
        where (var,val) = break (== ' ') . filter (`L.notElem` "()") $ dropWhile (==' ') line


yices :: Solver (SolverState (Formula IFormula))
yices = yices' []

yices' :: [String] -> Solver (SolverState (Formula IFormula))
yices' = smt2 "yices-smt2"

z3 :: Solver (SolverState (Formula IFormula))
z3 = z3' ["-smt2","-in"]

z3' :: [String] -> Solver (SolverState (Formula IFormula))
z3' = smt2 "z3"

