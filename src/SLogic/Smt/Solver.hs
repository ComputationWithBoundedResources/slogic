{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-- | This module provides 'Solver' implementations for SMT - Formula IFormula
module SLogic.Smt.Solver
  (
  -- * default solver
  minismt
  , minismt'

  , yices
  , yices'

  , z3
  , z3'

  -- * pretty printer and result parser for custom IO interaction
  , SolverFormatter
  , SolverParser
  , Args
  , Cmd

  , minismtFormatter
  , minismtParser

  , yicesFormatter
  , yicesParser

  , z3Formatter
  , z3Parser
  ) where

import           Control.Monad.Trans   (MonadIO, liftIO)
import qualified Data.ByteString.Char8 as BS
import qualified Data.List             as L
import           Data.Monoid
import qualified Data.Set              as S
import           System.Exit
import           System.IO             (hClose, hFlush)
import           System.IO.Temp        (withSystemTempFile)
import           System.Process

import           SLogic.Logic.Formula
import           SLogic.Data.Result
import           SLogic.Data.Solver
import           SLogic.Smt.State


--- * pretty printer -------------------------------------------------------------------------------------------------

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

temp, tspc, tLpa, tRpa :: DString
temp = toDString ""
tspc = toDString " "
tLpa = toDString "("
tRpa = toDString ")"
tSub, tAdd, tMul :: DString
tSub = toDString "-"
tAdd = toDString "+"
tMul = toDString "*"
tEq, tGte, tGt :: DString
-- tLt  = toDString "<"
-- tLte = toDString "<="
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


ppIExpr :: Var v => Bool -> IExpr v -> DString
ppIExpr b e = case e of
  IVar v       -> ppVar v
  IVal i       -> toDString (show i)
  ISub es      -> pp tSub es
  IAdd es      -> pp tAdd es
  IMul es      -> pp tMul es
  IIte f e1 e2 -> ppParens $ tite . ppIntFormula b f . ppIExpr b e1 . ppIExpr b e2
  where pp t = ppSExpr t (ppIExpr b)


ppIntFormula :: Var v => Bool -> Formula v -> DString
ppIntFormula imp e = case e of
  BVar v        -> ppVar v
  BVal b        -> if b then tt else tf
  Not e1        -> pps tnot [e1]
  And es        -> pps tand es
  Or es         -> pps tor es
  Implies e1 e2 -> pps (if imp then tip1 else tip2) [e1,e2]

  IEq e1 e2  -> pp2 tEq e1 e2
  IGt e1 e2  -> pp2 tGt e1 e2
  IGte e1 e2 -> pp2 tGte e1 e2
  where 
    pps s = ppSExpr s (ppIntFormula imp)
    pp2 s e1 e2 = ppSExpr s (ppIExpr imp) [e1,e2]

-- ppExpr' :: Var v => Bool -> Formula v -> DString
-- ppExpr' isImplies e = case e of
--   BVar v        -> ppVar v
--   BVal b        -> if b then tt else tf
--   Not e1        -> pp tnot [e1]
--   And es        -> pp tand es
--   Or es         -> pp tor es
  -- Ite e1 e2 e3  -> pp tite [e1,e2,e3]
  -- Implies e1 e2 -> pp (if isImplies then tip1 else tip2) [e1,e2]
  -- Eq e1 e2      -> pp tEq [e1, e2]
  -- where pp s = ppSExpr s (ppExpr' isImplies)


-- pretty printing of smt commands
ppSetLogic :: String -> DString
ppSetLogic s = toDString "(set-logic " . toDString s . tRpa

ppDeclareFun :: Var v => (v, VarType) -> DString
ppDeclareFun (v,ty) = toDString "(declare-fun " . ppVar v . toDString " () " . asDString (BS.pack ty) . tRpa

ppDeclareFuns :: Var v => [(v, VarType)] -> DString
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

ppGetValues :: Var v => [v] -> DString
ppGetValues [] = temp
ppGetValues vs = toDString "\n(get-value " . ppParens (ppList ppVar vs) . toDString ")"

ppVar :: Var v => v -> DString
ppVar = asDString . BS.pack . fromVar

--- * solver ---------------------------------------------------------------------------------------------------------


type SolverFormatter v = SmtState v -> BS.ByteString
type SolverParser v    = String -> Result (Store v)
type Args = [String]
type Cmd  = String



-- | Generic solver function
gSolver :: (MonadIO m, Var v)
  => SolverFormatter v
  -> SolverParser v
  -> Cmd
  -> Args
  -> (SmtState v) 
  -> m (Result (Store v))
gSolver formatter parser cmd args st = do
  let input = formatter st
  liftIO . withSystemTempFile "smt2x" $ \file hfile -> do
    BS.hPutStr hfile input
    hFlush hfile
    hClose hfile
    (code, stdout, stderr) <- readProcessWithExitCode cmd (args ++ [file]) ""
    return $ case code of
      ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
      ExitSuccess   -> parser stdout

-- MS:
-- minismt format differs a bit from the smt2 standard
-- * supports Nat type
-- * implication: "implies" instead of "=>"
-- * (get-value (fn)) returns a parse error; to get a model use -m
-- * since minismt 0.6; the second line displays the time

-- | Default minismt solver.
minismt :: (MonadIO m, Var v, Storing v) => SmtSolver m v
minismt = minismt' ["-m","-v2"]

-- | minismt solver.
minismt' ::  (MonadIO m, Storing v, Var v) => Args -> SmtSolver m v
minismt'= gSolver (minismtFormatter) (minismtParser) "minismt"

minismtFormatter :: Var v => SolverFormatter v
minismtFormatter st = 
  (ppSetLogic (show $ logic st)
  . ppDeclareFuns allvars
  . ppAsserts (ppIntFormula True) (asserts st)
  . ppCheckSat) BS.empty
  where allvars = S.toList $ S.unions (variables `fmap` asserts st)

minismtParser :: (Var v, Storing v) => SolverParser v
minismtParser s = case lines s of
  "sat"     : _ : xs        -> Sat . fill $ map pl xs
  "unsat"   : _             -> Unsat
  "unknown" : _             -> Unknown
  _                         -> Error s
  where
    pl line = (toVar var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line

smt2Formatter :: Var v => SolverFormatter v
smt2Formatter st =
  (ppSetLogic (show $ logic st)
  . ppDeclareFuns allvars
  . ppAsserts (ppIntFormula False) (asserts st)
  . ppCheckSat
  . ppGetValues (fst `fmap` allvars)) BS.empty
  where allvars = S.toList $ S.unions (variables `fmap` asserts st)

smt2Parser :: (Var v, Storing v) => SolverParser v
smt2Parser s = case lines s of
  "sat"     : xs -> Sat . fill $ map pl xs
  "unsat"   : _  -> Unsat
  "unknown" : _  -> Unknown
  _              -> Error s
  where
    pl line = (toVar var, read (tail val)::Value)
      where (var,val) = break (== ' ') . filter (`L.notElem` "()") $ dropWhile (==' ') line


yicesFormatter :: Var v => SolverFormatter v
yicesFormatter = smt2Formatter

yicesParser :: (Var v, Storing v) => SolverParser v
yicesParser = smt2Parser

z3Formatter :: Var v => SolverFormatter v
z3Formatter = smt2Formatter

z3Parser :: (Var v, Storing v) => SolverParser v
z3Parser = smt2Parser

yices :: (MonadIO m, Storing v, Var v) => SmtSolver m v
yices = yices' []

yices' :: (MonadIO m, Storing v, Var v) => Args -> SmtSolver m v
yices' = gSolver yicesFormatter yicesParser "yices-smt2"

z3 :: (MonadIO m, Storing v, Var v) => SmtSolver m v
z3 = z3' ["-smt2", "-in"]

z3' :: (MonadIO m, Storing v, Var v) => Args -> SmtSolver m v
z3' = gSolver z3Formatter z3Parser "z3"

