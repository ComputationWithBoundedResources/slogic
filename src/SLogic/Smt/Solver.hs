{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
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

  -- * output
  , Format
  , DiffFormat
  , diffFormat2Format
  , format2String
  , hPutFormat
  , hPutDiffFormat

  ) where

import           Control.Monad.Trans        (MonadIO, liftIO)
import qualified Data.ByteString.Builder    as BS
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.List                  as L
import           Data.Monoid
import qualified Data.Set                   as S
import           System.Exit
import           System.IO                  (Handle, hClose, hFlush, hSetBinaryMode)
import           System.IO.Temp             (withSystemTempFile)
import           System.Process

import           SLogic.Data.Result
import           SLogic.Data.Solver
import           SLogic.Logic.Formula
import           SLogic.Smt.State


--- * pretty printer -------------------------------------------------------------------------------------------------

type Format = BS.ByteString
type DiffFormat = BS.Builder

diffFormat2Format :: DiffFormat -> Format
diffFormat2Format = BS.toLazyByteString

format2String :: Format -> String
format2String = BS.unpack

hPutFormat :: Handle -> Format -> IO ()
hPutFormat = BS.hPut

hPutDiffFormat :: Handle -> DiffFormat -> IO ()
hPutDiffFormat = BS.hPutBuilder


string :: String -> DiffFormat
string = BS.string8

int :: Int -> DiffFormat
int = BS.intDec

char :: Char -> DiffFormat
char = BS.char8

asDiffFormat :: BS.ByteString -> DiffFormat
asDiffFormat = BS.lazyByteString

ppParens :: DiffFormat -> DiffFormat
ppParens s = tLpa <> s <> tRpa

ppList :: (a -> DiffFormat) -> [a]-> DiffFormat
ppList _ []     = temp
ppList f [a]    = f a
ppList f (a:as) = f a <> tspc <> ppList f as

ppBin :: (a -> DiffFormat) -> a -> a -> DiffFormat
ppBin f a b = f a <> tspc <> f b

ppSOne :: DiffFormat -> (t -> DiffFormat) -> t -> DiffFormat
ppSOne s f a   = ppParens $ s <> tspc <> f a

ppSBin :: DiffFormat -> (t -> DiffFormat) -> t -> t -> DiffFormat
ppSBin s f a b = ppParens $ s <> tspc <> f a <> tspc <> f b

ppSExpr :: DiffFormat -> (a -> DiffFormat) -> [a]-> DiffFormat
ppSExpr s f as = ppParens $ s <> tspc <> ppList f as

temp, tspc, tLpa, tRpa :: DiffFormat
temp = mempty
tspc = char ' '
tLpa = char '('
tRpa = char ')'
tSub, tAdd, tMul :: DiffFormat
tSub = char '-'
tAdd = char '+'
tMul = char '*'
tEq, tGte, tGt :: DiffFormat
-- tLt  = string "<"
-- tLte = string "<="
tEq  = string "="
tGte = string ">="
tGt  = string ">"
tt, tf, tnot, tor, tand, tite, tip1, tip2 :: DiffFormat
tt = string "true"
tf = string "false"
tnot = string "not"
tor = string "or"
tand = string "and"
tite = string "ite"
tip1 = string "implies"
tip2 = string "=>"


data CtxIExpr = CIExpr | CAdd | CMul
data CtxIFormula = CIFormula | CAnd | COr

ppIExpr :: Var v => Bool -> CtxIExpr -> IExpr v -> DiffFormat
ppIExpr _ _ (IVar v)          = ppVar v
ppIExpr _ _ (IVal i)          = if i >= 0 then int i else ppSOne tSub int (negate i)
ppIExpr b CAdd (IAdd e1 e2)   = ppBin       (ppIExpr b CAdd) e1 e2
ppIExpr b _    (IAdd e1 e2)   = ppSBin tAdd (ppIExpr b CAdd) e1 e2
ppIExpr b CMul (IMul e1 e2)   = ppBin       (ppIExpr b CMul) e1 e2
ppIExpr b _    (IMul e1 e2)   = ppSBin tMul (ppIExpr b CMul) e1 e2
ppIExpr b _    (INeg e)       = ppSOne tSub (ppIExpr b CIExpr) e
ppIExpr b _    (IIte f e1 e2) = ppParens $ tite <> tspc <> ppIntFormula b CIFormula f <> tspc <> ppIExpr b CIExpr e1 <> tspc <> ppIExpr b CIExpr e2


ppIntFormula :: Var v => Bool -> CtxIFormula -> Formula v -> DiffFormat
ppIntFormula _ _ (BVar v)           = ppVar v
ppIntFormula _ _ Top                = tt
ppIntFormula _ _ Bot                = tf
ppIntFormula b _ (Not e)            = ppSOne tnot (ppIntFormula b CIFormula) e
ppIntFormula b CAnd (And e1 e2)     = ppBin       (ppIntFormula b CAnd) e1 e2
ppIntFormula b _    (And e1 e2)     = ppSBin tand (ppIntFormula b CAnd) e1 e2
ppIntFormula b COr  (Or e1 e2)      = ppBin       (ppIntFormula b COr ) e1 e2
ppIntFormula b _    (Or e1 e2)      = ppSBin tor  (ppIntFormula b COr ) e1 e2
ppIntFormula b _    (Implies e1 e2) = ppSExpr (if b then tip1 else tip2) (ppIntFormula b CIFormula) [e1,e2]
ppIntFormula b _    (IEq e1 e2)     = ppSBin tEq  (ppIExpr b CIExpr) e1 e2
ppIntFormula b _    (IGt e1 e2)     = ppSBin tGt  (ppIExpr b CIExpr) e1 e2
ppIntFormula b _    (IGte e1 e2)    = ppSBin tGte (ppIExpr b CIExpr) e1 e2


-- pretty printing of smt commands
ppSetLogic :: String -> DiffFormat
ppSetLogic s = string "(set-logic " <> string s <> tRpa

ppDeclareFun :: Var v => (v, VarType) -> DiffFormat
ppDeclareFun (v,ty) = string "(declare-fun " <> ppVar v <> string " () " <> asDiffFormat (BS.pack ty) <> tRpa

ppDeclareFuns :: Var v => [(v, VarType)] -> DiffFormat
ppDeclareFuns [] = temp
ppDeclareFuns as = foldr k temp as
  where k a acc = acc <> string "\n" <> ppDeclareFun a

ppAssert :: (a -> DiffFormat) -> a -> DiffFormat
ppAssert f a = string "(assert " <> f a <> tRpa

ppAsserts :: (a -> DiffFormat) -> [a] -> DiffFormat
ppAsserts _ [] = temp
ppAsserts f as = foldr k temp as
  where k a acc = string "\n" <> ppAssert f a <> acc

ppCheckSat :: DiffFormat
ppCheckSat = string "\n(check-sat)"

ppGetValues :: Var v => [v] -> DiffFormat
ppGetValues [] = temp
ppGetValues vs = string "\n(get-value " <> ppParens (ppList ppVar vs) <> string ")"

ppVar :: Var v => v -> DiffFormat
ppVar = string . fromVar

--- * solver ---------------------------------------------------------------------------------------------------------


type SolverFormatter v = SmtState v -> DiffFormat
type SolverParser v    = String -> Result (Store v)
type Args = [String]
type Cmd  = String



-- | Generic solver function
gSolver :: (MonadIO m, Var v)
  => SolverFormatter v
  -> SolverParser v
  -> Cmd
  -> Args
  -> SmtState v
  -> m (Result (Store v))
gSolver formatter parser cmd args st = do
  let input = formatter st
  liftIO . withSystemTempFile "smt2x" $ \file hfile -> do
    hSetBinaryMode hfile True
    -- hSetBuffering hfile BlockBuffering
    hPutDiffFormat hfile input
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
minismt'= gSolver minismtFormatter minismtParser "minismt"

minismtFormatter :: Var v => SolverFormatter v
minismtFormatter st =
  ppSetLogic (show $ logic st)
  <> ppDeclareFuns allvars
  <> ppAsserts (ppIntFormula True CIFormula) (asserts st)
  <> ppCheckSat
  where allvars = S.toList $ S.unions (variables `fmap` asserts st)

minismtParser :: (Var v, Storing v) => SolverParser v
minismtParser s = case lines s of
  "sat"     : _ : xs        -> Sat . fill $ map pl xs
  "unsat"   : _             -> Unsat
  "unknown" : _             -> Unknown
  "unusual termination" : _ -> Unknown
  _                         -> Error s
  where
    pl line = (toVar var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line

smt2Formatter :: Var v => SolverFormatter v
smt2Formatter st =
  ppSetLogic (show $ logic st)
  <> ppDeclareFuns allvars
  <> ppAsserts (ppIntFormula False CIFormula) (asserts st)
  <> ppCheckSat
  <> ppGetValues (fst `fmap` allvars)
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

