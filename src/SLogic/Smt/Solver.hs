{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides 'Solver' implementations for SMT - Formula IFormula
module SLogic.Smt.Solver
  (
  SolverOptions (..)
  , defaultOptions

  , minismt
  , minismt'

  , yices
  , yices'

  , z3
  , z3'
  ) where

import qualified Control.Exception     as E
import           Control.Monad.Trans   (MonadIO, liftIO)
import qualified Data.ByteString.Char8 as BS
import qualified Data.List             as L
import qualified Data.Map.Strict       as M
import           Data.Monoid
import qualified Data.Set              as S
import           System.Exit
import           System.IO             (Handle, hClose, hFlush)
import           System.IO.Temp        (openTempFile, withSystemTempFile)
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


--- * solver ---------------------------------------------------------------------------------------------------------

-- MS: we use temporary files for the external solvers
withFile :: Maybe FilePath -> Maybe FilePath -> (FilePath -> Handle -> IO a) -> IO a
withFile (Just fb) (Just na) = E.bracket (openTempFile fb na) (hClose . snd) . uncurry
withFile (Just fb) Nothing   = E.bracket (openTempFile fb "smt2") (hClose . snd) . uncurry
withFile Nothing (Just na)   = withSystemTempFile na
withFile _ _                 = withSystemTempFile "smt2"

type Args = [String]
type Cmd = String


-- MS: readProcessWithExitCode does not kill the external process only sends a SIGTERM signal
-- so the temporary file may be locked when sending threadKill in an async setting.
-- | Solver options
-- Temporary files are used for the external solvers. 'tmpFile' indicates a suffix of the temporary file. If 'tmpDir'
-- is not set, an attempt to delete the temporary file is made. Note: This may file in an asynchrouns setting, due to
-- the current process handling. If 'tmpDir' is set temporary files are stored in the 'tmpDir'.
data SolverOptions = SolverOptions
  { args    :: Args            -- ^ cmd specific arguments
  , tmpDir  :: Maybe FilePath
  , tmpFile :: Maybe FilePath }

-- | Default options.
defaultOptions :: Args -> SolverOptions
defaultOptions as = SolverOptions { args = as, tmpDir = Nothing, tmpFile = Nothing }

-- | Generic solver function
gSolver :: MonadIO m =>
  (SolverState (Formula IFormula) -> DString)
  -> (String -> (Var, Value))
  -> Cmd
  -> SolverOptions
  -> Solver m (SolverState (Formula IFormula))
gSolver pp pl cmd opts st = do
  let input = pp st BS.empty
  liftIO $ withFile (tmpDir opts) (tmpFile opts) $ \file hfile -> do
    BS.hPutStr hfile input
    hFlush hfile
    hClose hfile
    (code , stdout, stderr) <- readProcessWithExitCode cmd (args opts ++ [file]) ""
    return $ case code of
      ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
      ExitSuccess   -> case lines stdout of
        ["sat"]                   -> Sat M.empty
        "sat"     : x@('(':_): xs -> Sat . M.fromList $ map pl (x:xs)
        "sat"     : _ : xs        -> Sat . M.fromList $ map pl xs
        "unsat"   : _             -> Unsat
        "unknown" : _             -> Unknown
        _                         -> Error stdout


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

plMinismt :: String -> (Var, Value)
plMinismt line = (strVar var, read (tail val)::Value)
  where (var,val) = break (== '=') $ filter (/=' ') line

-- | Default minismt solver.
minismt :: MonadIO m => Solver m (SolverState (Formula IFormula))
minismt = minismt' (defaultOptions ["-m","-v2"])

-- | minismt solver.
minismt' ::  MonadIO m => SolverOptions -> Solver m (SolverState (Formula IFormula))
minismt'= gSolver ppMinismt plMinismt "minismt"

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

plSmt2 :: String -> (Var, Value)
plSmt2 line = (strVar var, read (tail val)::Value)
  where (var,val) = break (== ' ') . filter (`L.notElem` "()") $ dropWhile (==' ') line

yices :: MonadIO m => Solver m (SolverState (Formula IFormula))
yices = yices' (defaultOptions [])

yices' :: MonadIO m => SolverOptions -> Solver m (SolverState (Formula IFormula))
yices' = gSolver ppSmt2 plSmt2 "yices-smt2"

z3 :: MonadIO m => Solver m (SolverState (Formula IFormula))
z3 = z3' (defaultOptions ["-smt2", "-in"])

z3' :: MonadIO m => SolverOptions -> Solver m (SolverState (Formula IFormula))
z3' = gSolver ppSmt2 plSmt2 "z3"

