{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides 'Solver' implementations for SMT.
module SLogic.Smt.Solver
  (
  minismt
  , minismt'

  , yices
  , yices'

  , z3
  , z3'
  ) where


import qualified Data.Map.Strict                   as M
import qualified Data.List as L
import qualified Data.Set                          as S
import           System.Exit
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen      as PP

import           SLogic.Logic.Core
import           SLogic.Logic.Int
import           SLogic.Result
import           SLogic.Solver
import           SLogic.SolverState


-- default pretty printing
ppIExpr :: IExpr-> PP.Doc
ppIExpr e = case e of
  IVar v _  -> PP.text v
  IVal i    -> PP.int i
  Neg e1    -> ppsexpr "-"  [e1]
  Add e1 e2 -> ppsexpr "+"  [e1,e2]
  Mul e1 e2 -> ppsexpr "*"  [e1,e2]
  where ppsexpr op es = PP.parens (PP.hsep $ PP.text op : map ppIExpr es)

ppTInt :: TInt -> PP.Doc
ppTInt e = case e of
  IExpr e1  -> ppIExpr e1
  Lt e1 e2  -> ppbin "<" e1 e2
  Lte e1 e2 -> ppbin "<=" e1 e2
  Gte e1 e2 -> ppbin ">=" e1 e2
  Gt e1 e2  -> ppbin ">" e1 e2
  where ppbin op e1 e2 = PP.parens (PP.text op PP.<+> ppIExpr e1 PP.<+> ppIExpr e2)

ppExpr' :: Bool -> (e -> PP.Doc) -> Formula e -> PP.Doc
ppExpr' isImplies ppAtom e = case e of
  Atom a        -> ppAtom a
  BVar v        -> PP.text v
  BVal b        -> PP.text (if b then "true" else "false")
  Not e1        -> ppsexpr "not" [e1]
  And e1 e2     -> ppsexpr "and" [e1,e2]
  Or e1 e2      -> ppsexpr "or" [e1,e2]
  Ite e1 e2 e3  -> ppsexpr "ite" [e1,e2,e3]
  Implies e1 e2 -> ppsexpr (if isImplies then "implies" else "=>") [e1,e2]
  Eq e1 e2      -> ppsexpr "=" [e1, e2]
  where ppsexpr op es = PP.parens (PP.hsep $ PP.text op : map (ppExpr' isImplies ppAtom)  es)


instance PP.Pretty TInt where
  pretty = ppTInt

-- pretty printing of smt commands
ppSetLogic :: String -> PP.Doc
ppSetLogic s = PP.parens (PP.text "set-logic" PP.<+> PP.text s)

ppDeclareFun :: (Var, String) -> PP.Doc
ppDeclareFun (v,ty) = PP.parens (PP.text "declare-fun" PP.<+> PP.text v PP.<+> PP.text "()" PP.<+> PP.text ty)

ppAssert :: PP.Doc -> PP.Doc
ppAssert a = PP.parens (PP.text "assert" PP.<+> a)

ppCheckSat :: PP.Doc
ppCheckSat = PP.parens (PP.text "check-sat")

ppGetValues :: [Var] -> PP.Doc
ppGetValues vs = PP.parens $ PP.text "get-value" PP.<+> PP.encloseSep PP.lparen PP.rparen PP.space (map PP.text vs)


-- MS: 
-- minismt format differs a bit from the smt2 standard
-- implication: "implies" instead of "=>"
-- (get-value (fn)) returns a parse error; to get a model use -m 
-- since minismt 0.6; the second line displays the time
-- TODO: insert version check
newtype Minismt f = Minismt f

ppExprMinismt :: PP.Pretty e => Formula e -> PP.Doc
ppExprMinismt = ppExpr' True PP.pretty

instance PP.Pretty (Minismt (SolverState ( Formula TInt))) where
  pretty (Minismt st) =
    ppSetLogic (format st)
    PP.<$> PP.vcat (map ppDeclareFun allvars)
    PP.<$> PP.vcat (map (ppAssert . ppExprMinismt) (reverse $ asserts st))
    PP.<$> ppCheckSat
    PP.<$> PP.empty
    where allvars = S.toList $ foldl (\s -> S.union s . vars) S.empty (asserts st)

-- | Default minismt solver.
minismt :: Solver (SolverState (Formula TInt))
minismt = minismt' ["-m","-v2"]

-- | Minismt solver. Constructs the problem from 'SolverState'.
minismt' :: [String] -> Solver (SolverState (Formula TInt))
minismt' args st = do
  let input = show $ PP.pretty (Minismt st)
  writeFile "/tmp/fm.smt2" input
  (code , stdout, stderr) <- readProcessWithExitCode "minismt" args input
  return $ case code of
    ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
    ExitSuccess   -> case lines stdout of
      "sat"   : _ : xs  -> Sat . M.fromList $ map parse xs
      "unsat" : _       -> Unsat
      "unknown" : _     -> Unknown
      "parse error" : _ -> Error "minismt: parse error"
      _                 -> Error "some error"
  where
    parse line = (var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line


-- Smt2 Standard
-- MS: replace IVar v Nat with IVar v Int + assertion v >= 0
newtype Smt2 f = Smt2 f

ppExprSmt2 :: PP.Pretty e => Formula e -> PP.Doc
ppExprSmt2 = ppExpr' False PP.pretty

instance PP.Pretty (Smt2 (SolverState (Formula TInt))) where
  pretty (Smt2 st) =
    ppSetLogic (format st)
    PP.<$> PP.vcat (map ppDeclareFun varsL)
    PP.<$> PP.vcat (map ppDeclareFun natsL)
    PP.<$> PP.vcat (map (ppAssert . ppExprSmt2) (reverse $ asserts st))
    PP.<$> PP.vcat (map (ppAssert . ppExprSmt2 . nat) natsL)
    PP.<$> ppCheckSat
    PP.<$> ppGetValues (map fst varsL)
    PP.<$> ppGetValues (map fst natsL)
    PP.<$> PP.empty
    where 
      allvarsS      = foldl (\s -> S.union s . vars) S.empty (asserts st)
      (varsS,natsS) = S.partition ((== "Nat") . snd) allvarsS
      varsL = S.toList varsS
      natsL = map (\(v,_) -> (v,"Int")) $ S.toList natsS
      nat (v,ty) = IVar v ty .>= IVal 0

smt2 :: String -> [String] -> Solver (SolverState (Formula TInt))
smt2 p args st = do
  let input = show $ PP.pretty (Smt2 st)
  writeFile "/tmp/fm.smt2" input
  (code , stdout, stderr) <- readProcessWithExitCode p args input
  return $ case code of
    ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
    ExitSuccess   -> case lines stdout of
      "sat"   : xs      -> Sat . M.fromList $ map parse xs
      "unsat" : _       -> Unsat
      "unknown" : _     -> Unknown
      _                 -> Error "some error"
  where
    parse line = (var, read (tail val)::Value)
      where (var,val) = break (== ' ') . filter (`L.notElem` "()") $ dropWhile (==' ') line


yices :: Solver (SolverState (Formula TInt))
yices = yices' []

yices' :: [String] -> Solver (SolverState (Formula TInt))
yices' = smt2 "yices-smt2"

z3 :: Solver (SolverState (Formula TInt))
z3 = z3' []

z3' :: [String] -> Solver (SolverState (Formula TInt))
z3' = smt2 "z3"

