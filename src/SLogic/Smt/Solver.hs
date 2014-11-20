{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides 'Solver' implementations for SMT.
module SLogic.Smt.Solver
  (minismt)
  where

import           Data.Generics.Uniplate.Operations
import qualified Data.Map.Strict                   as M
import qualified Data.Set                          as S
import           System.Exit
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen      as PP

import           SLogic.Logic.Core
import           SLogic.Logic.Int
import           SLogic.Result
import           SLogic.Solver
import           SLogic.SolverState


class Vars e where
  vars :: e -> S.Set (String, String)

instance Vars TInt where
  vars e = S.fromList [ (v, ty) | IVar v ty <- universeBi e]

instance Vars e => Vars (Formula e) where
  vars e = bvs `S.union` evs
   where
     evs = S.unions   [ vars a      | Atom a <- es ]
     bvs = S.fromList [ (v,"Bool")  | BVar v <- es ]
     es = universe e

-- default pretty printing
ppIExpr :: IExpr-> PP.Doc
ppIExpr e = case e of
  IVar v _ -> PP.text v
  IVal i -> PP.int i
  Neg e1 -> ppsexpr "-"  [e1]
  Add es -> ppsexpr "+"  es
  Mul es -> ppsexpr "*"  es
  where ppsexpr op es = PP.parens (PP.hsep $ PP.text op : map ppIExpr es)

ppTInt :: TInt -> PP.Doc
ppTInt e = case e of
  IExpr e1  -> ppIExpr e1
  Lt e1 e2  -> ppbin "<" e1 e2
  Lte e1 e2 -> ppbin "<=" e1 e2
  Gte e1 e2 -> ppbin ">=" e1 e2
  Gt e1 e2  -> ppbin ">" e1 e2
  where ppbin op e1 e2 = PP.parens (PP.text op PP.<+> ppIExpr e1 PP.<+> ppIExpr e2)

ppExpr :: (e -> PP.Doc) -> Formula e -> PP.Doc
ppExpr ppAtom e = case e of
  Atom a        -> ppAtom a
  BVar v        -> PP.text v
  BVal b        -> PP.text (if b then "true" else "false")
  Not e1        -> ppsexpr "-" [e1]
  And es        -> ppsexpr "and" es
  Or es         -> ppsexpr "or" es
  Ite e1 e2 e3  -> ppsexpr "ite" [e1,e2,e3]
  Implies e1 e2 -> ppsexpr "implies" [e1,e2]
  Eq e1 e2      -> ppsexpr "=" [e1, e2]
  where ppsexpr op es = PP.parens (PP.hsep $ PP.text op : map (ppExpr ppAtom)  es)

instance PP.Pretty TInt where
  pretty = ppTInt

instance PP.Pretty e => PP.Pretty (Formula e) where
  pretty = ppExpr PP.pretty


-- pretty printing of smt commands

ppSetLogic :: String -> PP.Doc
ppSetLogic s = PP.parens (PP.text "set-logic" PP.<+> PP.text s)

ppDeclareFun :: (String, String) -> PP.Doc
ppDeclareFun (v,ty) = PP.parens (PP.text "declare-fun" PP.<+> PP.text v PP.<+> PP.text "()" PP.<+> PP.text ty)

ppAssert :: PP.Doc -> PP.Doc
ppAssert a = PP.parens (PP.text "assert" PP.<+> a)

ppCheckSat :: PP.Doc
ppCheckSat = PP.parens (PP.text "check-sat")


newtype Minismt f = Minismt f


instance PP.Pretty (Minismt (SolverState ( Formula TInt))) where
  pretty (Minismt st) =
    ppSetLogic (format st)
    PP.<$> PP.vcat (map ppDeclareFun allvars)
    PP.<$> PP.vcat (map (ppAssert . PP.pretty) (reverse $ asserts st))
    PP.<$> ppCheckSat
    PP.<$> PP.empty
    where allvars = S.toList $ foldl (\s -> S.union s . vars) S.empty (asserts st)


-- | Minismt solver. Constructs the problem from 'SolverState'.
minismt :: Solver (SolverState (Formula TInt))
minismt st = do
  let input = show $ PP.pretty (Minismt st)
  writeFile "/tmp/fm.smt2" input
  (code , stdout, stderr) <- readProcessWithExitCode "minismt" ["-m","-v2"] input
  return $ case code of
    ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"
    ExitSuccess   -> case lines stdout of
      "sat"   : xs      -> Sat . M.fromList $ map parse xs
      "unsat" : _       -> Unsat
      "unknown" : _     -> Unknown
      "parse error" : _ -> Error "minismt: parse error"
      _                 -> Error "some error"
  where
    parse line = (var, read (tail val)::Value)
      where (var,val) = break (== '=') $ filter (/=' ') line


-- yices 2 for smtlibv2
--yices :: Solver
--yices input = do
  --(code , stdout, stderr) <- readProcessWithExitCode "yices" ["-in","-smt2"] input
  --return $ case lines stdout of
    --"sat"   : xs -> Sat $ M.empty
    --"unsat" : xs -> Unsat
    --_            -> Unknown

-- z3 does not know nat
--z3 :: Solver
--z3 input = do
  --(code , stdout, stderr) <- readProcessWithExitCode "z3" ["-in","-smt2"] input
  --return $ case lines stdout of
    --"sat"   : xs -> Sat $ M.empty
    --"unsat" : xs -> Unsat
    --_            -> Unknown

