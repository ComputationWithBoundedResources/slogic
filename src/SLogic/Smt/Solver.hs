module SLogic.Smt.Solver where

import qualified Data.Set as S
import System.Process
import System.Exit
import qualified Data.Map.Strict as M
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import SLogic.Solver
import SLogic.Smt.SmtM
import SLogic.Logic.Core
import SLogic.Logic.Int

type Var = String

class Universe a where
  unia :: a -> [a]

class BiUniverse a b where
  unib :: a -> [b]

instance Universe IExpr where
  unia (Neg e)  = [e]
  unia (Add es) = es
  unia (Mul es) = es
  unia _        = []

instance BiUniverse IAtom IExpr where
  unib (Lt e1 e2)  = [e1,e2]
  unib (Lte e1 e2) = [e1,e2]
  unib (Gte e1 e2) = [e1,e2]
  unib (Gt e1 e2)  = [e1,e2]
  unib (IExpr e1)  = [e1]

instance Universe (Expr e) where
  unia (Not e)         = [e]
  unia (And es)        = es
  unia (Or es)         = es
  unia (Ite e1 e2 e3)  = [e1,e2,e3]
  unia (Implies e1 e2) = [e1,e2]
  unia (Eq e1 e2)      = [e1,e2]
  unia _               = []

class Vars a where
  vars :: a -> S.Set (String, String)

instance Vars IExpr where
  vars (IVar v ty) = S.singleton (v,ty)
  vars e = foldl S.union S.empty (map vars $ unia e)

instance Vars IAtom where
  vars e = foldl S.union S.empty (map vars (unib e :: [IExpr]))

instance Vars e => Vars (Expr e) where
  vars (Atom e) = vars e
  vars e = foldl S.union S.empty (map vars $ unia e)

--ppSExpr :: PP.Doc -> [PP.Doc] -> PP.Doc
--ppSExpr op es = PP.parens (PP.hsep $ op :es)

ppIExpr :: IExpr-> PP.Doc
ppIExpr e = case e of
  IVar v _ -> PP.text v
  IVal i -> PP.int i
  Neg e1 -> ppsexpr "-"  [e1]
  Add es -> ppsexpr "+"  es
  Mul es -> ppsexpr "*"  es
  where ppsexpr op es = PP.parens (PP.hsep $ PP.text op : map ppIExpr es)

ppIAtom :: IAtom -> PP.Doc
ppIAtom e = case e of
  IExpr e1  -> ppIExpr e1
  Lt e1 e2  -> ppbin "<" e1 e2
  Lte e1 e2 -> ppbin "=<" e1 e2
  Gte e1 e2 -> ppbin ">=" e1 e2
  Gt e1 e2  -> ppbin ">" e1 e2
  where ppbin op e1 e2 = PP.parens (PP.text op PP.<+> ppIExpr e1 PP.<+> ppIExpr e2)

ppExpr :: (e -> PP.Doc) -> Expr e -> PP.Doc
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

instance PP.Pretty IAtom where
  pretty = ppIAtom

instance PP.Pretty e => PP.Pretty (Expr e) where
  pretty = ppExpr PP.pretty

ppSetLogic :: String -> PP.Doc
ppSetLogic s = PP.parens (PP.text "set-logic" PP.<+> PP.text s)

ppDeclareFun :: (String, String) -> PP.Doc
ppDeclareFun (v,ty) = PP.parens (PP.text "declare-fun" PP.<+> PP.text v PP.<+> PP.text "()" PP.<+> PP.text ty)

ppAssert :: PP.Doc -> PP.Doc
ppAssert a = PP.parens (PP.text "assert" PP.<+> a)

ppCheckSat :: PP.Doc
ppCheckSat = PP.parens (PP.text "check-sat")


newtype Minismt e = Minismt (SmtState e)

instance (Vars e, PP.Pretty e) => PP.Pretty (Minismt e) where
  pretty (Minismt st) = 
    ppSetLogic (logic st)
    PP.<$> PP.vcat (map ppDeclareFun allvars)
    PP.<$> PP.vcat (map (ppAssert . PP.pretty) (asserts st))
    PP.<$> ppCheckSat
    where allvars = S.toList $ foldl (\s -> S.union s . vars) S.empty (asserts st)


minismt :: (Vars e, PP.Pretty e) => Solver (SmtState e)
minismt st = do
  let input = show $ PP.pretty (Minismt st)
  (code , stdout, stderr) <- readProcessWithExitCode "minismt" ["-m","-v2"] input
  writeFile "/tmp/fm.smt2" input
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


