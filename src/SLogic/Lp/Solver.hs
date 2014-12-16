{-# LANGUAGE ScopedTypeVariables #-}
-- | This module provides 'Solver' implementations for LP.

{-

example:



-x1 -x2;
x1 >= 1;
x2 >= 1;
x1 + x2 >= 2;
int x1;

Value of objective function: -2

Actual values of the variables:
x1                              1
x2                              1
-}

module SLogic.Lp.Solver
  (
  lpSolve
  , lpSolve'
  ) where

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


-- default pretty printing
ppIExpr :: IExpr-> PP.Doc
ppIExpr e = case e of
  IVar v _ -> PP.text v
  IVal i -> PP.int i
  Neg e1 -> PP.text "-" PP.<> ppIExpr e1
  Add e1 e2 -> ppIExpr e1 PP.<+> ppIExpr e2
  Mul e1 e2 -> ppIExpr e1 PP.<+> ppIExpr e2

ppTInt :: TInt -> PP.Doc
ppTInt e = case e of
  IExpr e1  -> ppIExpr e1
  Lt e1 e2  -> ppbin "<" e1 e2
  Lte e1 e2 -> ppbin "<=" e1 e2
  Gte e1 e2 -> ppbin ">=" e1 e2
  Gt e1 e2  -> ppbin ">" e1 e2
  where ppbin op e1 e2 = ppIExpr e1 PP.<+> PP.text op PP.<+> ppIExpr e2

instance PP.Pretty TInt where
  pretty = ppTInt

-- pretty printing of smt commands


newtype LpSolve f = LpSolve f

ppAssert = undefined

instance PP.Pretty (LpSolve (SolverState  TInt)) where
  pretty (LpSolve st) =
    PP.vcat (map (ppAssert . PP.pretty) (reverse $ asserts st))
    PP.<$> PP.empty


-- | Default minismt solver.
lpSolve :: Solver (SolverState TInt)
lpSolve = lpSolve' []

-- | Minismt solver. Constructs the problem from 'SolverState'.
lpSolve' :: [String] -> Solver (SolverState TInt)
lpSolve' args st = undefined
  {-let input = show $ PP.pretty (LpSolve st)-}
  {-writeFile "/tmp/fm.smt2" input-}
  {-(code , stdout, stderr) <- readProcessWithExitCode "minismt" args input-}
  {-return $ case code of-}
    {-ExitFailure i -> Error $ "Error(" ++ show i ++ "," ++ show stderr ++ ")"-}
    {-ExitSuccess   -> case lines stdout of-}
      {-("Value of the objective function":cs)   : ls      -> Sat . M.fromList $ map parse xs-}
      {-"unsat" : _       -> Unsat-}
      {-"unknown" : _     -> Unknown-}
      {-"parse error" : _ -> Error "minismt: parse error"-}
      {-_                 -> Error "some error"-}
  {-where-}
    {-parse line = (var, read (tail val)::Value)-}
      {-where (var,val) = break (== '=') $ filter (/=' ') line-}


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

