module SmtLib.Solver where

import System.Process
import System.Exit
import qualified Data.Map as M

import SmtLib.SMT


type Var = String

minismt :: Solver
minismt input = do
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
    parse line = (var, read (tail val)::Constant)
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

