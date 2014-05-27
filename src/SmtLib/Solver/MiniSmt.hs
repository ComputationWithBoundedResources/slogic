module SmtLib.Solver.MiniSmt where


import SmtLib.SMT

import System.Process
import qualified Data.Map as M

import Debug.Trace

type Var = String

minismt :: Solver
minismt input = do
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v1"] input-}
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v2","-comp", "-simp", "2", "-t", "10"] input-}
  (code , stdout, stderr) <- readProcessWithExitCode "minismt" ["-m","-v2"] input
  --putStrLn input
  --print code
  --writeFile "/tmp/fm.smt2" input
  --putStrLn stderr
  --putStrLn stdout
  return $ case lines stdout of
    "sat"   : xs -> Sat . M.fromList $ map parse xs
    "unsat" : xs -> Unsat
    _            -> Unknown
  where 
    parse line = (var, read (tail val)::Constant)
      where (var,val) = break (== '=') $ filter (/=' ') line

z3 :: Solver
z3 input = do
  (code , stdout, stderr) <- readProcessWithExitCode "z3" ["-in","-smt2"] input
  --putStrLn input
  --print code
  --putStrLn stderr
  --putStrLn stdout
  return $ case lines stdout of
    "sat"   : xs -> Sat $ M.empty
    "unsat" : xs -> Unsat
    _            -> Unknown

