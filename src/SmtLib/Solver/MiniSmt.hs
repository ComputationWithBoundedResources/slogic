module SmtLib.Solver.MiniSmt where


import SmtLib.SMT

import System.Process
import qualified Data.Map as M

import Debug.Trace

type Var = String

minismt :: String -> IO (Maybe (M.Map Var Constant))
minismt input = do
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v1"] input-}
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v2","-comp", "-simp", "2", "-t", "10"] input-}
  ( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v2"] input
  putStrLn input
  print code
  putStrLn stderr
  putStrLn stdout
  case lines stdout of
    "sat" : xs -> return . Just . M.fromList $ map parse xs
    _          -> return Nothing
  where 
    parse line = (var, read (tail val)::Constant)
      where (var,val) = break (== '=') $ filter (/=' ') line


{-instance Decode (Maybe (M.Map Var Constant)) Literal Constant where-}
  {-decode (LBool b) = return CBool-}
  {-decode (LInt i) = return CInt i-}
  {-decode (LVar i) = \m -> M.lookup (show i) m-}
