minismt :: Solver
minismt input = do
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v1"] input-}
  {-( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v2","-comp", "-simp", "2", "-t", "10"] input-}
  ( code , stdout, stderr ) <- readProcessWithExitCode "minismt" ["-m","-v2"] input
  putStrLn input
  print code
  putStrLn stderr
  putStrLn stdout
  return $ case lines stdout of
    "sat"   : xs -> Sat . M.fromList $ map parse xs
    "unsat" : xs -> Unsat
    _            -> Unknown
  where 
    parse line = (var, read (tail val)::Constant)
      where (var,val) = break (== '=') $ filter (/=' ') line



