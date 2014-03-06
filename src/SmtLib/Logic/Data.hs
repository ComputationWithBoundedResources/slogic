{-# LANGUAGE FlexibleInstances #-}
module SmtLib.Logic.Data where


import qualified SMTLib2 as S

shallow :: String -> S.Expr -> S.Expr -> S.Expr
shallow s e1@(S.App (S.I (S.N s1) []) Nothing es1) e2@(S.App (S.I (S.N s2) []) Nothing es2) = 
  S.App (S.I (S.N s) []) Nothing $ k e1 s1 es1 $ k e2 s2 es2 []
  where k e' s' es' ess = if s' /= s then e':ess else es' ++ ess
shallow s e1 e2 = S.App (S.I (S.N s) []) Nothing [e1,e2]



