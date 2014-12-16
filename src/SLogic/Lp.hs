module SLogic.Lp where


import Data.Generics.Uniplate.Direct

import SLogic.Logic.Int


normalise :: IExpr -> IExpr
normalise = rewrite (k . simplify)
  where
    k (Mul (Add e1 e2) e3) = Just $ Add (Mul e1 e3)  (Mul e2 e3)
    k (Mul e3 (Add e1 e2)) = Just $ Add (Mul e3 e1)  (Mul e3 e2)
    k _                    = Nothing

