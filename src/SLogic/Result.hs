-- | This module provides the 'Result' type.
module SLogic.Result where

-- | Result Value.
data Value
  = IntVal Int
  | BoolVal Bool
  | Other
  deriving (Eq, Show)

instance Read Value where
  readsPrec _ r = readsBool1 ++ readsBool2  ++ readsInt where
    readsBool1 = [(BoolVal b, "") | (b,_)  <- reads r :: ([(Bool, String)])]
    readsBool2 = [(BoolVal True, "") | ("true", _) <- lex r] ++ [(BoolVal False, "") | ("false", _) <- lex r]
    readsInt   = [(IntVal i, "") | (i,_)  <- reads r :: ([(Int, String)])]

-- | Result of the 'Solver'.
data Result v
  = Sat v
  | Unsat
  | Unknown
  | Error String
  deriving (Eq, Show)

instance Functor Result where
  f `fmap` Sat v     = Sat (f v)
  _ `fmap` Unsat     = Unsat
  _ `fmap` Unknown   = Unknown
  _ `fmap` (Error s) = Error s

