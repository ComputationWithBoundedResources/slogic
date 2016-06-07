{-# LANGUAGE ConstraintKinds, DeriveFoldable, DeriveFunctor, DeriveTraversable, TypeFamilies #-}
-- | This module provides the the type for (SMT)-Formula.
module SLogic.Logic.Formula where


import           Control.Monad
import           Control.Monad.Reader
import qualified Data.Set             as S

import           SLogic.Data.Decode
import           SLogic.Data.Result
import           SLogic.Data.Solver
import           SLogic.Logic.Logic


-- TODO: MS: optimise; differentiate between user vars and generated vars or use just generated vars

-- | Formula. SMT Core + Int.
data Formula v
  = BVar v
  | Top
  | Bot

  | Not (Formula v)

  | And (Formula v) (Formula v)
  | Or  (Formula v) (Formula v)

  | Implies (Formula v) (Formula v)

  -- atomic integer arithmetic constraints
  | IEq  (IExpr v) (IExpr v)
  | IGt  (IExpr v) (IExpr v)
  | IGte (IExpr v) (IExpr v)

  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Integer Expressions.
data IExpr v
  = IVar v
  | IVal {-# UNPACK #-}!Int

  | INeg (IExpr v)
  | IAdd (IExpr v) (IExpr v)
  | IMul (IExpr v) (IExpr v)

  | IIte (Formula v) (IExpr v) (IExpr v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)


type VarType = String

boolType, intType :: VarType
boolType = "Bool"
intType  = "Int"

variables :: Ord v => Formula v -> S.Set (v, VarType)
variables f =  case f of
  BVar v        -> S.singleton (v, boolType)
  Top           -> S.empty
  Bot           -> S.empty
  Not f1        -> variables f1
  And f1 f2     -> variables f1 `S.union` variables f2
  Or f1 f2      -> variables f1 `S.union` variables f2
  Implies f1 f2 -> variables f1 `S.union` variables f2

  IEq e1 e2     -> variables' e1 `S.union` variables' e2
  IGt e1 e2     -> variables' e1 `S.union` variables' e2
  IGte e1 e2    -> variables' e1 `S.union` variables' e2
  where
    variables' :: Ord v => IExpr v -> S.Set (v, VarType)
    variables' e = case e of
      IVar v       -> S.singleton (v,intType)
      IVal _       -> S.empty
      INeg e1      -> variables' e1
      IAdd e1 e2   -> variables' e1 `S.union` variables' e2
      IMul e1 e2   -> variables' e1 `S.union` variables' e2
      IIte b e1 e2 -> variables b `S.union` variables' e1 `S.union` variables' e2



--- * Boolean --------------------------------------------------------------------------------------------------------
-- MS: Optimisations can be important. For matrices we want `0 .* e = 0` and `e .* 0`. This significantly improves the
-- generated formula (when identity/triangular matrices are used). But (`1 .+ a = a`) decreases the performance
-- significantly. So optimisations should be done domain specific. Further when optimisations are used variables may
-- vanish; this should be considered when decoding.
--
-- MS: Note that 'bigAnd [] = Top', and similar for other monoid instances. Whereas `(and )` is an invalid formula
-- according to the SMTv2 standard.

instance Boolean (Formula v) where
  top   = Top
  bot   = Bot
  bnot  = Not
  (.&&) = And
  (.||) = Or
  (.=>) = Implies

-- | Returns a Boolean variable with the given id.
bvar :: v -> Formula v
bvar = BVar

-- | Returns a Boolean value.
bool :: Bool -> Formula v
bool True = Top
bool _    = Bot


-- annihilate :: Formula v -> Formula v
-- annihilate = simplify f g where
--   f f1 = f1
--   g (IMul (IVal 0) _) = IVal 0
--   g (IMul _ (IVal 0)) = IVal 0
--   g e1                = e1

-- simplify :: (Formula v -> Formula v) -> (IExpr v -> IExpr v) -> Formula v -> Formula v
-- simplify f g (Not f1)        = f $! Not (simplify f g f1)
-- simplify f g (And f1 f2)     = f $! And (simplify f g f1) (simplify f g f2)
-- simplify f g (Or  f1 f2)     = f $! Or (simplify f g f1) (simplify f g f2)
-- simplify f g (Implies f1 f2) = f $! Implies (simplify f g f1) (simplify f g f2)
-- simplify f g (IEq e1 e2)     = f $! IEq  (simplify' f g e1) (simplify' f g e2)
-- simplify f g (IGt e1 e2)     = f $! IGt  (simplify' f g e1) (simplify' f g e2)
-- simplify f g (IGte e1 e2)    = f $! IGte (simplify' f g e1) (simplify' f g e2)
-- simplify _ _ f1              = f1

-- simplify' :: (Formula v -> Formula v) -> (IExpr v -> IExpr v) -> IExpr v -> IExpr v
-- simplify' f g (INeg e1)       = g $! INeg (simplify' f g e1)
-- simplify' f g (IAdd e1 e2)    = g $! IAdd (simplify' f g e1) (simplify' f g e2)
-- simplify' f g (IMul e1 e2)    = g $! IMul (simplify' f g e1) (simplify' f g e2)
-- simplify' f g (IIte f1 e1 e2) = g $! IIte (simplify f g f1) (simplify' f g e1) (simplify' f g e2)
-- simplify' _ _ e1              = e1


--- * Arithmetic -----------------------------------------------------------------------------------------------------


ivar :: v -> IExpr v
ivar = IVar

num :: Int -> IExpr v
num = IVal

instance AAdditive (IExpr v) where
  (.+) = IAdd
  zero = IVal 0

instance AAdditiveGroup (IExpr v) where
  neg = INeg

instance MMultiplicative (IExpr v) where
  (.*) = IMul
  one  = IVal 1

instance Equal (IExpr v) where
  type B (IExpr v) = Formula v
  (.==) = IEq

instance Order (IExpr v) where
  (.>)  = IGt
  (.>=) = IGte

instance Ite (IExpr v) where
  ite = IIte


--- * monadic interface ----------------------------------------------------------------------------------------------

bvarM :: Monad m => v -> m (Formula v)
bvarM = return .  bvar

boolM :: Monad m => Bool -> m (Formula v)
boolM = return . bool

topM, botM :: Monad m => m (Formula v)
topM = return top
botM = return bot

bnotM :: Monad m => m (Formula v) -> m (Formula v)
bnotM = fmap bnot

bandM, borM :: Monad m => m (Formula v) -> m (Formula v) -> m (Formula v)
bandM = liftM2 (.&&)
borM  = liftM2 (.||)

bigAndM, bigOrM :: Monad m => [m (Formula v)] -> m (Formula v)
bigAndM es = bigAnd `liftM` sequence es
bigOrM  es = bigOr `liftM` sequence es

impliesM :: Monad m => m (Formula v) -> m (Formula v) -> m (Formula v)
impliesM = liftM2 (.=>)


--- * decoding -------------------------------------------------------------------------------------------------------

-- NOTE: MS:
-- There are situations when a variable is not defined in the mapping.
-- The user asks for a variable which is not used; or a variable is removed by optimisations.
-- We handle this situations using Maybe and a default value (False, 0).

notLiteral :: String
notLiteral = "SLogic.Logic.Formula.decode: not a literal."

wrongArgument :: String
wrongArgument = "SLogic.Logic.Formula.decode: wrong argument number."

-- | standard environment
type Environment v = Reader (Store v)

-- TODO: MS: extend decode st. it decodes Formulas

instance Storing v => Decode (Environment v) (Formula v) (Maybe Bool) where
  decode c = case c of
    Top    -> return (Just True)
    Bot    -> return (Just False)
    BVar v -> get v
    _      -> error notLiteral
    where
      get v = asks $ \m -> case find v m of
        Just (BoolVal b) -> Just b
        Just _           -> error notLiteral
        _                -> Nothing

-- | Defaults to @False@.
instance Storing v => Decode (Environment v) (Formula v) Bool where
  decode c = case c of
    Top    -> return True
    Bot    -> return False
    BVar v -> get v
    _      -> error notLiteral
    where
      get v = asks $ \m -> case find v m of
        Just (BoolVal b) -> b
        Just _           -> error notLiteral
        _                -> False

instance Storing v => Decode (Environment v) (IExpr v) (Maybe Int) where
  decode c = case c of
    IVal i     -> return (Just i)
    IVar v     -> get v
    _          -> error "not a literal"
    where
      get v = asks $ \m -> case find v m of
        Just (IntVal i) -> Just i
        Just _          -> error notLiteral
        _               -> Nothing

-- | Defaults to @0@.
instance Storing v => Decode (Environment v) (IExpr v) Int where
  decode c = case c of
    IVal i        -> return i
    IVar v        -> get v
    IMul e1 e2    -> (*) <$> decode e1 <*> decode e2
    IAdd e1 e2    -> (+) <$> decode e1 <*> decode e2
    INeg e        -> negate <$> decode e
    IIte eb e1 e2 -> do
      b <- decode eb
      if b then decode e1 else decode e2
    where
      get v = asks $ \m -> case find v m of
        Just (IntVal i) -> i
        Just _          -> error notLiteral
        _               -> 0

