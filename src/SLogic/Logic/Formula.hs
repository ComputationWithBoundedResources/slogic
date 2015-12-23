{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, StandaloneDeriving #-}
-- | This module provides the the type for (SMT)-Formula.
module SLogic.Logic.Formula where


import           Control.Monad
import           Control.Monad.Reader
import qualified Data.Foldable        as F
import qualified Data.Set             as S
import qualified Data.Traversable     as T

import           SLogic.Data.Decode
import           SLogic.Data.Result
import           SLogic.Data.Solver


-- NOTE: MS:
-- When paramaterising the Formula type over some theory one has to lift atomic constraints, equality... Probably we
-- only support constraints for integer arithmetic anyway. So we fix the type. If one wants to support another theory,
-- the easiest way is to extend Formula (like for IExpr) (maybe also Value) ond provide a suitably (safe) interface.
-- This is a good compromise between a simple typing and s-expressions used by many other libraries.

-- TODO MS: experiment with simple optimisations
-- flattening IAdd/IMul helped suprisingly alot

-- | Formula. SMT Core + Int.
data Formula v
  = BVar v
  | BVal Bool

  | Not (Formula v)

  | And [Formula v]
  | Or  [Formula v]

  | Implies (Formula v) (Formula v)

  -- atomic integer arithmetic constraints
  | IEq  (IExpr v) (IExpr v)
  | IGt  (IExpr v) (IExpr v)
  | IGte (IExpr v) (IExpr v)

  deriving (Eq, Ord, Show, Functor)

deriving instance F.Foldable Formula
deriving instance T.Traversable Formula

-- | Integer Expressions.
data IExpr v
  = IVar v
  | IVal Int

  | ISub [IExpr v]
  | IAdd [IExpr v]
  | IMul [IExpr v]

  | IIte (Formula v) (IExpr v) (IExpr v)
  deriving (Eq, Ord, Show, Functor)

deriving instance F.Foldable IExpr
deriving instance T.Traversable IExpr

infixr 3 .&&
infixr 2 .||
infixr 1 .=>
infixr 1 .<=>


type VarType = String

boolType, intType :: VarType
boolType = "Bool"
intType  = "Int"

variables :: Ord v => Formula v -> S.Set (v, VarType)
variables f = case f of
  BVar v        -> S.singleton (v, boolType)
  BVal _        -> S.empty
  Not f1        -> variables f1
  And fs        -> S.unions (variables `fmap` fs)
  Or fs         -> S.unions (variables `fmap` fs)
  Implies f1 f2 -> variables f1 `S.union` variables f2

  IEq e1 e2     -> variables' e1 `S.union` variables' e2
  IGt e1 e2     -> variables' e1 `S.union` variables' e2
  IGte e1 e2    -> variables' e1 `S.union` variables' e2
  where
    variables' :: Ord v => IExpr v -> S.Set (v, VarType)
    variables' e = case e of
      IVar v       -> S.singleton (v,intType)
      IVal _       -> S.empty
      ISub es      -> S.unions (variables' `fmap` es)
      IAdd es      -> S.unions (variables' `fmap` es)
      IMul es      -> S.unions (variables' `fmap` es)
      IIte b e1 e2 -> variables b `S.union` variables' e1 `S.union` variables' e2


--- * core -----------------------------------------------------------------------------------------------------------

-- | Returns a Boolean variable with the given id.
bvar :: v -> Formula v
bvar = BVar

-- | Returns a Boolean value.
bool :: Bool -> Formula v
bool True = BVal True
bool _    = BVal False

-- | Top and bottom symbol.
top, bot :: Formula v
top = bool True
bot = bool False

-- | Boolean not.
bnot :: Formula v -> Formula v
bnot = Not

-- | Boolean and; Boolean or.
band, bor :: Formula v -> Formula v -> Formula v
a `band` b = And [a,b]
a `bor`  b = Or [a,b]

-- | Boolean implication.
implies :: Formula v -> Formula v -> Formula v
implies = Implies

-- | List versions of 'band' and 'bor'.
--
-- prop> bigAnd [] == top
-- prop> bigOr []  == bot
bigAnd, bigOr :: F.Foldable t => t (Formula v) -> Formula v
bigAnd = bigAnd' . F.toList where
  bigAnd' [] = top
  bigAnd' es = And es
bigOr  = bigOr' . F.toList where
  bigOr' [] = bot
  bigOr' es = Or es

ball, bany :: (Functor f, F.Foldable f) => (a -> Formula v) -> f a -> Formula v
ball f = bigAnd . fmap f
bany f = bigOr  . fmap f

--- * infix operators ------------------------------------------------------------------------------------------------

-- | Infix versions of 'band' and 'bor'.
(.&&), (.||) :: Formula v -> Formula v -> Formula v
a .&& b = a `band` b
a .|| b = a `bor` b

-- | Infix version of 'implies'.
(.=>) :: Formula v -> Formula v -> Formula v
(.=>) = implies

-- | a .<=> b == a .=> b .&& b .=> a
(.<=>) :: Formula v -> Formula v -> Formula v
(.<=>) a b = implies a b `band` implies b a


--- * monadic interface ----------------------------------------------------------------------------------------------

bvarM :: Monad m => v -> m (Formula v)
bvarM = return .  bvar

boolM :: Monad m => Bool -> m (Formula v)
boolM = return . bool

topM, botM :: Monad m => m (Formula v)
topM = return top
botM = return bot

bnotM :: Monad m => m (Formula v) -> m (Formula v)
bnotM = liftM bnot

bandM, borM :: Monad m => m (Formula v) -> m (Formula v) -> m (Formula v)
bandM = liftM2 band
borM  = liftM2 bor

bigAndM, bigOrM :: Monad m => [m (Formula v)] -> m (Formula v)
bigAndM es = bigAnd `liftM` sequence es
bigOrM  es = bigOr `liftM` sequence es

impliesM :: Monad m => m (Formula v) -> m (Formula v) -> m (Formula v)
impliesM = liftM2 implies


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

instance Storing v => Decode (Environment v) (Formula v) (Maybe Bool) where
  decode c = case c of
    BVal b -> return (Just b)
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
    BVal b  -> return b
    BVar v -> get v
    _      -> error notLiteral
    where
      get v = asks $ \m -> case find v m of
        Just (BoolVal b) -> b
        Just _           -> error notLiteral
        _                -> False

instance Storing v => Decode (Environment v) (IExpr v) (Maybe Int) where
  decode c = case c of
    IVal i -> return (Just i)
    IVar v -> get v
    _      -> error notLiteral
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
    IMul es       -> product <$> T.traverse decode es
    IAdd es       -> sum <$> T.traverse decode es
    ISub []       -> error wrongArgument
    ISub [e]      -> negate <$> decode e
    ISub (e:es)   -> (-) <$> decode e <*> (sum <$> T.traverse decode es)
    IIte eb e1 e2 -> do
      b <- decode eb
      if b then decode e1 else decode e2
    where
      get v = asks $ \m -> case find v m of
        Just (IntVal i) -> i
        Just _          -> error notLiteral
        _               -> 0

