{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE TypeFamilies       #-}
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
import           SLogic.Logic.Logic

-- MS: Optimisations?
-- * make flat formulas
--   * capture some simple cases (nested add).., or
--   * rewrite/simplify formula
-- * or is it actually better to have Add a b ? and provide a context in SMT.solver to obtain a flat structure?
-- *
-- * provide fresh counter vor bool and int; so we do not have to compute variables; then the problem may has unused
-- variables 
-- * specialise and pack fresh counter; for the beginning provide BUVar v; BFVar Int;


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

  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Integer Expressions.
data IExpr v
  = IVar v
  | IVal Int

  | ISub [IExpr v]
  | IAdd [IExpr v]
  | IMul [IExpr v]

  | IIte (Formula v) (IExpr v) (IExpr v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)


-- instance Num (IExpr w) where
--   fromInteger = IVal . fromIntegral
--   a + b       = IAdd [a,b]
--   a * b       = IMul [a,b]
--   negate a    = ISub [a]
--   abs a       = IIte (a `IGte` IVal 0) a (negate a)
--   signum a    = IIte (a `IEq` IVal 0) (IVal 0) (IIte (a `IGt` IVal 0) (IVal 1) (negate $ IVal 1 ))


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



--- * Boolean --------------------------------------------------------------------------------------------------------

instance Boolean (Formula v) where
  a .&& b    = And [a,b]
  a .|| b    = Or  [a,b]
  bnot       = Not
  top        = BVal True
  bot        = BVal False
  (.=>)      = Implies
  bigAnd fs  = case F.toList fs of { [] -> BVal True;  xs -> And xs }
  -- MS: bigOr == foldr (.||) bot; should the empty case really return False
  bigOr fs   = case F.toList fs of { [] -> BVal False; xs -> Or  xs }
  ball f     = bigAnd . fmap f . F.toList
  bany f     = bigOr  . fmap f . F.toList

-- | Returns a Boolean variable with the given id.
bvar :: v -> Formula v
bvar = BVar

-- | Returns a Boolean value.
bool :: Bool -> Formula v
bool True = BVal True
bool _    = BVal False



--- * Arithmetic -----------------------------------------------------------------------------------------------------


ivar :: v -> IExpr v
ivar = IVar

num :: Int -> IExpr v
num = IVal

instance AAdditive (IExpr v) where
  a .+ b = IAdd [a,b]
  zero   = IVal 0
  bigAdd = IAdd . F.toList

instance AAdditiveGroup (IExpr v) where
  neg a  = ISub [a]
  a .- b = ISub [a,b]

instance MMultiplicative (IExpr v) where
  a .* b = IMul [a,b]
  one    = IVal 1
  bigMul = IMul . F.toList

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

