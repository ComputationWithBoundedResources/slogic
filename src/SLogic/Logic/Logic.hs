{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies    #-}
module SLogic.Logic.Logic where

import qualified Data.Foldable as F (toList)

--- * boolean --------------------------------------------------------------------------------------------------------

infixr 3 .&&
infixr 2 .||
infixr 1 .=>
infixr 1 .<=>

-- | Abstract Boolean class.
class Boolean a where
  (.&&)  :: a -> a -> a
  (.||)  :: a -> a -> a
  bnot   :: a -> a
  top    :: a
  bot    :: a
  (.=>)  :: a -> a -> a
  (.<=>) :: a -> a -> a
  bigAnd :: Foldable f => f a -> a
  bigOr  :: Foldable f => f a -> a
  ball   :: Foldable f => (e -> a) -> f e -> a
  bany   :: Foldable f => (e -> a) -> f e -> a

  a .=> b   = (bnot a) .|| b
  a .<=> b  = (a .=> b) .&& (b .=> a)
  bigAnd    = foldr (.&&) top
  bigOr     = foldr (.||) bot

  ball f   = foldr (\ x frm -> f x .&& frm) top
  bany f   = foldr (\ x frm -> f x .|| frm) bot

  -- ite :: a -> a -> a -> a
  -- ite g t e = (g .=> t) && (not g --> e)

  -- maj :: a -> a -> a -> a
  -- maj a b c = (a || b) && (a || c) && (b || c)

  -- odd3 :: a -> a -> a -> a
  -- odd3 a b c = a <-> b <-> c

-- newtype Exist b = Exist { unExist :: b }

-- instance Boolean b => Monoid (Exist b) where
--   mempty                       = Exist bot
--   (Exist a) `mappend` (Exist b) = Exist (a .|| b)

-- newtype Forall b = Forall { unForall :: b }

-- instance Boolean b => Monoid (Forall b) where
--   mempty                          = Forall top
--   (Forall a) `mappend` (Forall b) = Forall (a .&& b)

instance Boolean Bool where
  (.&&) = (&&)
  (.||) = (||)
  bnot  = not
  top   = True
  bot   = False

--- * semiring -------------------------------------------------------------------------------------------------------

infixl 7 .*
infixl 6 .+, .-

class AAdditive a where
  (.+)   :: a -> a -> a
  zero   :: a
  bigAdd :: Foldable f => f a -> a

  bigAdd = foldr (.+) zero

class AAdditive a => AAdditiveGroup a where
  neg    :: a -> a
  (.-)   :: a -> a -> a
  bigSub :: Foldable f => f a -> a

  (.-) a b  = a .+ neg b
  bigSub xs = case F.toList xs of
    []     -> zero
    (a:bs) -> a .- bigAdd bs

class MMultiplicative a where
  (.*)   :: a -> a -> a
  one    :: a
  bigMul :: Foldable f => f a -> a

  bigMul = foldr (.*) one

type SSemiRing a = (AAdditive a,      MMultiplicative a)
type RRing  a    = (AAdditiveGroup a, MMultiplicative a)

instance AAdditive Int where
  (.+) = (+)
  zero = 0

instance AAdditiveGroup Int where
  neg  = negate
  (.-) = (-)

instance MMultiplicative Int where
  (.*) = (*)
  one  = 1


--- * ordering -------------------------------------------------------------------------------------------------------

infix 4 .==, ./=
infix 4 .<, .<=, .>=, .>

class Equal a where
  type B a :: *
  (.==), (./=) :: Boolean (B a) => a -> a -> (B a)
  x .== y = bnot $ x ./= y
  x ./= y = bnot $ x .== y

class Equal a => Ite a where
  ite :: Boolean (B a) => (B a) -> a -> a -> a

class Equal a => Order a where
  (.<), (.<=), (.>=), (.>) :: Boolean (B a) => a -> a -> (B a)
  x .> y  = (x .>= y) .&& bnot (x .== y)
  x .< y  = y .> x
  x .>= y = y .<= x
  x .<= y = y .>= x

instance Equal Int where
  type B Int = Bool
  (.==) = (==)
  (./=) = (/=)

instance Equal Bool where
  type B Bool = Bool
  (.==) = (==)
  (./=) = (/=)

instance Order Int where
  (.>)  = (>)
  (.<)  = (<)
  (.>=) = (>=)
  (.<=) = (<=)

instance Ite Int where
  ite b a1 a2 = if b then a1 else a2


--- * monadic interface ----------------------------------------------------------------------------------------------



-- zeroM, oneM, noneM :: Monad m => m (IExpr v)
-- zeroM = return zero
-- oneM  = return one
-- noneM = return none

-- negM :: SemiRing r => Monad m => m r -> m r
-- negM = fmap neg

-- mulM, addM, subM :: Monad m => m (IExpr v) -> m (IExpr v) -> m (IExpr v)
-- mulM = liftM2 (.*)
-- addM = liftM2 (.+)
-- subM = liftM2 (.-)

-- bigMulM, bigAddM :: Monad m => [m (IExpr v)] -> m (IExpr v)
-- bigMulM es = bigMul  `liftM` sequence es
-- bigAddM es = bigAdd  `liftM` sequence es

-- bigMulM', bigAddM' :: Monad m => [m (IExpr v)] -> m (IExpr v)
-- bigMulM' es = bigMul' `liftM` sequence es
-- bigAddM' es = bigAdd' `liftM` sequence es

-- eqM,neqM :: Monad m => m (IExpr v) -> m (IExpr v)-> m (Formula v)
-- eqM  = liftM2 eq
-- neqM = liftM2 neq

-- ltM, lteM, gteM, gtM :: Monad m => m (IExpr v) -> m (IExpr v) -> m (Formula v)
-- ltM  = liftM2 lt
-- lteM = liftM2 lte
-- gteM = liftM2 gte
-- gtM  = liftM2 gt

-- iteM :: Monad m => m (Formula v) -> m (IExpr v) -> m (IExpr v) -> m (IExpr v)
-- iteM = liftM3 IIte

