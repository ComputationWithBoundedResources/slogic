-- | This module provides constraints over integers.
module SLogic.Logic.IntFormula where
  -- (
  -- -- * re-export SLogic.Logic.Formula
  -- module M
  -- , Formula
  -- , IExpr

  -- -- * arithmetic operations and constraints
  -- , ivar
  -- , zero, one, none
  -- , num
  -- , mul, scale, add, sub, neg
  -- , bigMul, bigAdd
  -- , bigMul', bigAdd'
  -- , eq, neq
  -- , lt, lte, gte, gt
  -- , ite

  -- -- * infix operators
  -- ,(.*),(.+),(.-)
  -- ,(.==),(./=)
  -- ,(.<),(.=<),(.>=),(.>)

  -- -- * monadic interface
  -- , ivarM
  -- , zeroM, oneM, noneM
  -- , numM
  -- , mulM, addM, subM, negM, scaleM
  -- , bigMulM, bigAddM
  -- , bigMulM', bigAddM'
  -- , eqM, neqM
  -- , ltM, lteM, gteM, gtM
  -- , iteM
  -- ) where


import Control.Monad

import SLogic.Logic.Logic
import SLogic.Logic.Formula as M hiding (Formula, IExpr)
import SLogic.Logic.Formula


--- * int ------------------------------------------------------------------------------------------------------------

ivar :: v -> IExpr v
ivar = IVar


-- none = neg one

num :: Int -> IExpr v
num i = if i < 0 then neg (IVal (-i)) else IVal i


-- scale :: Int -> IExpr v -> IExpr v
-- scale i e = num i .* e


ite :: Formula v -> IExpr v -> IExpr v -> IExpr v
ite = IIte


--- * infix operator -------------------------------------------------------------------------------------------------


--- * monadic interface ----------------------------------------------------------------------------------------------

-- ivarM :: Monad m => v -> m (IExpr v)
-- ivarM = return . ivar

-- zeroM, oneM, noneM :: Monad m => m (IExpr v)
-- zeroM = return zero
-- oneM  = return one
-- noneM = return none

-- numM :: Monad m => Int -> m (IExpr v)
-- numM = return . num

-- negM :: Monad m => m (IExpr v) -> m (IExpr v)
-- negM = fmap neg

-- scaleM :: Monad m => Int -> m (IExpr v) -> m (IExpr v)
-- scaleM i e = (num i `mul`) `liftM` e

-- mulM, addM, subM :: Monad m => m (IExpr v) -> m (IExpr v) -> m (IExpr v)
-- mulM = liftM2 mul
-- addM = liftM2 add
-- subM = liftM2 sub

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

