-- | This module provides constraints over integers.
module SLogic.Logic.IntFormula
  (
  -- * re-export SLogic.Logic.Formula
  module M
  , Formula
  , IExpr

  -- * arithmetic operations and constraints
  , ivar
  , zero, one, none
  , num
  , mul, scale, add, sub, neg
  , bigMul, bigAdd
  , bigMul', bigAdd'
  , eq, neq
  , lt, lte, gte, gt
  , ite

  -- * infix operators
  ,(.*),(.+),(.-)
  ,(.==),(./=)
  ,(.<),(.=<),(.>=),(.>)

  -- * monadic interface
  , ivarM
  , zeroM, oneM, noneM
  , numM
  , mulM, addM, subM, negM, scaleM
  , bigMulM, bigAddM
  , bigMulM', bigAddM'
  , eqM, neqM
  , ltM, lteM, gteM, gtM
  , iteM
  ) where


import Control.Monad

import SLogic.Logic.Formula as M hiding (Formula, IExpr)
import SLogic.Logic.Formula


infix 4 .==,./=
infix 4 .=<,.<,.>,.>=

infixl 7 .*
infixl 6 .+, .-


--- * int ------------------------------------------------------------------------------------------------------------

ivar :: v -> IExpr v
ivar = IVar

zero, one, none :: IExpr v
zero = num 0
one  = num 1
none = neg one

num :: Int -> IExpr v
num i = if i < 0 then neg (IVal (-i)) else IVal i

mul, add, sub :: IExpr v -> IExpr v -> IExpr v
mul a b = IMul (k a ++ k b)
  where
    k (IMul es) = es
    k e        = [e]
add a b = IAdd (k a ++ k b)
  where
    k (IAdd es) = es
    k e        = [e]
sub a b = ISub [a,b]


neg :: IExpr v -> IExpr v
neg e = ISub [e]

scale :: Int -> IExpr v -> IExpr v
scale i e = num i `mul` e

-- | List version of 'mul' and 'add'. The default behaviour for empty lists depends on the background-solver.
-- ie. bigAdd [] translates to (* ) for smt, which is an invalid expression. Defaulting this to @0@ may lead for
-- unexpected results.
--
-- prop> bigMul [] = Mul []
bigMul, bigAdd :: [IExpr v] -> IExpr v
bigMul [] = IMul []
bigMul es = foldl1 mul es
bigAdd [] = IAdd []
bigAdd es = foldl1 add es

-- | Like 'bigMul' and 'bigAdd' but with defaulting behaviour.
--
-- prop> bigMul' [] = one
-- prop> bigAdd' [] = zero
bigMul', bigAdd' :: [IExpr v] -> IExpr v
bigMul' [] = one
bigMul' es = bigMul es
bigAdd' [] = zero
bigAdd' es = bigAdd es

eq, neq :: IExpr v -> IExpr v -> Formula v
eq        = IEq
a `neq` b = bnot (a `eq` b)

lt, lte, gte, gt :: IExpr v -> IExpr v -> Formula v
a `lt`  b = IGt b a
a `lte` b = IGte b a
a `gte` b = IGte a b
a `gt`  b = IGt a b

ite :: Formula v -> IExpr v -> IExpr v -> IExpr v
ite = IIte


--- * infix operator -------------------------------------------------------------------------------------------------

(.*),(.+),(.-) :: IExpr v -> IExpr v -> IExpr v
a .* b = a `mul` b
a .+ b = a `add` b
a .- b = a `sub` b

(.==),(./=) :: IExpr v -> IExpr v -> Formula v
(.==) = eq
(./=) = neq

(.<),(.=<),(.>=),(.>) :: IExpr v -> IExpr v -> Formula v
a .<  b = a `lt` b
a .=< b = a `lte` b
a .>= b = a `gte` b
a .>  b = a `gt` b


--- * monadic interface ----------------------------------------------------------------------------------------------

ivarM :: Monad m => v -> m (IExpr v)
ivarM = return . ivar

zeroM, oneM, noneM :: Monad m => m (IExpr v)
zeroM = return zero
oneM  = return one
noneM = return none

numM :: Monad m => Int -> m (IExpr v)
numM = return . num

negM :: Monad m => m (IExpr v) -> m (IExpr v)
negM = liftM neg

scaleM :: Monad m => Int -> m (IExpr v) -> m (IExpr v)
scaleM i e = (num i `mul`) `liftM` e

mulM, addM, subM :: Monad m => m (IExpr v) -> m (IExpr v) -> m (IExpr v)
mulM = liftM2 mul
addM = liftM2 add
subM = liftM2 sub

bigMulM, bigAddM :: Monad m => [m (IExpr v)] -> m (IExpr v)
bigMulM es = bigMul  `liftM` sequence es
bigAddM es = bigAdd  `liftM` sequence es

bigMulM', bigAddM' :: Monad m => [m (IExpr v)] -> m (IExpr v)
bigMulM' es = bigMul' `liftM` sequence es
bigAddM' es = bigAdd' `liftM` sequence es

eqM,neqM :: Monad m => m (IExpr v) -> m (IExpr v)-> m (Formula v)
eqM  = liftM2 eq
neqM = liftM2 neq

ltM, lteM, gteM, gtM :: Monad m => m (IExpr v) -> m (IExpr v) -> m (Formula v)
ltM  = liftM2 lt
lteM = liftM2 lte
gteM = liftM2 gte
gtM  = liftM2 gt

iteM :: Monad m => m (Formula v) -> m (IExpr v) -> m (IExpr v) -> m (IExpr v)
iteM = liftM3 IIte

