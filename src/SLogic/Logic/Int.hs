module SLogic.Logic.Int 
  (
  IExpr (..)
  , IAtom (..)

  -- * standard interface
  , ivar, nvar
  , zero, one, int
  , neg
  , scale, mul
  , add, sub
  , bigMul
  , bigAdd

  , lt, lte, gte, gt

  -- * operator interface
  , (.*)
  , (.+), (.-)
  , (.<),(.=<),(.>=),(.>)

  -- * monadic interface
  , ivarM, nvarM
  , zeroM, oneM, intM
  , negM
  , scaleM, mulM
  , addM, subM
  , bigMulM
  , bigAddM

  , ltM, lteM, gteM, gtM
  ) where


import Control.Monad

import SLogic.Logic.Core

data IExpr
  = IVar Var String
  | IVal Int
  | Neg IExpr
  | Add [IExpr]
  | Mul [IExpr]
  deriving (Eq, Ord, Show)

data IAtom
  = IExpr IExpr
  | Lt IExpr IExpr
  | Lte IExpr IExpr
  | Gte IExpr IExpr
  | Gt IExpr IExpr
  deriving (Eq, Ord, Show)



ivar, nvar :: Var -> IExpr
ivar v = IVar v "Int"
nvar v = IVar v "Nat"

zero, one :: IExpr
zero = int 0
one  = int 1

int :: Int -> IExpr
int = IVal

neg :: IExpr -> IExpr
neg = Neg

scale :: Int -> IExpr -> IExpr
scale i e = int i .* e

mul, add, sub :: IExpr -> IExpr -> IExpr
a `mul` b
  | a == zero || b == zero = zero
  | a == one = b
  | b == one = a
  | otherwise = bigMul [a,b]
a `add` b 
  | a == zero = b
  | b == zero = a 
  | otherwise = bigAdd [a,b]
a `sub` b = a `add` neg b

bigMul, bigAdd :: [IExpr] -> IExpr
bigMul = Mul
bigAdd = Add

lt, lte, gte, gt :: IExpr -> IExpr -> Expr IAtom
a `lt`  b = Atom (a `Lt` b)
a `lte` b = Atom (a `Lte` b)
a `gte` b = Atom (a `Gte` b)
a `gt`  b = Atom (a `Gt` b)

infixl 7  .*
infixl 6  .+, .-

(.*),(.+),(.-) :: IExpr -> IExpr -> IExpr
a .* b = a `mul` b
a .+ b = a `add` b
a .- b = a `sub` b

infix 4 .=<,.<,.>,.>=

(.<),(.=<),(.>=),(.>) :: IExpr -> IExpr -> Expr IAtom
a .<  b = a `lt` b
a .=< b = a `lte` b
a .>= b = a `gte` b
a .>  b = a `gt` b


-- monadic interface
ivarM, nvarM :: Monad m => Var -> m IExpr
ivarM = return . ivar
nvarM = return . nvar

zeroM, oneM :: Monad m => m IExpr
zeroM = return zero
oneM = return one

intM :: Monad m => Int -> m IExpr
intM = return . int


negM :: Monad m => m IExpr -> m IExpr
negM = liftM neg

scaleM :: Monad m => Int -> m IExpr -> m IExpr
scaleM i e = (int i `mul`) `liftM` e


mulM, addM, subM :: Monad m => m IExpr -> m IExpr -> m IExpr
mulM = liftM2 mul
addM = liftM2 mul
subM = liftM2 mul

bigMulM, bigAddM :: Monad m => [m IExpr] -> m IExpr
bigMulM es = bigMul  `liftM` sequence es
bigAddM es = bigAdd  `liftM` sequence es


ltM, lteM, gteM, gtM :: Monad m => m IExpr -> m IExpr -> m (Expr IAtom)
ltM  = liftM2 lte
lteM = liftM2 lte
gteM = liftM2 lte
gtM  = liftM2 lte


