-- | This module provides constraints over integers.
module SLogic.Logic.Int
  (
  IExpr (..)
  , TInt (..)

  -- * standard interface
  , tInt, ivar, tNat, nvar
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


import           Control.Monad
import           Control.Monad.Reader
import           Data.Generics.Uniplate.Direct
import qualified Data.Map.Strict               as M
import           Data.Maybe                    (fromMaybe)

import           SLogic.Decode
import           SLogic.Logic.Core
import           SLogic.Result


-- | Defines expressions over the integers.
data IExpr
  = IVar Var String -- ^ IVar id type; Type can be chosen; usually "Int" or "Nat"
  | IVal Int
  | Neg IExpr
  | Add [IExpr]
  | Mul [IExpr]
  deriving (Eq, Ord, Show)

instance Uniplate IExpr where
  uniplate (Neg e) = plate Neg |* e
  uniplate (Add es) = plate Add ||* es
  uniplate (Mul es) = plate Add ||* es
  uniplate x        = plate x

instance Biplate IExpr IExpr where
  biplate = plateSelf

-- | Inequality constraints over 'IExpr'.
data TInt
  = IExpr IExpr      -- necessary to lift equality; TODO: use dedicated symbol? together with pretty printing
  | Lt IExpr IExpr
  | Lte IExpr IExpr
  | Gte IExpr IExpr
  | Gt IExpr IExpr
  deriving (Eq, Ord, Show)

instance Uniplate TInt where
  uniplate = plate

instance Biplate TInt IExpr where
  biplate (IExpr e)   = plate IExpr |* e
  biplate (Lt e1 e2)  = plate Lt |* e1 |* e2
  biplate (Lte e1 e2) = plate Lte |* e1 |* e2
  biplate (Gte e1 e2) = plate Gte |* e1 |* e2
  biplate (Gt e1 e2)  = plate Gt |* e1 |* e2

instance LEq IExpr TInt where
  e1 `leq` e2  = Atom (IExpr e1) `Eq` Atom (IExpr e2)

-- | Int type.
tInt :: String
tInt = "Int"

-- | Nat type.
tNat :: String
tNat = "Nat"


-- | Provides integer variables of type 'tInt' and 'tNat'.
ivar, nvar :: Var -> IExpr
ivar v = IVar v tInt
nvar v = IVar v tNat

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

lt, lte, gte, gt :: IExpr -> IExpr -> Formula TInt
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

(.<),(.=<),(.>=),(.>) :: IExpr -> IExpr -> Formula TInt
a .<  b = a `lt` b
a .=< b = a `lte` b
a .>= b = a `gte` b
a .>  b = a `gt` b


-- * monadic interface

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


ltM, lteM, gteM, gtM :: Monad m => m IExpr -> m IExpr -> m (Formula TInt)
ltM  = liftM2 lte
lteM = liftM2 lte
gteM = liftM2 lte
gtM  = liftM2 lte


-- * decoding

fromValue :: Value -> Int
fromValue (IntVal i) = i
fromValue _ = error "SmtLib.Smt.Int.decode.fromValue: not an IntVal."

notFound :: String -> String
notFound v = "SmtLib.Smt.Int.decode.asks: variable " ++ v ++" not found."

notLiteral :: String
notLiteral = "SmtLib.Smt.Int.decode: not a literal."


instance Decode (Reader (M.Map String Value)) IExpr Value where
  decode c = case c of
    IVal i   -> return (IntVal i)
    IVar v _ -> get v
    _        -> return Other
    where get v = asks $ \m -> error (notFound v) `fromMaybe` M.lookup v  m

instance Decode (Reader (M.Map String Value)) TInt Value where
  decode c = case c of
    IExpr e -> decode e
    _       -> err
    where  err = error notLiteral

instance Decode (Reader (M.Map String Value)) IExpr Int where
  decode c = case c of
    IVal i   -> return i
    IVar v _ -> get v
    _        -> error notLiteral
    where get v = asks $ \m -> maybe (error $ notFound v) fromValue (M.lookup v m)

instance Decode (Reader (M.Map String Value)) TInt Int where
  decode c = case c of
    IExpr e -> decode e
    _       -> err
    where  err = error notLiteral

