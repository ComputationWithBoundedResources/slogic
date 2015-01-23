-- | This module provides constraints over integers.
module SLogic.Logic.Int
  (
  IExpr (..)
  , IFormula (..)

  -- * standard interface
  , tInt, ivar, tNat, nvar
  , zero, one, num
  , neg
  , scale, mul
  , add, sub
  , bigMul, bigMul'
  , bigAdd, bigAdd'

  , lt, lte, gte, gt

  -- * operator interface
  , (.*)
  , (.+), (.-)
  , (.<),(.=<),(.>=),(.>)

  -- * monadic interface
  , ivarM, nvarM
  , zeroM, oneM, numM
  , negM
  , scaleM, mulM
  , addM, subM
  , bigMulM, bigMulM'
  , bigAddM, bigAddM'

  , ltM, lteM, gteM, gtM
  ) where


import qualified Data.ByteString.Char8 as BS
import           Control.Monad
import           Control.Monad.Reader
import           Data.Generics.Uniplate.Direct
import qualified Data.Map.Strict               as M
import           Data.Maybe                    (fromMaybe)
import qualified Data.Set as S

import           SLogic.Decode
import           SLogic.Logic.Core
import           SLogic.Result


-- | Defines expressions over the integers.
data IExpr
  = IVar Var VType -- ^ IVar id type; Type can be chosen; usually "Int" or "Nat"
  | IVal Int
  | Neg IExpr
  | Add [IExpr]
  | Mul [IExpr]
  deriving (Eq, Ord, Show)

instance Uniplate IExpr where
  uniplate (Neg e)  = plate Neg |* e
  uniplate (Add es) = plate Add ||* es
  uniplate (Mul es) = plate Mul ||* es
  uniplate x        = plate x

instance Biplate IExpr IExpr where
  biplate = plateSelf

-- | Constraints over 'IExpr'.
data IFormula
  = Lt IExpr IExpr
  | Lte IExpr IExpr
  | IEq IExpr IExpr
  | Gte IExpr IExpr
  | Gt IExpr IExpr
  deriving (Eq, Ord, Show)

instance Uniplate IFormula where
  uniplate = plate

instance Biplate IFormula IExpr where
  biplate (Lt e1 e2)  = plate Lt |* e1 |* e2
  biplate (Lte e1 e2) = plate Lte |* e1 |* e2
  biplate (IEq e1 e2) = plate IEq |* e1 |* e2
  biplate (Gte e1 e2) = plate Gte |* e1 |* e2
  biplate (Gt e1 e2)  = plate Gt |* e1 |* e2

instance Vars IFormula where
  vars e = S.fromList [ (v, ty) | IVar v ty <- universeBi e]

instance LEq IExpr IFormula where
  e1 `leq` e2  = Atom (e1 `IEq` e2)

-- | Integer type.
tInt :: VType
tInt = BS.pack "Int"

-- | Natural type. Nat is not part of the smtlib2-standard but handled internally.
tNat :: VType
tNat = BS.pack "Nat"


-- | Provides integer variables of type 'tInt' and 'tNat'.
ivar, nvar :: String -> IExpr
ivar v = IVar (strVar v) tInt
nvar v = IVar (strVar v) tNat

zero, one, none :: IExpr
zero = num 0
one  = num 1
none = neg one

num :: Int -> IExpr
num i = if i < 0 then neg (IVal (-i)) else IVal i

-- push negations down
neg :: IExpr -> IExpr
neg (Neg e)      = e
neg e            = Neg e

scale :: Int -> IExpr -> IExpr
scale i e = num i `mul` e


-- MS: simplifications should not annihilate expressions; or in particular variables, as variable declarations depend
-- on the expression itself.
mul, add, sub :: IExpr -> IExpr -> IExpr
a `mul` b
  | a == one = b
  | b == one = a
  | a == none = neg b
  | b == none = neg a
  | otherwise = Mul (k a ++ k b)
  where
    k (Mul es) = es
    k e        = [e]
a `add` b 
  | a == zero = b
  | b == zero = a
  | otherwise = Add (k a ++ k b)
  where
    k (Add es) = es
    k e        = [e]
a `sub` b = a `add` neg b

-- | List version of 'mul' and 'add'. The default behaviour for empty lists depends on the background-solver.
-- ie. bigAdd [] translates to (* ) for smt, which is an invalid expression. Defaulting this to @0@ may lead for
-- unexpected results.
-- 
-- prop> bigMul [] = Mul []
bigMul, bigAdd :: [IExpr] -> IExpr
bigMul [] = Mul []
bigMul es = foldl1 mul es
bigAdd [] = Add []
bigAdd es = foldl1 add es

-- | Like 'bigMul' and 'bigAdd' but with defaulting behaviour.
--
-- prop> bigMul' [] = one
-- prop> bigAdd' [] = zero
bigMul', bigAdd' :: [IExpr] -> IExpr
bigMul' [] = one
bigMul' es = bigMul es
bigAdd' [] = zero
bigAdd' es = bigAdd es


lt, lte, gte, gt :: IExpr -> IExpr -> Formula IFormula
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

(.<),(.=<),(.>=),(.>) :: IExpr -> IExpr -> Formula IFormula
a .<  b = a `lt` b
a .=< b = a `lte` b
a .>= b = a `gte` b
a .>  b = a `gt` b


-- * monadic interface

ivarM, nvarM :: Monad m => String -> m IExpr
ivarM = return . ivar
nvarM = return . nvar

zeroM, oneM :: Monad m => m IExpr
zeroM = return zero
oneM = return one

numM :: Monad m => Int -> m IExpr
numM = return . num


negM :: Monad m => m IExpr -> m IExpr
negM = liftM neg

scaleM :: Monad m => Int -> m IExpr -> m IExpr
scaleM i e = (num i `mul`) `liftM` e


mulM, addM, subM :: Monad m => m IExpr -> m IExpr -> m IExpr
mulM = liftM2 mul
addM = liftM2 add
subM = liftM2 sub

bigMulM, bigAddM :: Monad m => [m IExpr] -> m IExpr
bigMulM es = bigMul  `liftM` sequence es
bigAddM es = bigAdd  `liftM` sequence es

bigMulM', bigAddM' :: Monad m => [m IExpr] -> m IExpr
bigMulM' es = bigMul' `liftM` sequence es
bigAddM' es = bigAdd' `liftM` sequence es


ltM, lteM, gteM, gtM :: Monad m => m IExpr -> m IExpr -> m (Formula IFormula)
ltM  = liftM2 lt
lteM = liftM2 lte
gteM = liftM2 gte
gtM  = liftM2 gt


-- * decoding

fromValue :: Value -> Int
fromValue (IntVal i) = i
fromValue _ = error "SmtLib.Smt.Int.decode.fromValue: not an IntVal."

notFound :: String -> String
notFound v = "SmtLib.Smt.Int.decode.asks: variable " ++ v ++" not found."

notLiteral :: String
notLiteral = "SmtLib.Smt.Int.decode: not a literal."

instance Decode Environment IExpr (Maybe Value) where
  decode c = case c of
    IVal i   -> return (Just (IntVal i))
    IVar v _ -> get v
    _        -> return (Just Other)
    where get v = asks $ \m -> M.lookup v  m

instance Decode Environment IExpr (Maybe Int) where
  decode c = case c of
    IVal i   -> return (Just i)
    IVar v _ -> get v
    _        -> error notLiteral
    where get v = asks $ \m -> liftM fromValue (M.lookup v m)

instance Decode Environment IExpr Value where
  decode c = case c of
    IVal i   -> return (IntVal i)
    IVar v _ -> get v
    _        -> return Other
    where get v = asks $ \m -> error (notFound $ varStr v) `fromMaybe` M.lookup v  m

instance Decode Environment IExpr Int where
  decode c = case c of
    IVal i   -> return i
    IVar v _ -> get v
    _        -> error notLiteral
    where get v = asks $ \m -> maybe (error . notFound $ varStr v) fromValue (M.lookup v m)

