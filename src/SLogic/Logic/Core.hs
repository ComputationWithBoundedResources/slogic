-- | This module provides the logical core.
module SLogic.Logic.Core
  (
  Formula (..)
  , Var, strVar, varStr
  , VType, strVType, vtypeStr
  , Vars (..)
  , LEq (..)

  -- * standard interface
  , bvar
  , bool, top, bot
  , bnot
  , eq, neq
  , band, bor, bigAnd, bigOr
  , implies, ite

  -- * operator interface
  , (.==),(./=)
  , (.&&), (.||)
  , (.==>)

  -- * monadic interface
  , bvarM
  , boolM, topM, botM
  , bnotM
  , eqM, neqM
  , bandM, borM, bigAndM, bigOrM
  , impliesM, iteM

  -- * decoding environment
  , Environment
  ) where


import qualified Data.Foldable as F
import qualified Data.ByteString.Char8 as BS
import           Control.Monad
import           Control.Monad.Reader
import           Data.Generics.Uniplate.Direct
import qualified Data.Map.Strict               as M
import           Data.Maybe                    (fromMaybe)
import qualified Data.Set                      as S

import           SLogic.Decode
import           SLogic.Result


-- | Variable type.
type Var = BS.ByteString
type VType = BS.ByteString

varStr,vtypeStr :: Var -> String
varStr   = BS.unpack
vtypeStr = BS.unpack

strVar, strVType :: String -> Var
strVar   = BS.pack
strVType = BS.pack

-- | Defines sat formula modulo some theory and equality.
data Formula a
  = Atom a
  | BVar Var
  | BVal Bool
  | Not (Formula a)
  | And [Formula a]
  | Or  [Formula a]
  | Ite (Formula a) (Formula a) (Formula a)
  | Implies (Formula a) (Formula a)
  | Eq (Formula a) (Formula a)
  deriving (Eq, Ord, Show)

instance Uniplate (Formula a) where
  uniplate (Not e)         = plate Not |* e
  uniplate (And es)        = plate And ||* es
  uniplate (Or es)         = plate Or ||* es
  uniplate (Ite e1 e2 e3)  = plate Ite |* e1 |* e2 |* e3
  uniplate (Implies e1 e2) = plate Implies |* e1 |* e2
  uniplate (Eq e1 e2)      = plate Eq |* e1 |* e2
  uniplate  x              = plate x

instance Biplate (Formula a) (Formula a) where
  biplate = plateSelf

instance Uniplate a => Biplate (Formula a) a where
  biplate (Atom a)        = plate Atom |* a
  biplate (Not e)         = plate Not |+ e
  biplate (And es)        = plate And ||+ es
  biplate (Or es)         = plate Or ||+ es
  biplate (Ite e1 e2 e3)  = plate Ite |+ e1 |+ e2 |+ e3
  biplate (Implies e1 e2) = plate Implies |+ e1 |+ e2
  biplate (Eq e1 e2)      = plate Eq |+ e1 |+ e2
  biplate  x              = plate x

class Vars e where
  vars :: e -> S.Set (Var, VType)

instance Vars e => Vars (Formula e) where
  vars e = bvs `S.union` evs
   where
     evs = S.unions   [ vars a      | Atom a <- es ]
     bvs = S.fromList [ (v, BS.pack "Bool")  | BVar v <- es ]
     es = universe e

-- | Equality itself is considered as Formula.
-- 'LEq' is used to lift equality between theory expressions.
class LEq a e where
  leq :: a -> a -> Formula e

-- | Returns a Boolean variable with the given id.
bvar :: String -> Formula a
bvar = BVar . strVar

-- | Returns a Boolean value.
bool :: Bool -> Formula a
bool = BVal

-- | Top and bottom symbol.
top, bot :: Formula a
top = bool True
bot = bool False

-- | Boolean not.
bnot :: Formula a -> Formula a
bnot = Not

-- | Boolean and; Boolean or.
band, bor :: Formula a -> Formula a -> Formula a
a `band` b = And [a,b]
a `bor`  b = Or [a,b]

-- | List versions of 'band' and 'bor'.
--
-- prop> bigAnd [] = top
-- prop> bigOr []  = bot
bigAnd, bigOr :: F.Foldable t => t (Formula a) -> Formula a
bigAnd = bigAnd' . F.toList where
  bigAnd' [] = top
  bigAnd' es = And es
bigOr  = bigOr' . F.toList where
  bigOr' [] = top
  bigOr' es = Or es

-- | Boolean implication.
implies :: Formula a -> Formula a -> Formula a
implies = Implies

-- | If then else.
ite :: Formula a -> Formula a -> Formula a -> Formula a
ite = Ite

instance LEq (Formula e) e where
  leq = Eq

-- | Equality.
eq :: (LEq e1 e) => e1 -> e1 -> Formula e
eq = leq

-- | prop> a `neq` b = bnot (a `eq` b)
neq :: (LEq e1 e) => e1 -> e1 -> Formula e
a `neq` b = bnot (a `eq` b)

infix 4 .==,./=
infixr 3 .&&
infixr 2 .||
infixr 1 .==>

-- | Infix versions of 'band' and 'bor'.
(.&&), (.||) :: Formula a -> Formula a -> Formula a
a .&& b = a `band` b
a .|| b = a `bor` b

-- | Infix version of 'implies'.
(.==>) :: Formula a -> Formula a -> Formula a
(.==>) = implies

-- | Infix versions of equality and diseuqlity.
(.==),(./=) :: (LEq e1 e) => e1 -> e1 -> Formula e
(.==) = eq
(./=) = neq


-- * monadic interface
bvarM :: Monad m => String -> m (Formula a)
bvarM = return .  bvar

boolM :: Monad m => Bool -> m (Formula a)
boolM = return . bool

topM, botM :: Monad m => m (Formula a)
topM = return top
botM = return bot

bnotM :: Monad m => m (Formula a) -> m (Formula a)
bnotM = liftM bnot

bandM, borM :: Monad m => m (Formula a) -> m (Formula a) -> m (Formula a)
bandM = liftM2 band
borM  = liftM2 bor

bigAndM, bigOrM :: Monad m => [m (Formula a)] -> m (Formula a)
bigAndM es = bigAnd `liftM` sequence es
bigOrM  es = bigOr `liftM` sequence es

impliesM :: Monad m => m (Formula a) -> m (Formula a) -> m (Formula a)
impliesM = liftM2 implies

iteM :: Monad m => m (Formula a) -> m (Formula a) -> m (Formula a) -> m (Formula a)
iteM = liftM3 ite

eqM,neqM :: (Monad m, LEq e1 e) => m e1 -> m e1 -> m (Formula e)
eqM  = liftM2 eq
neqM = liftM2 neq


-- * decoding

fromValue :: Value -> Bool
fromValue (BoolVal b) = b
fromValue _ = error "SmtLib.Logic.Int.decode.fromValue: not an BoolVal."

notFound :: String -> String
notFound v = "SmtLib.Logic.Core.decode.asks: variable " ++ v ++" not found."

notLiteral :: String
notLiteral = "SmtLib.Logic.Core.decode: not a literal."

-- | standard environment
type Environment = Reader (M.Map Var Value)

instance Decode Environment e Value => Decode Environment (Formula e) Value where
  decode c = case c of
    Atom a -> decode a
    BVal b -> return (BoolVal b)
    BVar v -> get v
    _      -> return Other
    where get v = asks $ \m -> Other `fromMaybe` M.lookup v  m

instance Decode Environment (Formula e) Bool where
  decode c = case c of
    BVal b -> return b
    BVar v -> get v
    _      -> error notLiteral
    where get v = asks $ \m -> maybe (error . notFound $ varStr v) fromValue (M.lookup v m)

instance Decode Environment (Formula e) (Maybe Bool) where
  decode c = case c of
    BVal b -> return (Just b)
    BVar v -> get v
    _      -> error notLiteral
    where get v = asks $ \m -> liftM fromValue (M.lookup v m)

