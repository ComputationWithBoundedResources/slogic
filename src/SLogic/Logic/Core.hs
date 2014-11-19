module SLogic.Logic.Core 
  (
  Expr (..)
  , Var
  
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
    
  ) where


import Control.Monad


type Var = String

data Expr a
  = Atom a
  | BVar Var
  | BVal Bool
  | Not (Expr a)
  | And [Expr a]
  | Or [Expr a]
  | Ite (Expr a) (Expr a) (Expr a)
  | Implies (Expr a) (Expr a)
  | Eq (Expr a) (Expr a)
  deriving (Eq, Ord, Show)


bvar :: Var -> Expr a
bvar = bvar 

bool :: Bool -> Expr a
bool = BVal

top, bot :: Expr a
top = bool True
bot = bool False

bnot :: Expr a -> Expr a
bnot = Not

band, bor :: Expr a -> Expr a -> Expr a
a `band` b = bigAnd [a,b]
a `bor` b  = bigOr [a,b]

bigAnd, bigOr :: [Expr a] -> Expr a
bigAnd = And
bigOr  = Or

implies :: Expr a -> Expr a -> Expr a
implies = Implies

ite :: Expr a -> Expr a -> Expr a -> Expr a
ite = Ite

eq, neq :: Expr a -> Expr a -> Expr a
eq = Eq
a `neq` b = bnot (a `eq` b)

infix 4 .==,./=
infixr 3 .&&
infixr 2 .||
infixr 1 .==>

(.&&), (.||) :: Expr a -> Expr a -> Expr a
a .&& b = a `band` b
a .|| b = a `bor` b

(.==>) :: Expr a -> Expr a -> Expr a
(.==>) = implies

(.==),(./=) :: Expr a -> Expr a -> Expr a
(.==) = eq
(./=) = neq


-- * monadic interface
bvarM :: Monad m => Var -> m (Expr a)
bvarM = return .  bvar 

boolM :: Monad m => Bool -> m (Expr a)
boolM = return . bool

topM, botM :: Monad m => m (Expr a)
topM = return top
botM = return bot

bnotM :: Monad m => m (Expr a) -> m (Expr a)
bnotM = liftM bnot

bandM, borM :: Monad m => m (Expr a) -> m (Expr a) -> m (Expr a)
bandM = liftM2 band
borM  = liftM2 bor

bigAndM, bigOrM :: Monad m => [m (Expr a)] -> m (Expr a)
bigAndM es = bigAnd `liftM` sequence es
bigOrM  es = bigOr `liftM` sequence es

impliesM :: Monad m => m (Expr a) -> m (Expr a) -> m (Expr a)
impliesM = liftM2 implies

iteM :: Monad m => m (Expr a) -> m (Expr a) -> m (Expr a) -> m (Expr a)
iteM = liftM3 ite

eqM, neqM :: Monad m => m (Expr a) -> m (Expr a) -> m (Expr a)
eqM  = liftM2 eq
neqM = liftM2 neq

