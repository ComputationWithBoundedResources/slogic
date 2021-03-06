{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, TypeFamilies, DataKinds, ScopedTypeVariables #-}
-- | Simple and unsafe matrix module
-- 
-- a rip-off of the matrix package (https://hackage.haskell.org/package/matrix)
module SLogic.Logic.Matrix
  where

import           Control.Monad       (forM_)
import qualified Data.List           as L (splitAt, transpose)
import           Data.Monoid         ((<>))
import qualified Data.Vector         as V
import qualified Data.Vector.Mutable as MV
import           SLogic.Logic.Logic
import SLogic.Logic.Formula

-- import Data.Proxy
-- import GHC.TypeLits

-- data MMatrix (m :: Nat) (n :: Nat) k = MM (V.Vector k) deriving Show

-- pplus :: MMatrix m n k -> MMatrix m n k -> MMatrix m n k
-- pplus = undefined

-- mmul :: MMatrix m n k -> MMatrix n o k -> MMatrix m o k
-- mmul = undefined

-- generate :: forall m n k. (KnownNat m, KnownNat n) => (Int -> k) -> MMatrix m n k
-- generate f = MM (V.generate (m*n) f) where
--     m = fromInteger (natVal (Proxy :: Proxy m))
--     n = fromInteger (natVal (Proxy :: Proxy n))


-- unit' :: forall m n a. (KnownNat m, KnownNat n, AAdditive a) => MMatrix m n a
-- unit' = MM (V.generate n (const zero))
--   where n = fromInteger (natVal (Proxy :: Proxy n))

-- ab :: Integer -> String
-- ab i = case someNatVal (fromInteger i) of
--   Just (SomeNat p) -> show $ MM (V.generate (fromInteger $ natVal p) (const 0))

-- abc :: Integer -> String
-- abc i = case someNatVal (fromInteger i) of
--   Just (SomeNat (_ :: Proxy n)) -> show (generate (const 0) :: MMatrix n n Int)

-- instance (KnownNat m, KnownNat n, AAdditive a) => AAdditive (MMatrix m n a) where
--   (.+) = pplus
--   zero = unit'

data Matrix k = M
  { nrows :: {-# UNPACK #-} !Int
  , ncols :: {-# UNPACK #-} !Int
  , mvect :: V.Vector k }
  deriving (Show, Eq, Functor, Foldable, Traversable)

prettyMatrix :: Show a => Matrix a -> String
prettyMatrix mx@M{ncols=m,nrows=n,mvect=v} = unlines
 [ "[ " <> unwords ((\j -> fill len $ show $ mx !. (i,j)) `fmap` [1..n]) <> " ]" | i <- [1..m] ]
 where
    len        = V.maximum $ fmap (length . show) v
    fill k str = replicate (k - length str) ' ' ++ str

encode :: Int -> (Int,Int) -> Int
encode m (i,j) = (i-1)*m + j - 1

-- decode :: Int -> Int -> (Int,Int)
-- decode m k = (q+1,r+1)
--   where (q,r) = quotRem k m

(!.) :: Matrix a -> (Int,Int) -> a
(!.) M{ncols=m, mvect=as} ij = V.unsafeIndex as (encode m ij)

entry :: Int -> Int -> Matrix a -> a
entry i j mx = mx !. (i,j)

getEntry :: (Int,Int) -> Matrix a -> a
getEntry ij mx = mx !. ij

setEntry :: a -> (Int,Int) -> Matrix a -> Matrix a
setEntry a ij mx@M{ncols=m, mvect=as} = mx{mvect=as'} where
  as' = V.modify (\v -> MV.write v (encode m ij) a) as

getRow :: Int -> Matrix a -> [a]
getRow i mx = [ entry i j mx | j <- [1..ncols mx] ]

getCol :: Int -> Matrix a -> [a]
getCol j mx = [ entry i j mx | i <- [1..nrows mx] ]

getDiagonal :: Matrix a -> [a]
getDiagonal mx = [ entry i i mx | i <- [1..min (nrows mx) (ncols mx)] ]


--- * construct / destruct -------------------------------------------------------------------------------------------

fromList :: Int -> Int -> [a] -> Matrix a
fromList n m as = M
  { nrows = n
  , ncols = m
  , mvect = V.fromListN (n*m) as }

toList :: Matrix a -> [a]
toList = V.toList . mvect

toLists, toRows, toCols :: Matrix a -> [[a]]
toLists M{ncols=m,mvect=as} = go (V.toList as) where
  go [] = []
  go xs = let (b,bs) = L.splitAt m xs in b:go bs
toRows = toLists
toCols = L.transpose . toRows

fromLists :: [[a]] -> Matrix a
fromLists []       = error "Matrix.fromLists: empty list."
fromLists (xs:xss) = fromList n m $ concat $ xs : fmap (take m) xss
  where
    n = 1 + length xss
    m = length xs

matrix :: Int -> Int -> ((Int,Int) -> a) -> Matrix a
matrix n m f = M{nrows=n, ncols=m, mvect=as} where
  as = V.create $ do
    v <- MV.new $ n * m
    let en = encode m
    forM_ [1..n] $
      \i -> forM_ [1..m] $
      \j -> MV.unsafeWrite v (en (i,j)) (f (i,j))
    return v

fold :: Matrix a -> [Matrix a] -> Matrix [a]
fold m = foldr (elementwise (:)) (fmap (:[]) m)


--- * arithmetic operations ------------------------------------------------------------------------------------------

elementwise :: (a -> b -> c) -> Matrix a -> Matrix b -> Matrix c
elementwise f m1 m2 = m1{ mvect = V.zipWith f (mvect m1) (mvect m2) }

add :: AAdditive a => Matrix a -> Matrix a -> Matrix a
add = elementwise (.+)

iemul :: Matrix (IExpr v) -> Matrix (IExpr v) -> Matrix (IExpr v)
iemul mx1@M{nrows=n1,ncols=m1} mx2@M{ncols=m2} = matrix n1 m2 $ \(i,j) -> bigAdd [ (mx1 !. (i,k)) `mmul` (mx2 !. (k,j)) | k <- [1 .. m1] ] where
  (IVal 0) `mmul` _        = IVal 0
  _        `mmul` (IVal 0) = IVal 0
  a        `mmul` b        = IMul a b

-- MS: not that I know what I do
{-# RULES "mul/(IExpr v)" mul = iemul #-}
{-# NOINLINE [1] mul                  #-}
mul :: SSemiRing a => Matrix a -> Matrix a -> Matrix a
mul mx1@M{nrows=n1,ncols=m1} mx2@M{ncols=m2} = matrix n1 m2 $ \(i,j) -> bigAdd [ mx1 !. (i,k) .* mx2 !. (k,j) | k <- [1 .. m1] ]

eye :: SSemiRing a => Int -> Matrix a
eye d = matrix d d $ \(i,j) -> if i == j then one else zero

zeros :: AAdditive a => Int -> Int -> Matrix a
zeros n m = fromList n m (repeat zero)

msum :: AAdditive a => Int -> [Matrix a] -> Matrix a
msum d []     = zeros d d
msum _ (m:ms) = bigAdd `fmap` fold m ms


-- * logic ----------------------------------------------------------------------------------------------------------

instance AAdditive a => AAdditive (Matrix a) where
  (.+) = add
  zero = error "Matrix.zero not defined"

instance AAdditiveGroup a => AAdditiveGroup (Matrix a) where
  neg = fmap neg

instance SSemiRing a => MMultiplicative (Matrix a) where
  (.*) = mul
  one = error "Matrix.one not defined"

instance Equal a => Equal (Matrix a) where
  type B (Matrix a) = B a
  m1 .== m2 = bigAnd $ elementwise (.==) m1 m2

