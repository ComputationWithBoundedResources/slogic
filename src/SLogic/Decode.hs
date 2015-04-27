-- | This module provides the decoding mechanism.
module SLogic.Decode where


import           Control.Applicative
import           Control.Monad
import qualified Data.Map.Strict     as M
import qualified Data.Set            as S
import qualified Data.Traversable    as F


class (Applicative m, Monad m) => Decode m c a where
  decode :: c -> m a

instance (Applicative m, Monad m) => Decode m () () where
  decode = return

instance (Decode m c1 a1, Decode m c2 a2) => Decode m (c1,c2) (a1,a2) where
  decode (c1,c2) = (,) <$> decode c1 <*> decode c2

instance (Decode m c1 a1, Decode m c2 a2, Decode m c3 a3) => Decode m (c1,c2,c3) (a1,a2,a3) where
  decode (c1,c2,c3) = (,,) <$> decode c1 <*> decode c2 <*> decode c3

instance (Decode m c1 a1, Decode m c2 a2, Decode m c3 a3, Decode m c4 a4) => Decode m (c1,c2,c3,c4) (a1,a2,a3,a4) where
  decode (c1,c2,c3,c4) = (,,,) <$> decode c1 <*> decode c2 <*> decode c3 <*> decode c4

instance (Decode m c a) => Decode m [c] [a] where
  decode = mapM decode

instance Decode m a b => Decode m (Maybe a) (Maybe b) where
  decode (Just b) = Just `liftM` decode b
  decode Nothing  = return Nothing

instance (Ord i, Decode m c a) => Decode m (M.Map i c) (M.Map i a) where
  decode = F.mapM decode

instance (Ord i, Decode m c Bool) => Decode m (M.Map i c) (S.Set i) where
  decode m = (M.keysSet . M.filter id) `liftM` F.mapM decode m

data Property a i c = Property (a -> Bool) (M.Map i c)

instance (Ord i, Decode m c a) => Decode m (Property a i c) (S.Set i) where
  decode (Property k m) = (M.keysSet . M.filter k) `liftM` F.mapM decode m

