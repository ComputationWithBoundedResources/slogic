-- | This module provides the decoding mechanism.
module SLogic.Decode where


import           Control.Monad
import qualified Data.Map.Strict as M


class Monad m => Decode m c a where
  decode :: c -> m a

instance Monad m => Decode m () () where
  decode () = return ()

instance (Decode m c1 a1, Decode m c2 a2) => Decode m (c1,c2) (a1,a2) where
  decode (c1,c2) = do a1 <- decode c1; a2 <- decode c2; return (a1,a2)

instance (Decode m c1 a1, Decode m c2 a2, Decode m c3 a3) => Decode m (c1,c2,c3) (a1,a2,a3) where
  decode (c1,c2,c3) = do a1 <- decode c1; a2 <- decode c2; a3 <- decode c3; return (a1,a2,a3)

instance (Decode m c a) => Decode m [c] [a] where
  decode = mapM decode

instance Decode m a b => Decode m (Maybe a) (Maybe b) where
  decode (Just b) = liftM Just (decode b)
  decode Nothing  = return Nothing

instance (Ord i, Decode m c a) => Decode m (M.Map i c) (M.Map i a) where
  decode x = do
    pairs <- sequence $ do
      (i,e) <- M.assocs x
      return $ do
        f <- decode e
        return (i,f)
    return $ M.fromList pairs
