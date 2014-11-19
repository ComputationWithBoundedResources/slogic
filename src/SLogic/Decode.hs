{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module SLogic.Decode where


import qualified Data.Map.Strict as M
import Control.Monad


class Monad m => Decode m c a where
  decode :: c -> m a

instance Monad m => Decode m () () where
  decode () = return ()
    
instance (Decode m c a, Decode m d b) => Decode m (c,d) (a,b) where
  decode (c,d) = do a <- decode c; b <- decode d; return (a,b)

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
