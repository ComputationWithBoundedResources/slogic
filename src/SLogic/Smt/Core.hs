{-# LANGUAGE FlexibleContexts #-}
module SLogic.Smt.Core 
  (
  module SLogic.Logic.Core

  , bvarM', bvarMO

  ) where

import Control.Monad.Reader
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Text.PrettyPrint.ANSI.Leijen as PP


import SLogic.Solver
import SLogic.Decode
import SLogic.Logic.Core
import SLogic.Smt.SmtM


bvarM' :: SmtM e (Expr e)
bvarM' = bvar `liftM` fresh

bvarMO:: Ord a => a -> Memo a (Expr e) (SmtM e) (Expr e)
bvarMO = memoized $ \_ -> lift bvarM'

instance Decode (Reader (M.Map String Value)) e Value => Decode (Reader (M.Map String Value)) (Expr e) Value where
  decode c = case c of
    Atom a -> decode a 
    BVal b -> return (BoolVal b)
    BVar v -> get v
    _      -> return Other
    where get v = asks $ \m -> Other `fromMaybe` M.lookup v  m

instance Monad m => Decode m Value Bool where
  decode c = case c of
    BoolVal b -> return b
    _         -> error "SmtLib.Smt.Bool.decode: not a bool"


