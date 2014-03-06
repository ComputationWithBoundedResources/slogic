{-# LANGUAGE OverloadedStrings #-}
module SmtLib.Logic.QF_NIA 
  ( module SmtLib.Logic.Core
  , module SmtLib.Logic.Int
  )
where

import SmtLib.Logic.Data
import SmtLib.Logic.Core
import SmtLib.Logic.Int
{-import SmtLib.Logic.Poly-}

import SMTLib2 (Name)

logic :: Name
logic =  "QF_NIA"

{-data Poly a = Poly [Mono a]-}
{-data Mono a = Mono a Pows-}
{-type Pos    = [Int]-}

{-instance Decode a Int => Decode m (Mono a) (Mono Int) where-}
  {-decode (Mono a ps) = Mono (decode a) ps-}

{-instance Decode a Int => Decode (Poly a) (Poly Int) where-}
  {-decode (Poly ms) = Poly (map $ decode ms)-}


