module SmtLib.PP
  ( module SMTLib2
  , render
  )
where

import SMTLib2 (pp)
import qualified Text.PrettyPrint as PP

render :: PP.Doc -> String
render = PP.render

