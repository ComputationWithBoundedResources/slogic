-- | This module exports the default SMT interface.
module SLogic.Smt
  ( Expr
  , module M)
  where

import SLogic.Decode      as M
import SLogic.Logic.Core  as M
import SLogic.Logic.Int   as M
import SLogic.Smt.Solver  as M
import SLogic.Solver      as M
import SLogic.Result      as M
import SLogic.SolverState as M

type Expr = M.Formula M.IFormula

