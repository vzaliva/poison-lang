-- TypecheckPExprPreservesTypestate Property for the Poison Language
--
-- The TypecheckPExprPreservesTypestate property states that typechecking
-- a pure expression (one that can be converted to PExpr) preserves the
-- typestate: memory environment equivalence, tag environment, and location/tag counters.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.JoinMemEnv

-- ================================================================
-- TypecheckPExprPreservesTypestate Property
-- ================================================================

-- TypecheckPExprPreservesTypestate property: typechecking pure expressions preserves typestate
-- For any expression that can be converted to PExpr, if typechecking succeeds,
-- then the memory environments are equivalent, tag environments are equal,
-- and location/tag counters are preserved
--
-- The proof is provided in TypecheckPExprPreservesTypestateProofs.lean
theorem typecheck_PExpr_preserves_typestate :
  ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = .ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e fuel = .ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag'
 := sorry
