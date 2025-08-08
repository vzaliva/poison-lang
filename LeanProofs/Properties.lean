-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck

-- Pure expression type checking does not modify typestates
theorem typecheck_preserves_typestate
  (ctx : TypeContext) (e : Expr):
e.toPExpr = .ok pe →
typecheckExpr ctx e fuel = .ok result →
ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' := by
  intro h1 h2
  sorry
