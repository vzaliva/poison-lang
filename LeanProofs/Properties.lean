-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck

-- Pure expression type checking does not modify typestates
theorem typecheck_preserves_typestate : ∀ (fuel : Nat),
  ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
  e.toPExpr = .ok pe →
  typecheckExpr ctx e fuel = .ok result →
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' := by
  intro fuel
  induction fuel with
  | zero =>
    intro ctx e pe result h1 h2
    -- If fuel = 0, typecheckExpr returns an error, contradicting h2
    unfold typecheckExpr at h2
    contradiction
  | succ fuel' IH =>
    intro ctx e pe result h1 h2
    -- We need to narrow down the type of e (constructors) based on h1
    cases e with
    | unit
    | num _
    | bool _ =>
      simp [Expr.toPExpr] at h1
      injection h1 with h1'
      simp [typecheckExpr, typecheckUnit] at h2
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    | var _ =>
      sorry
    | op _ _ _ =>
      sorry
    | ite _ _ _ =>
      sorry
    | deref _ =>
      sorry
    | vlet _ _ _ =>
      sorry
    | app _ _ =>
      sorry
    | _  =>
      /- These cases are not possible to convert to PExpr -/
      sorry
