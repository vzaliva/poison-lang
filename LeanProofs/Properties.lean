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
      simp [typecheckExpr] at h2
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    | var name =>
      simp [typecheckExpr, typecheckVar] at h2
      cases h0: lookupVarEnv ctx.varEnv name with
      | none =>
        simp [h0] at h2
      | some qt =>
        simp [h0] at h2
        cases h1: qt with
        | mk etyp poison pred =>
          simp [h0, h1] at h2
          cases h3: pred with
          | none =>
            simp [h0, h1, h3, pure, Except.pure] at h2
            cases result
            cases ctx
            simp [h2]
            injection h2
            trivial
          | some tp =>
            simp [h0, h1, h3] at h2
            cases h4: tp with
            | mk tag etyp =>
              simp [h0,h1,h3,h4] at h2
              cases h5: ctx.tagEnv[tag]? with
              | none =>
                simp [h0, h1, h3, h4, h5, pure, Except.pure] at h2
                cases result
                cases ctx
                simp [h2]
                injection h2
                trivial
              | some b =>
                cases h6: b with
                | true =>
                  simp [h0, h1, h3, h4, h5, h6, pure, Except.pure] at h2
                  cases result
                  cases ctx
                  simp [h2]
                  injection h2
                  trivial
                | false =>
                  simp [h0, h1, h3, h4, h5, h6, pure, Except.pure] at h2
                  cases result
                  cases ctx
                  simp [h2]
                  injection h2
                  trivial
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
      simp [Expr.toPExpr] at h1
