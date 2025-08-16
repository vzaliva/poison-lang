-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck


-- Pure expression type checking does not modify typestates
theorem typecheck_preserves_typestate : ∀ (fuel : Nat),
  ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
  e.toPExpr = .ok pe →
  typecheckExpr ctx e fuel = .ok result →
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' := by

  intros fuel ctx e pe result P H
  induction e generalizing fuel ctx result with
  | unit
  | str _
  | num _
  | bool _ =>
    cases fuel <;> simp [typecheckExpr] at H
    cases H
    exact ⟨rfl, rfl, rfl⟩
  | var name =>
    cases fuel <;> simp [typecheckExpr] at H
    -- All var cases preserve environment fields - handle uniformly
    simp [typecheckVar] at H
    cases h0: lookupVarEnv ctx.varEnv name with
    | none => simp [h0] at H
    | some qt =>
      cases h1: qt with
      | mk etyp poison pred =>
        cases h3: pred with
        | none =>
          -- No predicate case: preserves environment
          simp [h0, h1, h3, pure, Except.pure] at H
          cases result; cases ctx; simp [H]; injection H; trivial
        | some tp =>
          -- Has predicate: all cases preserve environment
          cases h4: tp with
          | mk tag etyp =>
            cases h5: ctx.tagEnv[tag]? with
            | none =>
              -- Guard unknown: preserves environment
              simp [h0, h1, h3, h4, h5, pure, Except.pure] at H
              cases result; cases ctx; simp [H]; injection H; trivial
            | some b =>
              -- Guard known (true/false): both preserve environment
              cases h6: b with
              | true =>
                simp [h0, h1, h3, h4, h5, h6, pure, Except.pure] at H
                cases result; cases ctx; simp [H]; injection H; trivial
              | false =>
                simp [h0, h1, h3, h4, h5, h6, pure, Except.pure] at H
                cases result; cases ctx; simp [H]; injection H; trivial
  | deref e1 IH =>
    /-
     simp [Expr.toPExpr, Functor.map, Except.map] at P
     cases h2: e1.toPExpr with
     | error err =>
       simp [h2] at P
     | ok pe1 =>
       simp [h2] at P
    -/

    cases fuel with
    | zero =>
      simp [typecheckExpr] at H
    | succ fuel =>
      simp [typecheckExpr] at H
      cases fuel with
      | zero =>
        simp [typecheckDeref] at H
      | succ fuel' =>
        simp [typecheckDeref, bind, Except.bind] at H
        cases h0: typecheckExpr ctx e1 fuel' with
        | error err =>
          simp [h0] at H
        | ok v =>
          -- use IH
          specialize IH fuel' ctx result
          simp [h0] at H
          cases h1: v.qualType with
          | mk etyp poison _pred =>
            simp [h1] at H
            cases h3: etyp <;> simp [h3] at H
            cases h4: poison with
            | true =>
              simp [h4] at H
              simp [pure, Except.pure] at H
              cases result; cases ctx; simp [H]; injection H
              sorry
            | false =>
              sorry
  | op e1 op e2 IH1 IH2 =>
    sorry
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    sorry
  | vlet x e1 e2 IH1 IH2 =>
    sorry
  | app e1 e2 IH1 IH2 =>
    sorry
  /- The following cases are not possible to convert to PExpr -/
  | newRef _
  | assign _ _
  | seq _ _
  | kwhile _ _
  | fn _ _ _ _
  | pfn _ _ _ _
  | rand _
  | frand _
  | printString _
  | printInt _ =>
    contradiction
