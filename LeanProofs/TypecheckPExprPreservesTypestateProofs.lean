-- Proofs for TypecheckPExprPreservesTypestate Property

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

import LeanProofs.JoinMemEnv
import LeanProofs.ToExpr
import LeanProofs.TypeSafety
import LeanProofs.TypecheckPExprPreservesTypestate


open Std

-- set_option diagnostics true

set_option maxHeartbeats 2000000

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

-- Property that a TypeResult preserves typestate relative to a base memory environment
private def preservesTypestate (m : MemoryTypeEnv) (tagEnv : TagEnv) (nextLoc : Loc) (nextTag : Tag)
    (result : TypeResult) : Prop :=
  m.equiv result.memEnv' ∧ tagEnv = result.tagEnv' ∧ nextLoc = result.nextLoc' ∧ nextTag = result.nextTag'

-- Private lemma for unit case
private lemma typecheck_unit_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat)
  (_C : ctx.pureCtx = true) (_P : Expr.unit.toPExpr = Except.ok pe) (H : typecheckExpr ctx Expr.unit (fuel + 1) = Except.ok result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv]

-- Private lemma for str case
private lemma typecheck_str_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (s : String)
  (_C : ctx.pureCtx = true) (_P : (Expr.str s).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.str s) (fuel + 1) = Except.ok result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv]

-- Private lemma for num case
private lemma typecheck_num_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (n : Int)
  (_C : ctx.pureCtx = true) (_P : (Expr.num n).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.num n) (fuel + 1) = Except.ok result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv]

-- Private lemma for bool case
private lemma typecheck_bool_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (b : Bool)
  (_C : ctx.pureCtx = true) (_P : (Expr.bool b).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.bool b) (fuel + 1) = Except.ok result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv]

-- Private lemma for var case
private lemma typecheck_var_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (name : Name)
  (C : ctx.pureCtx = true) (_P : (Expr.var name).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.var name) (fuel + 1) = Except.ok result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp_all [typecheckExpr]
  -- All var cases preserve environment fields - handle uniformly
  simp [typecheckVar] at H
  cases h0: ctx.varEnv.lookup name with
  | none => simp_all
  | some qt =>
    simp [h0] at H
    cases h1: qt with
    | mk etyp poison pred =>
      simp [h1] at H
      cases h3 : pred with
      | guardClosure tag arg_name pred_body var_env =>
        -- Both guard variants behave identically for the environment fields
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
      | guardOnly tag =>
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]
      | noPred =>
        -- No predicate case: preserves environment
        simp_all [typecheckVar, h0, h1, h3, pure, Except.pure]
        cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv]

-- Private lemma for deref case
private lemma typecheck_deref_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr)
  (C : ctx.pureCtx = true) (P : e1.deref.toPExpr = Except.ok pe) (H : typecheckExpr ctx e1.deref (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp [typecheckExpr] at H
  (cases fuel with | zero | succ fuel') <;>
    simp [typecheckDeref, bind, Except.bind] at H
  cases h0: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    -- use IH
    simp [Expr.toPExpr, Expr.toPExpr?] at P
    cases h1: Expr.toPExpr? e1 with
    | none =>
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
    | some pe1 =>
      have h1' : e1.toPExpr = Except.ok pe1 := by
        simp [Expr.toPExpr, h1, pure, Except.pure]
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
      have hfuel : fuel' < fuel' + 1 + 1 := by linarith
      specialize IH fuel' hfuel ctx e1 pe1 result1 h1' C h0
      unfold preservesTypestate at IH
      rcases IH with ⟨H1, H2, H3, H4⟩
      simp_all
      cases h2: result1.qualType with
      | mk etyp poison _pred =>
        simp_all
        cases h3: etyp with
        | ref t l =>
          simp_all
          -- New check: if t != ETyp.int then throw
          split at H
          · -- Case: t = ETyp.int (the only successful case)
            -- l is a LocSet, not a Loc
            -- typecheckDeref uses LocSet.foldM to iterate over locations
            -- Handle the isEmpty check first
            cases h_empty : l.isEmpty with
            | true =>
              -- Empty locset: throws error (contradiction with success)
              have hl_empty : l = ∅ := (ExtTreeSet.isEmpty_iff).1 h_empty
              simp [hl_empty] at H
              cases H
            | false =>
              -- Non-empty: foldM preserves environments
              -- Key observation: typecheckDeref only reads from result1.memEnv' and result1.tagEnv'
              -- but never modifies them. All branches return result1.memEnv', result1.tagEnv', etc.
              -- The foldM only computes (joinedCellPoison, mergedPred?), but doesn't affect environments
              -- Simplify the `if l = ∅` condition (we know l is non-empty)
              have h_ne : l ≠ ∅ := by
                intro heq
                rw [← ExtTreeSet.isEmpty_iff] at heq
                simp_all
              simp only [h_ne, ↓reduceIte, pure, Except.pure] at H
              -- Now H has the foldM bind structure
              -- The key observation: ALL return branches in the match expression
              -- use result1.memEnv', result1.tagEnv', result1.nextLoc', result1.nextTag'.
              -- We need to show that if H = Except.ok result, then result has these environments.
              -- Since the structure is complex with nested matches, we use split to handle all cases.
              split at H
              · -- foldM error case
                contradiction
              · -- foldM ok case
                rename_i v
                split at H
                · -- poison = true case
                  simp only [↓reduceIte, Except.ok.injEq] at H
                  cases H
                  exact ⟨H1, rfl, rfl, rfl⟩
                · -- poison = false case
                  split at H
                  · -- noPred case
                    simp only [Except.ok.injEq] at H
                    cases H
                    exact ⟨H1, rfl, rfl, rfl⟩
                  · -- guardOnly case
                    rename_i k
                    split at H
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
                  · -- guardClosure case
                    rename_i k _ _ _
                    split at H
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
                    · simp only [Except.ok.injEq] at H
                      cases H
                      exact ⟨H1, rfl, rfl, rfl⟩
          · -- Case: t ≠ ETyp.int (error - contradiction)
            cases H
        | _ => simp_all

-- Private lemma for ite case
private lemma typecheck_ite_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 e3 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.ite e2 e3).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.ite e2 e3) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckIf, bind, Except.bind]
  simp [Expr.toPExpr, Expr.toPExpr?] at P
  cases h1: Expr.toPExpr? e1 with
  | none =>
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
  | some pe1 =>
      have h1' : e1.toPExpr = Except.ok pe1 := by
        simp [Expr.toPExpr, h1, pure, Except.pure]
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
      cases h3: Expr.toPExpr? e2 with
      | none =>
          simp [Expr.toPExpr, Expr.toPExpr?, h3, pure, Except.pure] at P
      | some pe2 =>
          have h3' : e2.toPExpr = Except.ok pe2 := by
            simp [Expr.toPExpr, h3, pure, Except.pure]
          simp [Expr.toPExpr, Expr.toPExpr?, h3, pure, Except.pure] at P
          cases h4: Expr.toPExpr? e3 with
          | none =>
              simp [Expr.toPExpr, Expr.toPExpr?, h4, pure, Except.pure] at P
          | some pe3 =>
              have h4' : e3.toPExpr = Except.ok pe3 := by
                simp [Expr.toPExpr, h4, pure, Except.pure]
              simp [Expr.toPExpr, Expr.toPExpr?, h4, pure, Except.pure] at P

              cases h8: matchGuard e1 ctx.memEnv ctx.varEnv with
              | error err =>
                -- simple case: no matching predicate found
                simp_all
                cases h5: typecheckExpr ctx e1 fuel' with
                | error err =>
                  simp_all
                | ok result1 =>
                  simp [h5] at H
                  have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                  have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1' C h5
                  unfold preservesTypestate at IH1
                  rcases IH1 with ⟨H1, H2, H3, H4⟩
                  simp_all
                  cases h6: result1.qualType with
                  | mk etyp' poison' pred' =>
                    simp_all
                    cases h7: etyp' != ETyp.bool with
                    | true =>
                      simp_all
                    | false =>
                      simp_all [pure, Except.pure]
                      cases h9: typecheckExpr
                                  { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                    tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := ctx.pureCtx }
                                  e2 fuel' with
                      | error err =>
                        simp_all
                      | ok result2 =>
                        simp_all
                        cases h10: result2.qualType with
                        | mk etyp2 p'' pred =>
                          simp_all
                          cases h11: typecheckExpr
                                  { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                    tagEnv := result1.tagEnv',
                                    nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := ctx.pureCtx }
                                  e3 fuel' with
                          | error err =>
                            simp_all
                          | ok result3 =>
                            simp_all
                            cases h12: result3.qualType with
                            | mk etyp3 p''' pred =>
                              simp_all
                              cases h13: beqETypSignature etyp2 etyp3 with
                              | false =>
                                simp_all
                              | true =>
                                simp_all [pure, Except.pure]
                                have C' : ({ pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                             tagEnv := result1.tagEnv',
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                                        := by simp_all
                                have IH2 := IH fuel' hfuel
                                    { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                      tagEnv := result1.tagEnv',
                                      nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true }
                                    e2 pe2 result2 h3' C' h9
                                have C'' : ({ pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                              tagEnv := result1.tagEnv',
                                              nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                                        := by simp_all
                                have IH3 := IH fuel' hfuel
                                    { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                      tagEnv := result1.tagEnv',
                                      nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                                    e3 pe3 result3 h4' C'' h11
                                unfold preservesTypestate at IH2 IH3
                                rcases IH2 with ⟨H14, H15, H16⟩
                                rcases IH3 with ⟨H17, H18, H19⟩
                                -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv' ∧ result1.memEnv'.equiv result3.memEnv'
                                -- Goal: memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv')
                                -- Use joinMemEnv_idempotent with m=result1.memEnv', m1=result2.memEnv', m2=result3.memEnv'
                                have H_join : result1.memEnv'.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                                  joinMemEnv_idempotent result1.memEnv' result2.memEnv' result3.memEnv' H14 H17
                                have H_trans : ctx.memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                                  MemoryTypeEnv.equiv.trans ctx.memEnv result1.memEnv' (joinMemEnvs result2.memEnv' result3.memEnv') H1 H_join
                                cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
              | ok k_deps =>
                -- predicate-based case: matching predicate found
                simp_all
                have ctx_eta :
                  { pc := ctx.pc,
                    memEnv := ctx.memEnv,
                    varEnv := ctx.varEnv,
                    tagEnv := ctx.tagEnv,
                    nextLoc := ctx.nextLoc,
                    nextTag := ctx.nextTag,
                    pureCtx := true } = ctx := by
                  rw [← C]

                cases h5: typecheckExpr {
                                          pc := ctx.pc,
                                          memEnv := ctx.memEnv,
                                          varEnv := ctx.varEnv,
                                          tagEnv := ctx.tagEnv,
                                          nextLoc := ctx.nextLoc,
                                          nextTag := ctx.nextTag,
                                          pureCtx := true
                                        } e1 fuel' with
                | error err =>
                   rw [h5] at H
                   simp at H
                | ok result1 =>
                  rw [h5] at H
                  simp at H
                  cases h6: result1.qualType with
                  | mk etyp1 p' pred =>
                    simp_all
                    cases h7: etyp1 != ETyp.bool
                    · -- false case: etyp1 = ETyp.bool, proceed with the then/else branches
                      simp_all [pure, Except.pure]
                      cases h9:  typecheckExpr
                                  { pc := ctx.pc,
                                    memEnv := ctx.memEnv,
                                    varEnv := ctx.varEnv,
                                    tagEnv := ctx.tagEnv.insert k_deps.1 { value := true, deps := k_deps.2 },
                                    nextLoc := ctx.nextLoc,
                                    nextTag := ctx.nextTag,
                                    pureCtx := true }
                                  e2 fuel' with
                      | error err =>
                        simp [h9] at H
                      | ok result2 =>
                        simp [h9] at H
                        cases h10: result2.qualType with
                        | mk etyp2 p'' pred =>
                          simp [h10] at H
                          cases h11: typecheckExpr
                                  { pc := ctx.pc,
                                    memEnv := ctx.memEnv,
                                    varEnv := ctx.varEnv,
                                    tagEnv := ctx.tagEnv.insert k_deps.1 { value := false, deps := k_deps.2 },
                                    nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                                  e3 fuel' with
                          | error err =>
                            simp [h11] at H
                          | ok result3 =>
                            simp [h11] at H
                            cases h12: result3.qualType with
                            | mk etyp3 p''' pred =>
                              simp [h12] at H
                              cases h13: beqETypSignature etyp2 etyp3 with
                              | false =>
                                simp [h13] at H
                              | true =>
                                simp [h13] at H
                                have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                                have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1' C h5
                                unfold preservesTypestate at IH1
                                rcases IH1 with ⟨H1, H2, H3, H4⟩
                                have C' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                             tagEnv := ctx.tagEnv.insert k_deps.1 { value := true, deps := k_deps.2 },
                                             nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true } : TypeContext).pureCtx = true
                                        := by simp
                                have IH2 :=
                                  IH fuel' hfuel { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                                   tagEnv := ctx.tagEnv.insert k_deps.1 { value := true, deps := k_deps.2 },
                                                   nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true }
                                                   e2 pe2 result2 h3' C' h9

                                have C'' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                                   tagEnv := ctx.tagEnv.insert k_deps.1 { value := false, deps := k_deps.2 },
                                                   nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                                        := by simp
                                have IH3 :=
                                  IH fuel' hfuel
                                    { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                      tagEnv := ctx.tagEnv.insert k_deps.1 { value := false, deps := k_deps.2 },
                                      nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                                    e3 pe3 result3 h4' C'' h11
                                unfold preservesTypestate at IH2 IH3
                                rcases IH2 with ⟨H14, H15, H16⟩
                                rcases IH3 with ⟨H17, H18, H19⟩
                                -- Prove: memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv')
                                -- We have: memEnv.equiv memEnv (reflexivity from H1)
                                -- And: memEnv.equiv result2.memEnv' (from H14)
                                -- And: memEnv.equiv result3.memEnv' (from H17)
                                -- Use joinMemEnv_idempotent with m=memEnv, m1=result2.memEnv', m2=result3.memEnv'
                                have H_join : ctx.memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                                  joinMemEnv_idempotent ctx.memEnv result2.memEnv' result3.memEnv' H14 H17
                                cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
                    · -- true case: etyp1 != ETyp.bool, the else branch returns an error (contradiction)
                      simp_all

-- Private lemma for op case
private lemma typecheck_op_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr) (op : Op) (e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.op op e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.op op e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckOp, bind, Except.bind]
  simp [Expr.toPExpr, Expr.toPExpr?] at P
  cases h1: Expr.toPExpr? e1 with
  | none =>
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
  | some pe1 =>
      have h1' : e1.toPExpr = Except.ok pe1 := by
        simp [Expr.toPExpr, h1, pure, Except.pure]
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
      cases h2: Expr.toPExpr? e2 with
      | none =>
          simp [Expr.toPExpr, Expr.toPExpr?, h2, pure, Except.pure] at P
      | some pe2 =>
          have h2' : e2.toPExpr = Except.ok pe2 := by
            simp [Expr.toPExpr, h2, pure, Except.pure]
          simp [Expr.toPExpr, Expr.toPExpr?, h2, pure, Except.pure] at P
          cases h3: typecheckExpr ctx e1 fuel' with
          | error err =>
            simp_all
          | ok result1 =>
            simp [h3] at H
            have hfuel : fuel' < fuel' + 1 + 1 := by linarith
            have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1' C h3
            rcases IH1 with ⟨H1, H2, H3, H4⟩
            simp_all
            cases h4: result1.qualType with
            | mk etyp1 p1 pred1 =>
              simp_all
              cases h5: typecheckExpr
                              { pc := ctx.pc, memEnv := result1.memEnv',
                                varEnv := ctx.varEnv,
                                tagEnv := result1.tagEnv',
                                nextLoc := result1.nextLoc',
                                nextTag := result1.nextTag',
                                pureCtx := ctx.pureCtx }
                              e2 fuel' with
              | error err =>
                simp_all
              | ok result2 =>
                simp_all
                cases h6: result2.qualType with
                | mk etyp2 p2 pred2 =>
                  simp_all
                  cases h7: opEType? op etyp1 etyp2 with
                  | some etyp3 =>
                    simp_all [pure, Except.pure]
                    have C' : ({ pc := ctx.pc,
                                 memEnv := result1.memEnv',
                                 varEnv := ctx.varEnv,
                                 tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc',
                                 nextTag := result1.nextTag',
                                 pureCtx := true } : TypeContext).pureCtx = true
                            := by simp_all
                    have IH2 := IH fuel' hfuel
                              { pc := ctx.pc,
                                memEnv := result1.memEnv',
                                varEnv := ctx.varEnv,
                                tagEnv := result1.tagEnv',
                                nextLoc := result1.nextLoc',
                                nextTag := result1.nextTag',
                                pureCtx := true }
                              e2 pe2 result2 h2' C' h5
                    unfold preservesTypestate at IH2
                    rcases IH2 with ⟨H8, H9, H10⟩
                    -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
                    -- H1: ctx.memEnv.equiv result1.memEnv'
                    -- H8: result1.memEnv'.equiv result2.memEnv'
                    -- Goal: ctx.memEnv.equiv result.memEnv' where result.memEnv' = result2.memEnv'
                    have H_trans : ctx.memEnv.equiv result2.memEnv' := MemoryTypeEnv.equiv.trans ctx.memEnv result1.memEnv' result2.memEnv' H1 H8
                    simp_all [H_trans]
                    cases result; cases result1; cases result2; cases ctx; cases H; simp_all
                  | none =>
                    simp_all

-- Private lemma for unaryop case
private lemma typecheck_unaryop_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (op : UnaryOp) (e : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.unaryop op e).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckUnaryOp, bind, Except.bind]
  simp [Expr.toPExpr, Expr.toPExpr?] at P
  cases h1: Expr.toPExpr? e with
  | none =>
    simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
  | some pe1 =>
    have h1' : e.toPExpr = Except.ok pe1 := by
      simp [Expr.toPExpr, h1, pure, Except.pure]
    simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
    cases h2: typecheckExpr ctx e fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h2] at H
      have hfuel : fuel' < fuel' + 1 + 1 := by linarith
      cases h4: result1.qualType with
      | mk etyp p pred =>
        simp_all
        cases h7: opUnaryEType? op etyp with
        | some r =>
          simp_all [pure, Except.pure]
          specialize IH fuel' hfuel ctx e pe1 result1 h1' C h2
          unfold preservesTypestate at IH
          rcases IH with ⟨H8, H9, H10⟩
          simp_all
          cases result; cases result1; cases ctx; cases H; simp_all
        | none =>
          simp_all

-- Private lemma for vlet case
private lemma typecheck_vlet_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (x : Name) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.vlet x e1 e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.vlet x e1 e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckVlet, bind, Except.bind]
  simp [Expr.toPExpr, Expr.toPExpr?] at P
  cases h1: Expr.toPExpr? e1 with
  | none =>
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
  | some pe1 =>
      have h1' : e1.toPExpr = Except.ok pe1 := by
        simp [Expr.toPExpr, h1, pure, Except.pure]
      simp [Expr.toPExpr, Expr.toPExpr?, h1, pure, Except.pure] at P
      cases h2: Expr.toPExpr? e2 with
      | none =>
          simp [Expr.toPExpr, Expr.toPExpr?, h2, pure, Except.pure] at P
      | some pe2 =>
          have h2' : e2.toPExpr = Except.ok pe2 := by
            simp [Expr.toPExpr, h2, pure, Except.pure]
          simp [Expr.toPExpr, Expr.toPExpr?, h2, pure, Except.pure] at P
          cases h3: typecheckExpr ctx e1 fuel' with
          | error err =>
            simp_all
          | ok result1 =>
            simp [h3] at H
            have hfuel : fuel' < fuel' + 1 + 1 := by linarith
            have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1' C h3
            rcases IH1 with ⟨H1, H2, H3, H4⟩
            simp_all
            cases h4: result1.qualType with
            | mk etyp1 p1 pred1 =>
              simp_all
              cases h4: typecheckExpr
                              { pc := ctx.pc, memEnv := result1.memEnv',
                                varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
                                tagEnv := result1.tagEnv',
                                nextLoc := result1.nextLoc',
                                nextTag := result1.nextTag', pureCtx := ctx.pureCtx }
                              e2 fuel' with
              | error err =>
                simp_all
              | ok result2 =>
                simp_all
                cases h5: result2.qualType with
                | mk etyp2 p2 pred2 =>
                  simp_all [pure, Except.pure]
                  have C' : ({ pc := ctx.pc,
                               memEnv := result1.memEnv',
                               varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
                               tagEnv := result1.tagEnv',
                               nextLoc := result1.nextLoc',
                               nextTag := result1.nextTag',
                               pureCtx := true } : TypeContext).pureCtx = true
                              := by simp_all
                  have IH2 := IH fuel' hfuel
                    { pc := ctx.pc,
                      memEnv := result1.memEnv',
                      varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
                      tagEnv := result1.tagEnv',
                      nextLoc := result1.nextLoc',
                      nextTag := result1.nextTag',
                      pureCtx := true }
                    e2 pe2 result2 h2' C' h4
                  unfold preservesTypestate at IH2
                  rcases IH2 with ⟨H8, H9, H10⟩
                  -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
                  -- H1: ctx.memEnv.equiv result1.memEnv'
                  -- H8: result1.memEnv'.equiv result2.memEnv'
                  -- Goal: ctx.memEnv.equiv result.memEnv' where result.memEnv' = result2.memEnv'
                  have H_trans : ctx.memEnv.equiv result2.memEnv' := MemoryTypeEnv.equiv.trans ctx.memEnv result1.memEnv' result2.memEnv' H1 H8
                  simp_all [H_trans]
                  cases result; cases result1; cases result2; cases ctx; cases H; simp_all

        -- ================================================================
-- Helper lemmas for app case
-- ================================================================

-- Helper: applyPFnTClosure preserves typestate for regular closures
-- Regular closures call typecheckExpr with pureCtx=true, so by IH, typestate is preserved
private lemma applyPFnTClosure_regular_preserves_typestate
    (x : Name) (body : PExpr) (env : CapturedVarEnv)
    (st1 st2 : Typ) (p p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure (PFnTClosure.regular x body env) st1 st2 p p1 argEtyp argPoison argPred ctx result2 (fuel + 1) = Except.ok closureResult)
    (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  -- applyPFnTClosure.regular calls typecheckExpr ctx'' (PExpr.toExpr body) fuel
  -- where ctx'' has memEnv = result2.memEnv', tagEnv = result2.tagEnv', pureCtx = true
  -- By IH (with m = fuel < fuel + 1), the result preserves typestate relative to ctx''
  classical
  let argQt : QTyp := ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
  let envMap := VarTypeEnv.ofCaptured env
  let env' := VarTypeEnv.update envMap x argQt
  let ctx'' : TypeContext :=
    { ctx with pc := joinPoison p (joinPoison ctx.pc p1),
               memEnv := result2.memEnv',
               varEnv := env',
               tagEnv := result2.tagEnv',
               pureCtx := true,
               nextLoc := result2.nextLoc',
               nextTag := result2.nextTag' }
  have h_apply' := h_apply
  simp [applyPFnTClosure, argQt, envMap, env', ctx''] at h_apply'
  cases h_tc : typecheckExpr ctx'' (PExpr.toExpr body) fuel with
  | error err =>
      rw [h_tc] at h_apply'
      simp [bind, Except.bind] at h_apply'
  | ok result3 =>
      have h_apply'' := h_apply'
      rw [h_tc] at h_apply''
      simp [bind, Except.bind] at h_apply''
      cases hq : result3.qualType with
      | mk etyp3 poison3 pred3 =>
          simp [hq] at h_apply''
          cases hsub : isSubtype st2 (QTyp.mk etyp3 poison3 pred3) with
          | true =>
              simp [hsub, pure, Except.pure] at h_apply''
              have h_eq : closureResult = result3 := by
                simpa [Except.ok.injEq] using h_apply''.symm
              have h_pres :
                  preservesTypestate ctx''.memEnv ctx''.tagEnv ctx''.nextLoc ctx''.nextTag result3 :=
                IH fuel (by linarith) ctx'' (PExpr.toExpr body) body result3
                  (by simpa using (toExpr_toPExpr body)) (by simp [ctx'']) h_tc
              simpa [ctx'', h_eq] using h_pres
          | false =>
              simp [hsub, pure, Except.pure] at h_apply''
              cases h_apply''

-- Helper: applyPFnTClosure preserves typestate for extern closures
-- Extern closures directly return result2's memEnv', tagEnv', etc.
private lemma applyPFnTClosure_extern_preserves_typestate
    (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
    (_st1 _st2 : Typ) (_p _p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure (PFnTClosure.extern x retSpec capturedEnv) _st1 _st2 _p _p1 argEtyp argPoison argPred ctx result2 (fuel + 1) = Except.ok closureResult) :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  -- For extern closures, all branches return:
  -- memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextTag' := result2.nextTag'
  -- For nextLoc': it's either preserved or comes from returnSpecToQTyp which preserves it for basic types
  unfold preservesTypestate
  -- Case split on retSpec
  cases retSpec with
  | simple typ poison pred =>
      simp only [applyPFnTClosure, bind, Except.bind] at h_apply
      cases h_ret : returnSpecToQTyp typ poison pred
          (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
          result2.nextLoc' with
      | error err =>
          simp [h_ret] at h_apply
      | ok retPair =>
          cases retPair with
          | mk retQt nextLoc' =>
              simp [h_ret] at h_apply
              simp only [pure, Except.pure, Except.ok.injEq] at h_apply
              cases h_apply
              refine ⟨MemoryTypeEnv.equiv.refl _, rfl, ?_, rfl⟩
              have h_nextLoc : nextLoc' = result2.nextLoc' := by
                cases typ with
                | int =>
                    cases h_pred : attachVarEnvToPredicate pred
                        (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) with
                    | error err =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                    | ok pred' =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                        cases h_ret with
                        | _ _ hright => exact hright.symm
                | bool =>
                    cases h_pred : attachVarEnvToPredicate pred
                        (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) with
                    | error err =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                    | ok pred' =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                        cases h_ret with
                        | _ _ hright => exact hright.symm
                | unit =>
                    cases h_pred : attachVarEnvToPredicate pred
                        (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) with
                    | error err =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                    | ok pred' =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                        cases h_ret with
                        | _ _ hright => exact hright.symm
                | string =>
                    cases h_pred : attachVarEnvToPredicate pred
                        (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) with
                    | error err =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                    | ok pred' =>
                        simp [returnSpecToQTyp, h_pred] at h_ret
                        cases h_ret with
                        | _ _ hright => exact hright.symm
                | ref _ =>
                    simp [returnSpecToQTyp] at h_ret
                    cases h_ret
                | arrow _ _ =>
                    simp [returnSpecToQTyp] at h_ret
                    cases h_ret
              exact h_nextLoc.symm
  | nestedFn _ _ _ _ =>
    simp only [applyPFnTClosure, pure, Except.pure, Except.ok.injEq] at h_apply
    cases h_apply
    exact ⟨MemoryTypeEnv.equiv.refl _, rfl, rfl, rfl⟩
  | nestedPfn _ _ _ =>
    simp only [applyPFnTClosure, pure, Except.pure, Except.ok.injEq] at h_apply
    cases h_apply
    exact ⟨MemoryTypeEnv.equiv.refl _, rfl, rfl, rfl⟩

-- Helper: applyPFnTClosure preserves typestate (combines regular and extern cases)
private lemma applyPFnTClosure_preserves_typestate
    (tcl : PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 (fuel + 1) = Except.ok closureResult)
    (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  cases tcl with
  | regular x body env =>
    exact applyPFnTClosure_regular_preserves_typestate x body env st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel closureResult h_apply IH
  | extern x retSpec capturedEnv =>
    exact applyPFnTClosure_extern_preserves_typestate x retSpec capturedEnv st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel closureResult h_apply

-- Helper: applyPFnTClosure preserves typestate at an arbitrary fuel (including 0)
private lemma applyPFnTClosure_preserves_typestate_at_fuel
    (tcl : PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel = Except.ok closureResult)
    (IH : ∀ m < fuel, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  cases fuel with
  | zero =>
    -- applyPFnTClosure ... 0 always errors
    simp [applyPFnTClosure] at h_apply
  | succ fuel' =>
    -- Use the (+1)-fuel lemma
    have IH' :
        ∀ m < fuel' + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
          e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
          preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
      intro m hm ctx' e pe result h_pe h_pure h_tc
      exact IH m (by omega) ctx' e pe result h_pe h_pure h_tc
    exact
      applyPFnTClosure_preserves_typestate tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel'
        closureResult (by simpa using h_apply) IH'

-- Helper: List.mapM of applyPFnTClosure preserves typestate for all results
private lemma mapM_applyPFnTClosure_preserves_typestate
    (tcls : List PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (results : List TypeResult)
    (h_map : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel) tcls = Except.ok results)
    (IH : ∀ m < fuel, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
    ∀ r ∈ results, preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' r := by
  -- Use List.mapM_Except_preserves_property from TypeSafety
  refine List.mapM_Except_preserves_property tcls
    (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel)
    (fun r => preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' r)
    (fun tcl r h_ok =>
      applyPFnTClosure_preserves_typestate_at_fuel
        tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel r h_ok IH)
    results h_map

-- Helper: max is idempotent (using Nat.max_self from mathlib)

-- Helper: joinTypeResults preserves all 4 typestate components
-- Given that all inputs have equivalent memEnv and equal tagEnv/nextLoc/nextTag,
-- the output also has equivalent memEnv and equal tagEnv/nextLoc/nextTag.
--
-- Proof sketch:
-- joinTypeResults folds over restResults using:
-- - joinMemEnvs for memEnv' (preserves equivalence via joinMemEnv_idempotent)
-- - joinTagEnvs for tagEnv' (when all inputs equal, result equals via joinTagEnvs_idempotent)
-- - max for nextLoc' and nextTag' (max n n = n via Nat.max_self)
--
-- Using List.foldlM_Except_preserves_property with a combined property P capturing all 4 invariants:
-- P(acc) = m.equiv acc.memEnv ∧ t = acc.tagEnv ∧ nl = acc.nextLoc ∧ nt = acc.nextTag
--
-- Base case: P(initAcc) holds by h_first_* hypotheses
-- Inductive case: foldFn preserves P using joinMemEnv_idempotent, joinTagEnvs_idempotent, Nat.max_self
private lemma joinTypeResults_preserves_typestate
    (_tctx : TypeContext) (m : MemoryTypeEnv) (t : TagEnv) (nl : Loc) (nt : Tag)
    (firstResult : TypeResult) (restResults : List TypeResult) (finalResult : TypeResult)
    (_h_all : ∀ r ∈ (firstResult :: restResults), preservesTypestate m t nl nt r)
    (_h_join : joinTypeResults _tctx firstResult restResults = Except.ok finalResult) :
    preservesTypestate m t nl nt finalResult := by
  classical
  have h_first : preservesTypestate m t nl nt firstResult := _h_all firstResult (by simp)
  have h_rest : ∀ r ∈ restResults, preservesTypestate m t nl nt r := by
    intro r hr
    exact _h_all r (by simp [hr])

  -- Invert `joinTypeResults` to expose the join fold.
  cases h_qt : firstResult.qualType with
  | mk firstEtyp firstP firstPred =>
    -- Match the accumulator and fold function used in `joinTypeResults`.
    let initAcc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag :=
      (firstEtyp, firstResult.memEnv', firstP, firstPred, firstResult.tagEnv', firstResult.nextLoc', firstResult.nextTag')
    let joinFn :
        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) →
          TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) :=
      fun acc result => do
        let ⟨resEtyp, resPoison, resPred⟩ := result.qualType
        let (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag) := acc
        pure
          (joinETyps joinedEtyp resEtyp joinedPoison resPoison,
            joinMemEnvs joinedMemEnv result.memEnv',
            joinPoison joinedPoison resPoison,
            joinPredicates joinedPred resPred,
            joinTagEnvs joinedTagEnv result.tagEnv',
            max maxNextLoc result.nextLoc',
            max maxNextTag result.nextTag')
    let P : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) → Prop
      | (_et, mem, _p, _pred, tagEnv, nextLoc, nextTag) =>
          m.equiv mem ∧ t = tagEnv ∧ nl = nextLoc ∧ nt = nextTag
    let Q : TypeResult → Prop := fun r => preservesTypestate m t nl nt r

    have h_init : P initAcc := by
      simpa [P, Q, initAcc, preservesTypestate] using h_first

    have h_all_rest : ∀ r ∈ restResults, Q r := by
      intro r hr
      exact h_rest r hr

    have h_step :
        ∀ (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) (x : TypeResult),
          P acc →
          Q x →
          (∀ acc', joinFn acc x = Except.ok acc' → P acc') := by
      intro acc x hPacc hQx acc' h_fx
      rcases acc with ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag⟩
      have hP' : m.equiv joinedMemEnv ∧ t = joinedTagEnv ∧ nl = maxNextLoc ∧ nt = maxNextTag := by
        simpa [P] using hPacc
      have hQ' : m.equiv x.memEnv' ∧ t = x.tagEnv' ∧ nl = x.nextLoc' ∧ nt = x.nextTag' := by
        simpa [Q, preservesTypestate] using hQx

      cases h_qt_x : x.qualType with
      | mk resEtyp resPoison resPred =>
        have h_fx' :
            (joinETyps joinedEtyp resEtyp joinedPoison resPoison,
              joinMemEnvs joinedMemEnv x.memEnv',
              joinPoison joinedPoison resPoison,
              joinPredicates joinedPred resPred,
              joinTagEnvs joinedTagEnv x.tagEnv',
              max maxNextLoc x.nextLoc',
              max maxNextTag x.nextTag') =
              acc' := by
          simpa [joinFn, h_qt_x, pure, Except.pure] using h_fx

        -- Rewrite the goal to the tuple computed by `joinFn` and discharge the invariant.
        rw [← h_fx']
        simp [P]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact joinMemEnv_idempotent m joinedMemEnv x.memEnv' hP'.1 hQ'.1
        · rw [← hP'.2.1, ← hQ'.2.1]
          rw [joinTagEnvs_idempotent t]
        · rw [← hP'.2.2.1, ← hQ'.2.2.1]
          simp
        · rw [← hP'.2.2.2, ← hQ'.2.2.2]
          simp

    -- Now unfold `joinTypeResults` in `Except.bind` form and invert the successful run.
    have h_join' := _h_join
    simp [joinTypeResults, h_qt, bind, pure, Except.pure] at h_join'

    -- Step 1: signature check fold must succeed
    rcases Except.bind_eq_ok
        (x :=
          List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature firstEtyp resEtyp = false then
                  throw
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr firstEtyp) ++
                        toString " vs " ++
                      toString (repr resEtyp))
                else Except.ok ()) () restResults)
        (f := fun _ =>
          Except.bind (List.foldlM joinFn initAcc restResults) (fun joined =>
            Except.ok
              { qualType :=
                  { etyp := joined.1, poison := joinPoison _tctx.pc joined.2.2.1,
                    pred :=
                      match joined.1 with
                      | ETyp.arrow _ _ _ _ => Predicate.noPred
                      | ETyp.parrow _ _ _ _ => Predicate.noPred
                      | _ => joined.2.2.2.1 },
                memEnv' := joined.2.1, tagEnv' := joined.2.2.2.2.1, nextLoc' := joined.2.2.2.2.2.1,
                nextTag' := joined.2.2.2.2.2.2 }))
        (b := finalResult) h_join' with ⟨_u, _h_sig_ok, h_after_sig⟩

    -- Step 2: join fold must succeed, yielding the final record
    rcases Except.bind_eq_ok (x := List.foldlM joinFn initAcc restResults)
        (f := fun joined =>
          Except.ok
            { qualType :=
                { etyp := joined.1, poison := joinPoison _tctx.pc joined.2.2.1,
                  pred :=
                    match joined.1 with
                    | ETyp.arrow _ _ _ _ => Predicate.noPred
                    | ETyp.parrow _ _ _ _ => Predicate.noPred
                    | _ => joined.2.2.2.1 },
              memEnv' := joined.2.1, tagEnv' := joined.2.2.2.2.1, nextLoc' := joined.2.2.2.2.2.1,
              nextTag' := joined.2.2.2.2.2.2 })
        (b := finalResult) h_after_sig with ⟨joined, h_fold, h_ok⟩

    rcases joined with ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag⟩

    have h_ret := by
      injection h_ok

    have hP_joined :
        m.equiv joinedMemEnv ∧ t = joinedTagEnv ∧ nl = maxNextLoc ∧ nt = maxNextTag := by
      have hP_acc :
          P (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag) :=
        List.foldlM_Except_preserves_property_of_forall_mem
          restResults initAcc joinFn P Q h_init h_all_rest h_step
          (joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag) (by
            simpa [joinFn] using h_fold)
      simpa [P] using hP_acc

    have h_memEq : finalResult.memEnv' = joinedMemEnv := by
      have : joinedMemEnv = finalResult.memEnv' := by
        simpa using congrArg TypeResult.memEnv' h_ret
      exact this.symm
    have h_tagEq : finalResult.tagEnv' = joinedTagEnv := by
      have : joinedTagEnv = finalResult.tagEnv' := by
        simpa using congrArg TypeResult.tagEnv' h_ret
      exact this.symm
    have h_locEq : finalResult.nextLoc' = maxNextLoc := by
      have : maxNextLoc = finalResult.nextLoc' := by
        simpa using congrArg TypeResult.nextLoc' h_ret
      exact this.symm
    have h_tagEq' : finalResult.nextTag' = maxNextTag := by
      have : maxNextTag = finalResult.nextTag' := by
        simpa using congrArg TypeResult.nextTag' h_ret
      exact this.symm

    -- Conclude typestate preservation for the returned `TypeResult`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [h_memEq] using hP_joined.1
    · simpa [h_tagEq] using hP_joined.2.1
    · simpa [h_locEq] using hP_joined.2.2.1
    · simpa [h_tagEq'] using hP_joined.2.2.2

-- ================================================================
-- Private lemma for app case
-- ================================================================

private lemma typecheck_app_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.app e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.app e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result) :
  preservesTypestate ctx.memEnv ctx.tagEnv ctx.nextLoc ctx.nextTag result := by
  unfold preservesTypestate
  -- Unfold to typecheckApp
  simp only [typecheckExpr] at H
  cases fuel with
  | zero => simp [typecheckApp] at H
  | succ fuel' =>
    simp only [typecheckApp, bind, Except.bind] at H
    -- Extract pe1, pe2 from P
    simp [Expr.toPExpr, Expr.toPExpr?] at P
    cases h_pe1 : Expr.toPExpr? e1 with
    | none =>
        simp [Expr.toPExpr, Expr.toPExpr?, h_pe1, pure, Except.pure] at P
    | some pe1 =>
        have h_pe1' : e1.toPExpr = Except.ok pe1 := by
          simp [Expr.toPExpr, h_pe1, pure, Except.pure]
        simp [Expr.toPExpr, Expr.toPExpr?, h_pe1, pure, Except.pure] at P
        cases h_pe2 : Expr.toPExpr? e2 with
        | none =>
          simp [Expr.toPExpr, Expr.toPExpr?, h_pe2, pure, Except.pure] at P
        | some pe2 =>
          have h_pe2' : e2.toPExpr = Except.ok pe2 := by
            simp [Expr.toPExpr, h_pe2, pure, Except.pure]
          simp [Expr.toPExpr, Expr.toPExpr?, h_pe2, pure, Except.pure] at P
          -- Step 1 (re-ordered): typecheck e2 first
          cases h_tc2 : typecheckExpr ctx e2 fuel' with
          | error err =>
              -- Contradiction: typechecking fails but H claims success.
              have hbad : False := by
                have H' := H
                simp [h_tc2] at H'
              exact False.elim hbad
          | ok result2 =>
              simp [h_tc2] at H
              have hfuel : fuel' < fuel' + 1 + 1 := by omega
              have IH2 := IH fuel' hfuel ctx e2 pe2 result2 h_pe2' C h_tc2
              unfold preservesTypestate at IH2
              obtain ⟨H2_memEnv, H2_tagEnv, H2_nextLoc, H2_nextTag⟩ := IH2

              -- Step 2 (re-ordered): typecheck e1 in the post-context of e2
              let ctx' : TypeContext :=
                { pc := ctx.pc, memEnv := result2.memEnv', varEnv := ctx.varEnv,
                  tagEnv := result2.tagEnv', nextLoc := result2.nextLoc',
                  nextTag := result2.nextTag', pureCtx := ctx.pureCtx }
              have C' : ctx'.pureCtx = true := C
              cases h_tc1 : typecheckExpr ctx' e1 fuel' with
              | error err =>
                  have h_tc1' := by simpa [ctx'] using h_tc1
                  have hbad : False := by
                    have H' := H
                    simp [h_tc1'] at H'
                    cases hq : result2.qualType <;> simp [hq] at H'
                  exact False.elim hbad
              | ok result1 =>
                  have h_tc1' := by simpa [ctx'] using h_tc1
                  simp [h_tc1'] at H
                  -- Case split on result1.qualType.etyp
                  match h_qt1 : result1.qualType with
                  | ⟨etyp1, p1, _pred1⟩ =>
                    simp only [h_qt1] at H
                    match etyp1 with
                    | .arrow _ _ _ _ =>
                        -- Arrow in pure context throws error
                        have hbad : False := by
                          have H' := H
                          simp [C] at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad
                    | .parrow st1 st2 p tcls =>
                        simp only at H
                        cases h_empty : tcls.isEmpty with
                        | true =>
                            have h_nil : tcls = [] := by rwa [List.isEmpty_iff] at h_empty
                            have hbad : False := by
                              have H' := H
                              simp [h_nil] at H'
                              cases hq : result2.qualType <;> simp [hq] at H'
                            exact False.elim hbad
                        | false =>
                            have h_nonempty : tcls ≠ [] := by
                              intro h_nil
                              simp [h_nil] at h_empty
                            simp only [h_nonempty, ↓reduceIte, pure, Except.pure] at H

                            -- Transitivity bases: e2 preserves typestate from ctx to result2
                            have H_memEnv_trans : ctx.memEnv.equiv result2.memEnv' := H2_memEnv
                            have H_tagEnv_trans : ctx.tagEnv = result2.tagEnv' := H2_tagEnv
                            have H_nextLoc_trans : ctx.nextLoc = result2.nextLoc' := H2_nextLoc
                            have H_nextTag_trans : ctx.nextTag = result2.nextTag' := H2_nextTag

                            -- Subtype check: if isSubtype st1 result2.qualType = false then error else ...
                            cases h_sub : isSubtype st1 result2.qualType with
                            | true =>
                                simp only [h_sub, ↓reduceIte] at H
                                -- Destruct result2.qualType for the inner match
                                cases h_qt2 : result2.qualType with
                                | mk etyp2 p2 pred2 =>
                                    simp only [h_qt2] at H
                                    -- Step 3: mapM applyPFnTClosure
                                    cases h_map : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls with
                                    | error _ =>
                                        simp [h_map] at H
                                    | ok closureResults =>
                                        simp only [h_map] at H
                                        match h_res : closureResults with
                                        | [] =>
                                            -- Empty list: H becomes throw ... = Except.ok, contradiction
                                            simp only [h_res, Bool.true_eq_false, ↓reduceIte] at H
                                            cases H
                                        | firstResult :: restResults =>
                                            simp only [h_res] at H
                                            -- Use mapM helper: all results preserve typestate relative to result2
                                            have IH_lower : ∀ m < fuel', ∀ (ctx' : TypeContext) (e : Expr) (pe' : PExpr) (res : TypeResult),
                                                e.toPExpr = Except.ok pe' → ctx'.pureCtx = true → typecheckExpr ctx' e m = Except.ok res →
                                                preservesTypestate ctx'.memEnv ctx'.tagEnv ctx'.nextLoc ctx'.nextTag res := by
                                              intro m hm ctx'' e' pe' res h_pe' h_ctx h_tc
                                              exact IH m (by omega) ctx'' e' pe' res h_pe' h_ctx h_tc
                                            -- h_map was specialized by the match, so closureResults = firstResult :: restResults
                                            have h_map' : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls =
                                                Except.ok (firstResult :: restResults) := h_map
                                            have h_all := mapM_applyPFnTClosure_preserves_typestate tcls st1 st2 p p1 etyp2 p2 pred2
                                                ctx result2 fuel' (firstResult :: restResults) h_map' IH_lower
                                            -- Use joinTypeResults_preserves_typestate (strengthened version)
                                            have h_join_result := joinTypeResults_preserves_typestate ctx
                                                result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag'
                                                firstResult restResults result
                                                (by
                                                  intro r h_mem
                                                  exact h_all r h_mem)
                                                H
                                            obtain ⟨h_final_memEnv, h_final_tagEnv, h_final_nextLoc, h_final_nextTag⟩ := h_join_result
                                            have H_final_memEnv_trans : ctx.memEnv.equiv result.memEnv' :=
                                              MemoryTypeEnv.equiv.trans ctx.memEnv result2.memEnv' result.memEnv' H_memEnv_trans h_final_memEnv
                                            refine ⟨H_final_memEnv_trans, ?_, ?_, ?_⟩
                                            · rw [H_tagEnv_trans]; exact h_final_tagEnv
                                            · rw [H_nextLoc_trans]; exact h_final_nextLoc
                                            · rw [H_nextTag_trans]; exact h_final_nextTag
                            | false =>
                                -- isSubtype fails: H becomes Except.error = Except.ok, contradiction
                                simp only [h_sub, ↓reduceIte] at H
                                cases h_qt2 : result2.qualType with
                                | mk _ _ _ =>
                                    simp only [h_qt2] at H
                                    exact absurd H (by simp)
                    | .int =>
                        have hbad : False := by
                          have H' := H
                          simp at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad
                    | .bool =>
                        have hbad : False := by
                          have H' := H
                          simp at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad
                    | .unit =>
                        have hbad : False := by
                          have H' := H
                          simp at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad
                    | .string =>
                        have hbad : False := by
                          have H' := H
                          simp at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad
                    | .ref _ _ =>
                        have hbad : False := by
                          have H' := H
                          simp at H'
                          cases hq : result2.qualType <;> simp [hq] at H'
                        exact False.elim hbad

  theorem typecheck_PExpr_preserves_typestate : TypecheckPExprPreservesTypestate := by
    unfold TypecheckPExprPreservesTypestate
    intro fuel
     -- strong induction on `fuel`
    induction fuel using Nat.strong_induction_on with
    | _ n IH =>
      intro ctx e pe result P C H
      cases n with
      | zero =>
        simp [typecheckExpr] at H
      | succ fuel =>
        cases e with
        | unit =>
          apply typecheck_unit_preserves_typestate ctx pe result fuel C P H
        | str s =>
          apply typecheck_str_preserves_typestate ctx pe result fuel s C P H
        | num n =>
          apply typecheck_num_preserves_typestate ctx pe result fuel n C P H
        | bool b =>
          apply typecheck_bool_preserves_typestate ctx pe result fuel b C P H
        | var name =>
          apply typecheck_var_preserves_typestate ctx pe result fuel name C P H
        | deref e1 =>
          apply typecheck_deref_preserves_typestate ctx pe result fuel e1 C P H IH
        | ite e1 e2 e3  =>
          apply typecheck_ite_preserves_typestate ctx pe result fuel e1 e2 e3 C P H IH
        | op e1 op e2 =>
          apply typecheck_op_preserves_typestate ctx pe result fuel e1 op e2 C P H IH
        | unaryop op e =>
          apply typecheck_unaryop_preserves_typestate ctx pe result fuel op e C P H IH
        | vlet x e1 e2 =>
          apply typecheck_vlet_preserves_typestate ctx pe result fuel x e1 e2 C P H IH
        | app e1 e2 =>
          apply typecheck_app_preserves_typestate ctx pe result fuel e1 e2 C P H IH
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
        | printInt _
        | externVal _ _ _
        | externFn _ _ _ _
        | externPfn _ _ _
          =>
          contradiction
