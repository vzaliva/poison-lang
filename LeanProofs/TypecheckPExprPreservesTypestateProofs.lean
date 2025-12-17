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
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
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

-- Private lemma for unit case
private lemma typecheck_unit_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat)
  (_C : ctx.pureCtx = true) (_P : Expr.unit.toPExpr = Except.ok pe) (H : typecheckExpr ctx Expr.unit (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for str case
private lemma typecheck_str_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (s : String)
  (_C : ctx.pureCtx = true) (_P : (Expr.str s).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.str s) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for num case
private lemma typecheck_num_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (n : Int)
  (_C : ctx.pureCtx = true) (_P : (Expr.num n).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.num n) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for bool case
private lemma typecheck_bool_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (b : Bool)
  (_C : ctx.pureCtx = true) (_P : (Expr.bool b).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.bool b) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for var case
private lemma typecheck_var_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (name : Name)
  (C : ctx.pureCtx = true) (_P : (Expr.var name).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.var name) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
      | guardOnly tag =>
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
      | noPred =>
        -- No predicate case: preserves environment
        simp_all [typecheckVar, h0, h1, h3, pure, Except.pure]
        cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for deref case
private lemma typecheck_deref_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr)
  (C : ctx.pureCtx = true) (P : e1.deref.toPExpr = Except.ok pe) (H : typecheckExpr ctx e1.deref (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero | succ fuel') <;>
    simp [typecheckDeref, bind, Except.bind] at H
  cases h0: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    -- use IH
    simp [Expr.toPExpr, Functor.map, Except.map] at P
    cases h1: e1.toPExpr with
    | error err =>
      simp_all
    | ok pe1 =>
      simp [h1] at P
      have hfuel : fuel' < fuel' + 1 + 1 := by linarith
      specialize IH fuel' hfuel ctx e1 pe1 result1 h1 C h0
      rcases IH with ⟨H1, H2, H3, H4⟩
      simp_all
      cases h2: result1.qualType with
      | mk etyp poison _pred =>
        simp_all
        cases h3: etyp with
        | ref t l =>
          simp_all
          -- l is a LocSet, not a Loc
          -- typecheckDeref uses LocSet.foldM to iterate over locations
          -- Handle the isEmpty check first
          cases h_empty : l.isEmpty with
          | true =>
            -- Empty locset: throws error (contradiction with success)
            have h_eq_empty : l = ∅ := by
              rw [ExtTreeSet.isEmpty_iff] at h_empty
              exact h_empty
            simp [typecheckDeref, h_empty, h_eq_empty] at H
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
              simp at H
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
        | _ => simp_all

-- Private lemma for ite case
private lemma typecheck_ite_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 e3 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.ite e2 e3).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.ite e2 e3) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckIf, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with| error err | ok pe1 ) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h3: e2.toPExpr with | error err | ok pe2) <;> simp [h3] at P
  (cases h4: e3.toPExpr with | error err | ok pe3) <;> simp [h4] at P

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
      have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h5
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
                        e2 pe2 result2 h3 C' h9
                    have C'' : ({ pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                  tagEnv := result1.tagEnv',
                                  nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                            := by simp_all
                    have IH3 := IH fuel' hfuel
                        { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv',
                          nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                        e3 pe3 result3 h4 C'' h11
                    rcases IH2 with ⟨H14, H15, H16⟩
                    rcases IH3 with ⟨H17, H18, H19⟩
                    -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv' ∧ result1.memEnv'.equiv result3.memEnv'
                    -- Goal: memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv')
                    -- Use joinMemEnv_idempotent with m=result1.memEnv', m1=result2.memEnv', m2=result3.memEnv'
                    have H_join : result1.memEnv'.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                      joinMemEnv_idempotent result1.memEnv' result2.memEnv' result3.memEnv' H14 H17
                    have H_trans : ctx.memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                      Std.HashMap.Equiv.trans H1 H_join
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
                        tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
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
                        tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
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
                    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h5
                    rcases IH1 with ⟨H1, H2, H3, H4⟩
                    have C' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                 tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
                                 nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true } : TypeContext).pureCtx = true
                            := by simp
                    have IH2 :=
                      IH fuel' hfuel { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                       tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
                                       nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true }
                                       e2 pe2 result2 h3 C' h9

                    have C'' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                       tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
                                       nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                            := by simp
                    have IH3 :=
                      IH fuel' hfuel
                        { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                          tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
                          nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                        e3 pe3 result3 h4 C'' h11
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
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckOp, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
  cases h3: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h3] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h3
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
                      e2 pe2 result2 h2 C' h5
            rcases IH2 with ⟨H8, H9, H10⟩
            simp_all
            cases result; cases result1; cases result2; cases ctx; cases H; simp_all
            -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
            apply Std.HashMap.Equiv.trans H1 H8
          | none =>
            simp_all

-- Private lemma for unaryop case
private lemma typecheck_unaryop_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (op : UnaryOp) (e : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.unaryop op e).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckUnaryOp, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
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
        specialize IH fuel' hfuel ctx e pe1 result1 h1 C h2
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
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckVlet, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
  cases h3: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h3] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h3
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
            e2 pe2 result2 h2 C' h4
          rcases IH2 with ⟨H8, H9, H10⟩
          simp_all
          cases result; cases result1; cases result2; cases ctx; cases H; simp_all
          -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
          apply Std.HashMap.Equiv.trans H1 H8

-- ================================================================
-- Helper lemmas for app case
-- ================================================================

-- Property that a TypeResult preserves typestate relative to a base memory environment
private def preservesTypestate (m : MemoryTypeEnv) (tagEnv : TagEnv) (nextLoc : Loc) (nextTag : Tag)
    (result : TypeResult) : Prop :=
  m.equiv result.memEnv' ∧ tagEnv = result.tagEnv' ∧ nextLoc = result.nextLoc' ∧ nextTag = result.nextTag'

-- Helper: applyPFnTClosure preserves typestate for regular closures
-- Regular closures call typecheckExpr with pureCtx=true, so by IH, typestate is preserved
private lemma applyPFnTClosure_regular_preserves_typestate
    (x : Name) (body : PExpr) (env : VarTypeEnv)
    (st1 st2 : Typ) (p p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure (PFnTClosure.regular x body env) st1 st2 p p1 argEtyp argPoison argPred ctx result2 (fuel + 1) = Except.ok closureResult)
    (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  -- applyPFnTClosure.regular calls typecheckExpr ctx'' (PExpr.toExpr body) fuel
  -- where ctx'' has memEnv = result2.memEnv', tagEnv = result2.tagEnv', pureCtx = true
  -- By IH (with m = fuel < fuel + 1), the result preserves typestate relative to ctx''
  sorry

-- Helper: applyPFnTClosure preserves typestate for extern closures
-- Extern closures directly return result2's memEnv', tagEnv', etc.
private lemma applyPFnTClosure_extern_preserves_typestate
    (x : Name) (retSpec : ExternReturn) (capturedEnv : VarTypeEnv)
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
    cases h_ret : returnSpecToQTyp typ poison pred (VarTypeEnv.update capturedEnv x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) result2.nextLoc' with
    | error err => simp [h_ret] at h_apply
    | ok retPair =>
      simp [h_ret] at h_apply
      simp only [pure, Except.pure, Except.ok.injEq] at h_apply
      cases h_apply
      refine ⟨Std.HashMap.Equiv.refl _, rfl, ?_, rfl⟩
      -- For nextLoc': returnSpecToQTyp for basic types preserves it
      -- Need a lemma showing returnSpecToQTyp preserves nextLoc for basic types
      sorry
  | nestedFn _ _ _ _ =>
    simp only [applyPFnTClosure, pure, Except.pure, Except.ok.injEq] at h_apply
    cases h_apply
    exact ⟨Std.HashMap.Equiv.refl _, rfl, rfl, rfl⟩
  | nestedPfn _ _ _ =>
    simp only [applyPFnTClosure, pure, Except.pure, Except.ok.injEq] at h_apply
    cases h_apply
    exact ⟨Std.HashMap.Equiv.refl _, rfl, rfl, rfl⟩

-- Helper: applyPFnTClosure preserves typestate (combines regular and extern cases)
private lemma applyPFnTClosure_preserves_typestate
    (tcl : PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (closureResult : TypeResult)
    (h_apply : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 (fuel + 1) = Except.ok closureResult)
    (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
    preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' closureResult := by
  cases tcl with
  | regular x body env =>
    exact applyPFnTClosure_regular_preserves_typestate x body env st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel closureResult h_apply IH
  | extern x retSpec capturedEnv =>
    exact applyPFnTClosure_extern_preserves_typestate x retSpec capturedEnv st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel closureResult h_apply

-- Helper: List.mapM of applyPFnTClosure preserves typestate for all results
private lemma mapM_applyPFnTClosure_preserves_typestate
    (tcls : List PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (fuel : Nat) (results : List TypeResult)
    (h_map : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 fuel) tcls = Except.ok results)
    (IH : ∀ m < fuel, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
      e.toPExpr = Except.ok pe → ctx.pureCtx = true → typecheckExpr ctx e m = Except.ok result →
      ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
    ∀ r ∈ results, preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' r := by
  -- Use List.mapM_Except_preserves_property
  -- Each tcl in tcls produces a result that preserves typestate by applyPFnTClosure_preserves_typestate
  sorry

-- Helper: joinTypeResults preserves memEnv equivalence
-- If m.equiv firstResult.memEnv' and ∀ r ∈ restResults, m.equiv r.memEnv',
-- then m.equiv finalResult.memEnv'
private lemma joinTypeResults_preserves_equiv (tctx : TypeContext) (m : MemoryTypeEnv)
    (firstResult : TypeResult) (restResults : List TypeResult) (finalResult : TypeResult)
    (h_first : m.equiv firstResult.memEnv')
    (h_rest : ∀ r ∈ restResults, m.equiv r.memEnv')
    (h_join : joinTypeResults tctx firstResult restResults = Except.ok finalResult) :
    m.equiv finalResult.memEnv' := by
  -- joinTypeResults folds over restResults using joinMemEnvs
  -- Starting from firstResult.memEnv' (equiv to m) and joining with each r.memEnv' (all equiv to m)
  -- By joinMemEnv_idempotent, the result is equiv to m
  sorry

-- Helper: joinTypeResults preserves all 4 typestate components
-- This is a stronger version that we use in the main proof
private lemma joinTypeResults_preserves_typestate (tctx : TypeContext)
    (firstResult : TypeResult) (restResults : List TypeResult) (finalResult : TypeResult)
    (h_first : preservesTypestate firstResult.memEnv' firstResult.tagEnv' firstResult.nextLoc' firstResult.nextTag' firstResult)
    (h_rest : ∀ r ∈ restResults, preservesTypestate firstResult.memEnv' firstResult.tagEnv' firstResult.nextLoc' firstResult.nextTag' r)
    (h_join : joinTypeResults tctx firstResult restResults = Except.ok finalResult) :
    preservesTypestate firstResult.memEnv' firstResult.tagEnv' firstResult.nextLoc' firstResult.nextTag' finalResult := by
  -- The proof requires showing that joinTypeResults preserves equivalence for memEnv
  -- and that tagEnv/nextLoc/nextTag are handled by the join (taking max/join)
  sorry

-- ================================================================
-- Private lemma for app case
-- ================================================================

private lemma typecheck_app_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.app e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.app e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  -- Unfold to typecheckApp
  simp only [typecheckExpr] at H
  cases fuel with
  | zero => simp [typecheckApp] at H
  | succ fuel' =>
    simp only [typecheckApp, bind, Except.bind] at H
    -- Extract pe1, pe2 from P
    simp only [Expr.toPExpr, Functor.map, Except.map] at P
    cases h_pe1 : e1.toPExpr with
    | error _ => simp [h_pe1, Seq.seq, Except.bind] at P
    | ok pe1 =>
      simp [h_pe1, Seq.seq, Except.bind] at P
      cases h_pe2 : e2.toPExpr with
      | error _ => simp [h_pe2, Except.map] at P
      | ok pe2 =>
        simp [h_pe2] at P
        -- Step 1: typecheck e1
        cases h_tc1 : typecheckExpr ctx e1 fuel' with
        | error _ => simp [h_tc1] at H
        | ok result1 =>
          simp [h_tc1] at H
          have hfuel : fuel' < fuel' + 1 + 1 := by omega
          have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h_pe1 C h_tc1
          obtain ⟨H1_memEnv, H1_tagEnv, H1_nextLoc, H1_nextTag⟩ := IH1
          -- Case split on result1.qualType.etyp
          match h_qt1 : result1.qualType with
          | ⟨etyp1, p1, _pred1⟩ =>
            simp only [h_qt1] at H
            match etyp1 with
            | .arrow _ _ _ _ =>
              -- Arrow in pure context throws error
              simp [C] at H
            | .parrow st1 st2 p tcls =>
              simp only at H
              cases h_empty : tcls.isEmpty with
              | true =>
                have h_nil : tcls = [] := by rwa [List.isEmpty_iff] at h_empty
                simp [h_nil] at H
              | false =>
                have h_nonempty : tcls ≠ [] := by
                  intro h_nil
                  simp [h_nil] at h_empty
                simp only [h_nonempty, ↓reduceIte, pure, Except.pure] at H
                -- Step 2: typecheck e2 with updated context
                cases h_tc2 : typecheckExpr { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                               tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                               nextTag := result1.nextTag', pureCtx := ctx.pureCtx } e2 fuel' with
                | error _ => simp [h_tc2] at H
                | ok result2 =>
                  simp [h_tc2] at H
                  let ctx' : TypeContext := { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                               tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                                               nextTag := result1.nextTag', pureCtx := ctx.pureCtx }
                  have C' : ctx'.pureCtx = true := C
                  have IH2 := IH fuel' hfuel ctx' e2 pe2 result2 h_pe2 C' h_tc2
                  obtain ⟨H2_memEnv, H2_tagEnv, H2_nextLoc, H2_nextTag⟩ := IH2
                  -- Transitivity for all 4 components
                  have H_memEnv_trans : ctx.memEnv.equiv result2.memEnv' := Std.HashMap.Equiv.trans H1_memEnv H2_memEnv
                  have H_tagEnv_trans : ctx.tagEnv = result2.tagEnv' := by rw [H1_tagEnv]; exact H2_tagEnv
                  have H_nextLoc_trans : ctx.nextLoc = result2.nextLoc' := by rw [H1_nextLoc]; exact H2_nextLoc
                  have H_nextTag_trans : ctx.nextTag = result2.nextTag' := by rw [H1_nextTag]; exact H2_nextTag
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
                      | error _ => simp [h_map] at H
                      | ok closureResults =>
                        simp only [h_map] at H
                        match h_res : closureResults with
                        | [] =>
                          -- Empty list: H becomes throw ... = Except.ok, contradiction
                          simp only [h_res, Bool.true_eq_false, ↓reduceIte] at H
                          -- H : throw ... = Except.ok result is a contradiction (Except.error ≠ Except.ok)
                          cases H
                        | firstResult :: restResults =>
                          simp only [h_res] at H
                          -- Use mapM helper: all results preserve typestate relative to result2
                          have IH_lower : ∀ m < fuel', ∀ (ctx' : TypeContext) (e : Expr) (pe' : PExpr) (res : TypeResult),
                              e.toPExpr = Except.ok pe' → ctx'.pureCtx = true → typecheckExpr ctx' e m = Except.ok res →
                              ctx'.memEnv.equiv res.memEnv' ∧ ctx'.tagEnv = res.tagEnv' ∧ ctx'.nextLoc = res.nextLoc' ∧ ctx'.nextTag = res.nextTag' := by
                            intro m hm ctx'' e' pe' res h_pe' h_ctx h_tc
                            exact IH m (by omega) ctx'' e' pe' res h_pe' h_ctx h_tc
                          -- h_map was specialized by the match, so closureResults = firstResult :: restResults
                          have h_map' : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls = Except.ok (firstResult :: restResults) := h_map
                          have h_all := mapM_applyPFnTClosure_preserves_typestate tcls st1 st2 p p1 etyp2 p2 pred2
                              ctx result2 fuel' (firstResult :: restResults) h_map' IH_lower
                          -- All closure results preserve typestate relative to result2
                          have h_first_mem : firstResult ∈ (firstResult :: restResults) := by simp
                          have h_first := h_all firstResult h_first_mem
                          have h_rest : ∀ r ∈ restResults, preservesTypestate result2.memEnv' result2.tagEnv' result2.nextLoc' result2.nextTag' r := by
                            intro r h_mem
                            have : r ∈ (firstResult :: restResults) := by simp [h_mem]
                            exact h_all r this
                          -- Extract memEnv equivalences
                          have h_first_equiv : result2.memEnv'.equiv firstResult.memEnv' := h_first.1
                          have h_rest_equiv : ∀ r ∈ restResults, result2.memEnv'.equiv r.memEnv' := fun r h => (h_rest r h).1
                          -- Use joinTypeResults_preserves_equiv
                          have h_final : result2.memEnv'.equiv result.memEnv' :=
                            joinTypeResults_preserves_equiv ctx result2.memEnv' firstResult restResults result h_first_equiv h_rest_equiv H
                          -- Final transitivity
                          refine ⟨Std.HashMap.Equiv.trans H_memEnv_trans h_final, ?_, ?_, ?_⟩
                          -- For tagEnv, nextLoc, nextTag: they are joined in joinTypeResults
                          -- The property depends on how joinTypeResults handles these
                          -- Since all closure results have same tagEnv/nextLoc/nextTag as result2 (by h_first/h_rest),
                          -- and joinTypeResults takes max/join, the result should equal result2's values
                          all_goals sorry
                  | false =>
                    -- isSubtype fails: H becomes Except.error = Except.ok, contradiction
                    simp only [h_sub, ↓reduceIte] at H
                    cases h_qt2 : result2.qualType with
                    | mk _ _ _ =>
                      simp only [h_qt2] at H
                      exact absurd H (by simp)
            | .int | .bool | .unit | .string | .ref _ _ => simp at H

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
