-- Proofs for TypecheckPExprPreservesTypestate Property

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import LeanProofs.TypecheckPExprPreservesTypestate
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


open Std

-- set_option diagnostics true

set_option maxHeartbeats 2000000

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

/- TODO: this proof needs repairs.

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
          cases h5 : result1.memEnv'.get? l with
          | none =>
            simp_all
          | some qt =>
            cases h6 : qt with
            | mk etyp' p2 tp =>
              simp_all
              cases h7 : etyp' != t with
              | true =>
                simp_all
              | false =>
                simp_all
                cases h4: poison with
                | true =>
                  simp_all [pure, Except.pure]
                  cases result; cases result1; cases ctx; cases H; simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                | false =>
                  simp [h4] at H
                  cases h8 : tp with
                  | noPred =>
                    simp_all [pure, Except.pure]
                    cases result; cases result1; cases ctx; cases H; simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                  | guardOnly k =>
                    simp_all
                    match h9 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all [pure, Except.pure] <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all [pure, Except.pure] <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                  | guardClosure k arg_name pred_body var_env =>
                    simp_all
                    match h9 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all [pure, Except.pure] <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all [pure, Except.pure] <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
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

-- Private lemma for app case
private lemma typecheck_app_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.app e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.app e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckApp, bind, Except.bind]
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
      simp [h4] at H
      cases h5: etyp1 with
      | arrow st1 st2 _p tcl =>
        -- non-pure arrow case; not expected under pureCtx hypothesis
        simp_all
      | parrow st1 st2 p tcl =>
        simp [h5] at H
        cases h6: typecheckExpr
                    { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv, tagEnv := result1.tagEnv',
                      nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true }
                    e2 fuel' with
        | error err =>
          simp_all
        | ok result2 =>
          simp (config := { failIfUnchanged := false }) [h6] at H
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
            e2 pe2 result2 h2 C' h6
          rcases IH2 with ⟨H7, H8, H9, H10⟩
          simp_all
          cases h7: result2.qualType with
          | mk etyp2 p2 pred2 =>
            simp_all
            cases h7: isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } with
            | false =>
              simp_all
            | true =>
              simp_all [pure, Except.pure]
              cases tcl with
              | extern _x _retSpec _effects => sorry
              | regular x body env =>
                simp_all
                cases h8: typecheckExpr
                      { pc := joinPoison p (joinPoison ctx.pc p1),
                        memEnv := result2.memEnv',
                        varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                        tagEnv := result2.tagEnv',
                        nextLoc := result2.nextLoc',
                        nextTag := result2.nextTag',
                        pureCtx := true }
                      body.toExpr fuel' with
                | error err =>
                  simp_all
                | ok result3 =>
                  simp_all
                  cases h9: result3.qualType with
                  | mk etyp3 p3 pred3 =>
                    simp_all
                    cases h10: isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                    | false =>
                      simp_all
                    | true =>
                      simp_all [pure, Except.pure]
                      have C'' : ({ pc := joinPoison p (joinPoison ctx.pc p1),
                                    memEnv := result2.memEnv',
                                    varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                                    tagEnv := result2.tagEnv',
                                    nextLoc := result2.nextLoc',
                                    nextTag := result2.nextTag',
                                    pureCtx := true } : TypeContext).pureCtx = true
                          := by simp_all
                      have hb : body.toExpr.toPExpr = Except.ok body := by
                        simpa using toExpr_toPExpr body
                      have IH3 := IH fuel' hfuel
                        { pc := joinPoison p (joinPoison ctx.pc p1),
                          memEnv := result2.memEnv',
                          varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                          tagEnv := result2.tagEnv',
                          nextLoc := result2.nextLoc',
                          nextTag := result2.nextTag',
                          pureCtx := true }
                        body.toExpr body result3 hb C'' h8
                      rcases IH3 with ⟨H11, H12, H13, H14⟩
                      cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
                      -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv' ∧ result2.memEnv'.equiv result3.memEnv'
                      apply Std.HashMap.Equiv.trans H1
                      apply Std.HashMap.Equiv.trans H7
                      exact H11
      | _ => simp_all

theorem typecheck_PExpr_preserves_typestate :
  ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = .ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e fuel = .ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag'
 := by
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
-/
