-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanPoison.Poison
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args are
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

theorem OpEType.sound {o t₁ t₂ r}
  (h : OpEType o t₁ t₂ r) : opEType? o t₁ t₂ = some r := by
  cases h <;> simp [opEType?]

theorem OpEType.complete {o t₁ t₂ r}
  (h : opEType? o t₁ t₂ = some r) : OpEType o t₁ t₂ r := by
  cases o <;> cases t₁ <;> cases t₂
   <;> simp [opEType?] at h <;> rw [<-h] <;> constructor

@[simp] theorem opEType?_iff (o t₁ t₂ r) :
  opEType? o t₁ t₂ = some r ↔ OpEType o t₁ t₂ r :=
  ⟨OpEType.complete, OpEType.sound⟩

@[simp]
theorem joinMemEnv_idempotent : ∀ (m1 : MemoryTypeEnv), joinMemEnvs m1 m1 = m1 := by
  intros m1
  simp [joinMemEnvs]
  sorry

@[simp] theorem toExpr_toPExpr (pe : PExpr) :
  pe.toExpr.toPExpr = Except.ok pe := by
  induction pe with
  | unit | num _ | bool _ | str _ | var _ =>
    simp [PExpr.toExpr, Expr.toPExpr, pure, Except.pure]
  | vlet x e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | app e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | op e1 o e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | unaryop opname e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH]
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2, IH3]
  | deref e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH]

set_option maxHeartbeats 1000000

section TypecheckPExprPreservesTypestate

-- Private lemma for unit case
private lemma typecheck_unit_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat)
  (_C : ctx.pureCtx = true) (_P : Expr.unit.toPExpr = Except.ok pe) (H : typecheckExpr ctx Expr.unit (fuel + 1) = Except.ok result) :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  trivial

-- Private lemma for str case
private lemma typecheck_str_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (s : String)
  (_C : ctx.pureCtx = true) (_P : (Expr.str s).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.str s) (fuel + 1) = Except.ok result) :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  trivial

-- Private lemma for num case
private lemma typecheck_num_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (n : Int)
  (_C : ctx.pureCtx = true) (_P : (Expr.num n).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.num n) (fuel + 1) = Except.ok result) :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  trivial

-- Private lemma for bool case
private lemma typecheck_bool_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (b : Bool)
  (_C : ctx.pureCtx = true) (_P : (Expr.bool b).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.bool b) (fuel + 1) = Except.ok result) :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  trivial

-- Private lemma for var case
private lemma typecheck_var_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (name : Name)
  (C : ctx.pureCtx = true) (_P : (Expr.var name).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.var name) (fuel + 1) = Except.ok result) :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          cases result <;> cases ctx <;> cases H <;> simp_all
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all
      | guardOnly tag =>
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all
      | noPred =>
        -- No predicate case: preserves environment
        simp_all [typecheckVar, h0, h1, h3, pure, Except.pure]
        cases result <;> cases ctx <;> cases H <;> simp_all

-- Private lemma for deref case
private lemma typecheck_deref_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr)
  (C : ctx.pureCtx = true) (P : e1.deref.toPExpr = Except.ok pe) (H : typecheckExpr ctx e1.deref (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          cases h4: poison with
          | true =>
            simp_all [pure, Except.pure]
            cases result; cases result1; cases ctx; cases H; trivial
          | false =>
            simp [h4] at H
            cases h5 : result1.memEnv'.get? l with
            | none =>
              simp_all
            | some qt =>
              cases h6 : qt with
              | mk etyp' p2 tp =>
                simp_all
                cases h7 : tp with
                | noPred =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    cases result; cases result1; cases ctx; cases H; trivial
                | guardOnly k =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    match h10 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> trivial
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> trivial
                | guardClosure k arg_name pred_body var_env =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    match h10 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> trivial
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> trivial
        | _ => simp_all

-- Private lemma for ite case
private lemma typecheck_ite_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 e3 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.ite e2 e3).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.ite e2 e3) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
                  cases h13: etyp2 != etyp3 with
                  | true =>
                    simp_all
                  | false =>
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
                    cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
  | ok k_deps =>
    -- predicate-based case: matching predicate found
    simp_all
    have ctx_simp: ctx = { pc := ctx.pc,
                           memEnv := ctx.memEnv,
                           varEnv := ctx.varEnv,
                           tagEnv := ctx.tagEnv,
                           nextLoc := ctx.nextLoc,
                           nextTag := ctx.nextTag,
                           pureCtx := true
                         }
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
        simp [h6] at H
        cases h7: etyp1 != ETyp.bool with
        | true =>
          simp [h7] at H
        | false =>
          simp [h7] at H
          simp [pure, Except.pure] at H
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
                  cases h13: etyp2 != etyp3 with
                  | true =>
                    simp [h13] at H
                  | false =>
                    simp [h13] at H
                    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                    rw [<- ctx_simp] at h5
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
                    cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all

-- Private lemma for op case
private lemma typecheck_op_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr) (op : Op) (e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.op op e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.op op e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          | none =>
            simp_all

-- Private lemma for unaryop case
private lemma typecheck_unaryop_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (op : UnaryOp) (e : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.unaryop op e).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          simp_all
          cases result; cases result1; cases result2; cases ctx; cases H; simp_all

-- Private lemma for app case
private lemma typecheck_app_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.app e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.app e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
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
          simp [h6] at H
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
              | mk x body env =>
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
                      have hb : body.toExpr.toPExpr = Except.ok body := by simp
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
      | _ => simp_all

theorem typecheck_PExpr_preserves_typestate :
  ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = .ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e fuel = .ok result →
    ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag'
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
      | printInt _ =>
        contradiction

end TypecheckPExprPreservesTypestate

-- ================================================================
-- Evaluation Preserves Variable Environment
-- ================================================================
--
-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)

-- Helper lemma: bevalFunctionBody preserves varEnv
private lemma bevalFunctionBody_preserves_varEnv
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
    pure (.success finalConfig v) →
  currentConfig.varEnv = finalConfig.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel
  revert finalConfig v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro finalConfig v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, bevalFunctionBody returns outOfFuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp [pure] at h_eval
      -- Apply congrFun to convert function equality to point-wise equality
      apply congrFun (a := ()) at h_eval
      -- Now we have: EvalResult.outOfFuel = EvalResult.success finalConfig v
      -- Injection will give us the contradictory components
      injection h_eval with h_contr
      -- h_contr is a contradiction between different constructors, so cases derives False
      cases h_contr
    | succ fuel' =>
      -- fuel = fuel' + 1: bevalFunctionBody has enough fuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp at h_eval
      -- Convert IO to EStateM form
      apply congrFun (a := ()) at h_eval
      simp [bind, Bind.bind, EStateM.bind] at h_eval
      -- Split on body evaluation result
      split at h_eval
      · next h_body_result h_body_state h_beval_body =>
        split at h_eval
        · next evalConfig v_body =>
          -- Body evaluation succeeded
          split at h_eval
          · -- isPure = true branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
          · -- isPure = false branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc, pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
        · next =>
          injection h_eval with h_contr _
          injection h_contr
        · next msg =>
          injection h_eval with h_contr _
          injection h_contr
      · next h_body_error h_body_state =>
        injection h_eval

-- Helper lemmas for beval_preserves_varEnv, one per expression constructor

private lemma beval_preserves_varEnv_num (n : Int) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.num n) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_bool (b : Bool) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.bool b) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_unit (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ Expr.unit verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_str (s : String) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.str s) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_var (x : Name) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.var x) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  cases h_lookup : config₀.varEnv.lookup x with
  | some v' =>
    simp [h_lookup] at h_eval
    injection h_eval with h_cfg _
    injection h_cfg with h_cfg_eq
    subst h_cfg_eq
    rfl
  | none =>
    simp [h_lookup] at h_eval
    injection h_eval with h_contr _
    injection h_contr
private lemma beval_preserves_varEnv_op (e1 e2 : Expr) (op : Op) (fuel' : Nat) (verbose : Bool) (config₀ config₃ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.op e1 op e2) verbose = pure (.success config₃ v)) :
  config₀.varEnv = config₃.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁ v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁ v₁ h_beval1'
            have h_beval2' : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₁ config₂ v₂ h_beval2'
            exact Eq.trans IH1 IH2
          | none =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 =>
        cases h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => cases h_eval

private lemma beval_preserves_varEnv_unaryop (op : UnaryOp) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' v' =>
      cases h_evalUnaryOp : LeanPoison.evalUnaryOp op v' with
      | some v_result =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' v') := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1'
      | none =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_ite (e1 e2 e3 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool true)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool true) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result3 h_state3 h_beval3 =>
        split at h_eval
        · next config₂ v₃ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool false)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool false) h_beval1'
          have h_beval3' : LeanPoison.beval fuel' config₁' e3 verbose = pure (.success config₂ v₃) := by
            funext _
            simp [pure]
            exact h_beval3
          let IH3 := IH fuel' h_fuel e3 verbose config₁' config₂ v₃ h_beval3'
          exact Eq.trans IH1 IH3
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error3 h_state3 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_newRef (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.newRef e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      injection h_eval with h_cfg _
      injection h_cfg with h_cfg_eq
      subst h_cfg_eq
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      simp [freshLoc]
      exact IH1
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_assign (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' l =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ n =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.loc l)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.loc l) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ (Value.num n) h_beval2'
          simp
          exact Eq.trans IH1 IH2
        · next v => injection h_eval with h_cfg _; injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_deref (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.deref e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' l =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.loc l)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.loc l) h_beval1'
      cases h_mem_lookup : config'.memory[l]? with
      | some n =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        exact IH1
      | none =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_contr _
        injection h_contr
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_seq (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_split1_result h_split1_state h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      . next h_split3_config h_split3_v1 h_beval2 =>
        split at h_eval
        · next h_split4_config config₂ v₂ =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1 with h_eval_e1_result h_eval_e1_config
          subst h_eval_e1_result h_eval_e2 h_eval_e1_config
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        . next h_split4_eq =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
        . next h_split4_msg h_split4_eq =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
      . next h_split3_eq => injection h_eval
    · next h_split2_error h_split2_state =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
    . next h_split2_msg h_split2_eq =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
  . next h_split1_error h_split1_state h_split1_eq => injection h_eval

private lemma beval_preserves_varEnv_kwhile (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  unfold LeanPoison.beval at h_eval
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel'.succ - 1) config₀ unfolded verbose
  simp at h_eval
  -- After simp: the let binding is inlined and fuel'.succ - 1 simplifies to fuel'
  -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose = pure (.success config₁ v)
  -- Convert to applied form to work with the monadic structure
  apply congrFun (a := ()) at h_eval
  -- h_eval now contains: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose () = pure (.success config₁ v) ()
  have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
  -- Define the unfolded expression that kwhile expands to
  let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  -- h_eval already contains the evaluation of this unfolded expression
  -- Convert from applied form to pure form for IH
  have h_beval_unfolded : LeanPoison.beval fuel' config₀ unfolded verbose = pure (.success config₁ v) := by
    funext _
    simp [pure]
    exact h_eval
  -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
  -- The unfolded expression (ite) preserves varEnv by IH (which internally uses the ite proof)
  exact IH fuel' h_fuel unfolded verbose config₀ config₁ v h_beval_unfolded

private lemma beval_preserves_varEnv_vlet (x : Name) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          simp
          exact IH1
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_fn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.fn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_pfn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.pfn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_app (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval2 =>
    split at h_eval
    · next config₁' v₂ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval1 =>
        split at h_eval
        · next config₂ x body env =>
          split at h_eval
          · injection h_eval with h_contr _; injection h_contr
          · -- pureMode is false, call bevalFunctionBody
            -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body false = pure (.success config₁ v)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
            have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.closure x body env)) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.closure x body env) h_beval1'
            -- Extract bevalFunctionBody equality from h_eval
            -- Convert from applied form to pure form
            have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval
            -- Apply helper lemma
            have h_funcBody : config₂.varEnv = config₁.varEnv :=
              bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body false v h_bevalFunctionBody
            -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
            exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next config₂ x body env =>
          -- peClosure case (pure function), call bevalFunctionBody with isPure=true
          -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body true = pure (.success config₁ v)
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
          have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.peClosure x body env)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.peClosure x body env) h_beval1'
          -- Extract bevalFunctionBody equality from h_eval
          -- Convert from applied form to pure form
          have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
              pure (.success config₁ v) := by
            funext _
            simp [pure]
            exact h_eval
          -- Apply helper lemma
          have h_funcBody : config₂.varEnv = config₁.varEnv :=
            bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body true v h_bevalFunctionBody
          -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
          exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next v => injection h_eval with h_contr _; injection h_contr
        · next => injection h_eval with h_contr _; injection h_contr
        · next msg => injection h_eval with h_contr _; injection h_contr
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_contr _; injection h_contr
    · next msg => injection h_eval with h_contr _; injection h_contr
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_rand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.rand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_frand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.frand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printInt (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printInt e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printString (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printString e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' s =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.str s)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.str s) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)
lemma beval_preserves_varEnv (e : Expr) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ e verbose = pure (.success config₁ v) →
  config₀.varEnv = config₁.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel, then case analysis on e
  -- For all expression forms, the varEnv field is never modified
  -- (even in let bindings, we create a new config with extended varEnv for the body,
  --  but the final result restores the original varEnv)
  revert e config₀ config₁ v h_eval verbose
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e verbose config₀ config₁ v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, beval returns outOfFuel, not success
      unfold LeanPoison.beval at h_eval
      simp at h_eval
      apply congrFun (a := ()) at h_eval
      cases h_eval
    | succ fuel' =>
      cases e with
      | num n => exact beval_preserves_varEnv_num n fuel' verbose config₀ config₁ v IH h_eval
      | bool b => exact beval_preserves_varEnv_bool b fuel' verbose config₀ config₁ v IH h_eval
      | unit => exact beval_preserves_varEnv_unit fuel' verbose config₀ config₁ v IH h_eval
      | str s => exact beval_preserves_varEnv_str s fuel' verbose config₀ config₁ v IH h_eval
      | var x => exact beval_preserves_varEnv_var x fuel' verbose config₀ config₁ v IH h_eval
      | op e1 op e2 =>
        exact beval_preserves_varEnv_op e1 e2 op fuel' verbose config₀ config₁ v IH h_eval
      | unaryop op e1 =>
        exact beval_preserves_varEnv_unaryop op e1 fuel' verbose config₀ config₁ v IH h_eval
      | ite e1 e2 e3 =>
        exact beval_preserves_varEnv_ite e1 e2 e3 fuel' verbose config₀ config₁ v IH h_eval
      | newRef e1 =>
        exact beval_preserves_varEnv_newRef e1 fuel' verbose config₀ config₁ v IH h_eval
      | assign e1 e2 =>
        exact beval_preserves_varEnv_assign e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | deref e1 =>
        exact beval_preserves_varEnv_deref e1 fuel' verbose config₀ config₁ v IH h_eval
      | seq e1 e2 =>
        exact beval_preserves_varEnv_seq e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | kwhile e1 e2 =>
        exact beval_preserves_varEnv_kwhile e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | vlet x e1 e2 =>
        exact beval_preserves_varEnv_vlet x e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | fn x paramType body returnType =>
        exact beval_preserves_varEnv_fn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | pfn x paramType body returnType =>
        exact beval_preserves_varEnv_pfn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | app e1 e2 =>
        exact beval_preserves_varEnv_app e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | rand e1 =>
        exact beval_preserves_varEnv_rand e1 fuel' verbose config₀ config₁ v IH h_eval
      | frand e1 =>
        exact beval_preserves_varEnv_frand e1 fuel' verbose config₀ config₁ v IH h_eval
      | printInt e1 =>
        exact beval_preserves_varEnv_printInt e1 fuel' verbose config₀ config₁ v IH h_eval
      | printString e1 =>
        exact beval_preserves_varEnv_printString e1 fuel' verbose config₀ config₁ v IH h_eval
