-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
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
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2, IH3]
  | deref e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH]

set_option maxHeartbeats 1000000

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
      | unit
      | str _
      | num _
      | bool _ =>
        simp_all [typecheckExpr]
        cases H
        trivial
      | var name =>
        simp_all [typecheckExpr]
        -- All var cases preserve environment fields - handle uniformly
        simp [typecheckVar] at H
        cases h0: ctx.varEnv.lookup name with
        | none => simp_all
        | some qt =>
          cases h1: qt with
          | mk etyp poison pred =>
            cases h3: pred with
            | none =>
              -- No predicate case: preserves environment
              simp_all [pure, Except.pure]
              cases result; cases ctx; cases H; trivial
            | some tp =>
              -- Has predicate: all cases preserve environment
              cases h4: tp with
              | mk tag etyp =>
                cases h5: ctx.tagEnv[tag]? with
                | none =>
                  -- Guard unknown: preserves environment
                  simp_all [pure, Except.pure]
                  cases result; cases ctx; cases H; trivial
                | some b =>
                  -- Guard known (true/false): both preserve environment
                  cases b <;>
                  simp_all <;>
                  cases result <;> cases ctx <;> cases H <;> trivial

      | deref e1 =>
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
                  cases h5: result1.memEnv'[l]? with
                  | none =>
                    simp_all
                  | some qt =>
                    cases h6: qt with
                    | mk etyp' p2 tp =>
                      simp_all
                      cases h7: tp with
                      | none =>
                        simp_all
                        cases h9: etyp' != t with
                        | true =>
                          simp_all
                        | false =>
                          simp_all [pure, Except.pure]
                          cases result; cases result1; cases ctx; cases H; trivial
                      | some tp =>
                        cases h8: tp with
                        | mk k arg_name pred_body var_env =>
                          simp_all
                          cases h9: etyp' != t with
                          | true =>
                            simp_all
                          | false =>
                            simp_all [pure, Except.pure]
                            match h10 : result1.tagEnv'[k]? with
                            | some true | some false | none =>
                            simp_all <;>
                            cases result <;> cases result1 <;> cases ctx <;> cases H <;> trivial
              | _ => simp_all
      | ite e1 e2 e3  =>
        simp [typecheckExpr] at H
        (cases fuel with | zero |succ fuel') <;> simp_all [typecheckIf, bind, Except.bind]
        simp [Expr.toPExpr, Functor.map, Except.map] at P
        (cases h1: e1.toPExpr with| error err | ok pe1 ) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
        (cases h3: e2.toPExpr with | error err | ok pe2) <;> simp [h3] at P
        (cases h4: e3.toPExpr with | error err | ok pe3) <;> simp [h4] at P
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
              cases h8: matchGuard e1 result1.memEnv' ctx.varEnv with
              | ok k =>
                simp_all
                cases h9: typecheckExpr { pc := ctx.pc,
                                          memEnv := result1.memEnv',
                                          varEnv := ctx.varEnv,
                                          tagEnv := Std.HashMap.insert result1.tagEnv' k true,
                                          nextLoc := result1.nextLoc',
                                          nextTag := result1.nextTag',
                                          pureCtx := true } e2 fuel'
                               with
                | error err =>
                  simp_all
                | ok result2 =>
                  simp_all
                  cases h10: result2.qualType with
                  | mk etyp2 p'' pred =>
                    simp_all
                    cases h11: typecheckExpr
                            { pc := ctx.pc,
                              memEnv := result1.memEnv',
                              varEnv := ctx.varEnv,
                              tagEnv := Std.HashMap.insert result1.tagEnv' k false,
                              nextLoc := result2.nextLoc',
                              nextTag := result2.nextTag',
                              pureCtx := true }
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
                          simp_all
                          have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                          have C' : ({ pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                             tagEnv := Std.HashMap.insert result1.tagEnv' k true,
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                                  := by simp_all
                          have IH2 :=
                            IH fuel' hfuel { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                             tagEnv := Std.HashMap.insert result1.tagEnv' k true,
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true }
                                             e2 pe2 result2 h3 C' h9

                          have C'' : ({ pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                             tagEnv := Std.HashMap.insert result1.tagEnv' k false,
                                             nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                                  := by simp_all
                          have IH3 :=
                            IH fuel' hfuel
                              { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                tagEnv := Std.HashMap.insert result1.tagEnv' k false,
                                nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                              e3 pe3 result3 h4 C'' h11
                          rcases IH2 with ⟨H14, H15, H16⟩
                          rcases IH3 with ⟨H17, H18, H19⟩
                          cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
              | error err =>
                simp_all
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
      | op e1 op e2 =>
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
      | vlet x e1 e2 =>
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
      | app e1 e2 =>
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
