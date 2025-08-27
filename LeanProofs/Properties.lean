-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.Eval

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

-- Pure expression type checking does not modify typestates
theorem typecheck_preserves_typestate : ∀ (fuel : Nat),
  ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
  e.toPExpr = .ok pe →
  typecheckExpr ctx e fuel = .ok result →
  ctx.memEnv = result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' := by

  intros fuel ctx e pe result P H
  induction e generalizing fuel ctx result pe with
  | unit
  | str _
  | num _
  | bool _ =>
    cases fuel <;> simp_all [typecheckExpr]
    cases H
    trivial
  | var name =>
    cases fuel <;> simp_all [typecheckExpr]
    -- All var cases preserve environment fields - handle uniformly
    simp [typecheckVar] at H
    cases h0: lookupVarEnv ctx.varEnv name with
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

  | deref e1 IH =>
    (cases fuel with | zero |succ fuel) <;> simp_all [typecheckExpr]
    (cases fuel with | zero |succ fuel') <;> simp_all [typecheckDeref, bind, Except.bind]
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
        specialize IH fuel' ctx pe1 result1 h1 h0
        rcases IH with ⟨H1, H2, H3⟩
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
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    (cases fuel with | zero |succ fuel) <;> simp_all [typecheckExpr]
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
      specialize IH1 fuel' ctx pe1 result1 h1 h5
      rcases IH1 with ⟨H1, H2, H3⟩
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
            cases h9: typecheckExpr
                        { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := Std.HashMap.insert result1.tagEnv' k true, nextLoc := result1.nextLoc', nextTag := ctx.nextTag}
                        e2 fuel' with
            | error err =>
              simp_all
            | ok result2 =>
              simp_all
              cases h10: result2.qualType with
              | mk etyp2 p'' pred =>
                simp_all
                cases h11: typecheckExpr
                        { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := Std.HashMap.insert result1.tagEnv' k false, nextLoc := result1.nextLoc', nextTag := ctx.nextTag}
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
                      have hpe2 : pe2 = pe2 := rfl
                      specialize IH2 fuel'
                           { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                             tagEnv := Std.HashMap.insert result1.tagEnv' k true,
                             nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
                           pe2 result2 hpe2 h9
                      have hpe3 : pe3 = pe3 := rfl
                      specialize IH3 fuel' { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                             tagEnv := Std.HashMap.insert result1.tagEnv' k false,
                                             nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
                          pe3 result3 hpe3 h11
                      rcases IH2 with ⟨H14, H15, H16⟩
                      rcases IH3 with ⟨H17, H18, H19⟩
                      cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
          | error err =>
            simp_all
            cases h9: typecheckExpr
                        { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
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
                          tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
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
                      have hpe2 : pe2 = pe2 := rfl
                      specialize IH2 fuel'
                           { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                             tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
                           pe2 result2 hpe2 h9
                      have hpe3 : pe3 = pe3 := rfl
                      specialize IH3 fuel' {pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                            tagEnv := result1.tagEnv',
                                            nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
                          pe3 result3 hpe3 h11
                      rcases IH2 with ⟨H14, H15, H16⟩
                      rcases IH3 with ⟨H17, H18, H19⟩
                      cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
  | op e1 op e2 IH1 IH2 =>
    (cases fuel with | zero |succ fuel) <;> simp_all [typecheckExpr]
    (cases fuel with | zero |succ fuel') <;> simp_all [typecheckOp, bind, Except.bind]
    simp [Expr.toPExpr, Functor.map, Except.map] at P
    (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp_all [h1, Seq.seq, Except.bind, Except.map]
    (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp_all [h2, Seq.seq, Except.bind, Except.map]
    cases h3: typecheckExpr ctx e1 fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h3] at H
      have hpe1 : pe1 = pe1 := rfl
      specialize IH1 fuel' ctx pe1 result1 hpe1 h3
      rcases IH1 with ⟨H1, H2, H3⟩
      simp_all
      cases h4: result1.qualType with
      | mk etyp1 p1 pred1 =>
        simp_all
        cases h5: typecheckExpr
                        { pc := ctx.pc, memEnv := result1.memEnv',
                          varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv',
                          nextLoc := result1.nextLoc',
                          nextTag := ctx.nextTag }
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
              have hpe2 : pe2 = pe2 := rfl
              specialize IH2 fuel'
                        { pc := ctx.pc, memEnv := result1.memEnv',
                          varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv',
                          nextLoc := result1.nextLoc',
                          nextTag := ctx.nextTag }
                        pe2 result2 hpe2 h5
              rcases IH2 with ⟨H8, H9, H10⟩
              simp_all
              cases result; cases result1; cases result2; cases ctx; cases H; simp_all
            | none =>
              simp_all
  | vlet x e1 e2 IH1 IH2 =>
    (cases fuel with | zero |succ fuel) <;> simp_all [typecheckExpr]
    (cases fuel with | zero |succ fuel') <;> simp_all [typecheckVlet, bind, Except.bind]
    simp [Expr.toPExpr, Functor.map, Except.map] at P
    (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
    (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
    cases h3: typecheckExpr ctx e1 fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h3] at H
      specialize IH1 fuel' ctx pe1 result1 h1 h3
      rcases IH1 with ⟨H1, H2, H3⟩
      cases h4: result1.qualType with
      | mk etyp1 p1 pred1 =>
        simp_all
        cases h4: typecheckExpr
                        { pc := ctx.pc, memEnv := result1.memEnv',
                          varEnv := updateVarEnv ctx.varEnv x { etyp := etyp1, poison := joinPoison ctx.pc p1, pred := pred1 },
                          tagEnv := result1.tagEnv',
                          nextLoc := result1.nextLoc',
                          nextTag := ctx.nextTag }
                        e2 fuel' with
        | error err =>
          simp_all
        | ok result2 =>
          simp_all
          cases h5: result2.qualType with
          | mk etyp2 p2 pred2 =>
            simp_all [pure, Except.pure]
            have hpe2 : pe2 = pe2 := rfl
            specialize IH2 fuel'
             { pc := ctx.pc, memEnv := result1.memEnv',
               varEnv := updateVarEnv ctx.varEnv x { etyp := etyp1, poison := joinPoison ctx.pc p1, pred := pred1 },
               tagEnv := result1.tagEnv',
               nextLoc := result1.nextLoc',
               nextTag := ctx.nextTag }
             pe2 result2 hpe2 h4
            simp_all
            cases result; cases result1; cases result2; cases ctx; cases H; simp_all
  | app e1 e2 IH1 IH2 =>
    (cases fuel with | zero |succ fuel) <;> simp_all [typecheckExpr]
    (cases fuel with | zero |succ fuel') <;> simp_all [typecheckApp, bind, Except.bind]
    simp [Expr.toPExpr, Functor.map, Except.map] at P
    (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
    (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
    cases h3: typecheckExpr ctx e1 fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h3] at H
      specialize IH1 fuel' ctx pe1 result1 h1 h3
      rcases IH1 with ⟨H1, H2, H3⟩
      simp_all
      cases h4: result1.qualType with
      | mk etyp1 _p1 pred1 =>
        simp [h4] at H
        cases h5: etyp1 with
        | arrow st1 st2 _p tcl =>
          simp [h5] at H
          cases h6: typecheckExpr
                        { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv, tagEnv := result1.tagEnv',
                          nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
                        e2 fuel' with
          | error err =>
            simp_all
          | ok result2 =>
            simp [h6] at H
            have hpe2 : pe2 = pe2 := rfl
            specialize IH2 fuel' { pc := ctx.pc, memEnv := result1.memEnv',
                                   varEnv := ctx.varEnv,
                                   tagEnv := result1.tagEnv',
                                   nextLoc := result1.nextLoc',
                                   nextTag := ctx.nextTag }
                                   pe2 result2 hpe2 h6
            rcases IH2 with ⟨H7, H8, H9⟩
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
                | fn_tclosure x body env =>
                  -- should not be possible to have a fn_tclosure here
                  sorry
                | pfn_tclosure x body env =>
                  simp_all
                  cases h8: typecheckExpr
                        { pc := ctx.pc, memEnv := result2.memEnv',
                          varEnv := updateVarEnv env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                          tagEnv := result2.tagEnv', nextLoc := result1.nextLoc', nextTag := ctx.nextTag }
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
                      cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
                      sorry
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

namespace NonInterference

-- ================================================================
-- Non-Interference (semantic formulation)
-- ================================================================

-- We formulate the Non-Interference Property using the operational
-- semantics carriers (Expr, Config, ExprOrValue) and use QTyp/TPred to
-- describe predicates attached to critical inputs. We deliberately keep
-- some components abstract (as constants), to be instantiated later with
-- concrete predicate/application machinery.

-- Big-step termination relation to a final configuration and result.
-- Intended to coincide with repeated small-step evaluation to a value
-- (or irreducible expression) as implemented in LeanPoison.Eval.
  def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
    ∃ (fuel : Nat) (verbose : Bool),
      eval fuel c₀ (ExprOrValue.expr e) verbose = pure (StepResult.progress c₁ out)

  -- Input partition: which initial locations/variables are critical vs non-critical
  structure InputPartition where
    Lcrit    : List Address
    Vcrit    : List Name
    Lnoncrit : List Address
    Vnoncrit : List Name
  deriving Repr

  def disjointList {α} [DecidableEq α] (xs ys : List α) : Prop :=
    ∀ a, a ∈ xs → a ∉ ys

  def wfPartition (p : InputPartition) : Prop :=
    disjointList p.Lcrit p.Lnoncrit ∧ disjointList p.Vcrit p.Vnoncrit

  -- Types for critical inputs (use QTyp so we can attach optional predicates)
  structure InputTyping where
    critLocTypes : List (Address × QTyp)
    critVarTypes : VarTypeEnv
  deriving Repr

  def keysLoc (it : InputTyping) : List Address := it.critLocTypes.map (·.1)
  def keysVar (it : InputTyping) : List Name := it.critVarTypes.map (·.1)

  def sameElems {α} [DecidableEq α] (xs ys : List α) : Prop :=
    ∀ a, a ∈ xs ↔ a ∈ ys

  def wfTyping (p : InputPartition) (it : InputTyping) : Prop :=
    sameElems p.Lcrit (keysLoc it) ∧ sameElems p.Vcrit (keysVar it)

  -- What parts of the final state are observable
  structure ObservableSpec where
    Lobs       : List Address
    observeRet : Bool
  deriving Repr

  -- Regime vector (one boolean per critical input, in some fixed order).
  -- We keep the ordering abstract and only require consistency via
  -- the abstract predicates below.
  structure Regime where
    bits : List Bool
  deriving Repr

  def numCritical (p : InputPartition) : Nat := p.Lcrit.length + p.Vcrit.length
  def regimeWellSized (R : Regime) (p : InputPartition) : Prop :=
    R.bits.length = numCritical p

  -- Abstract predicate: does the QTyp-attached predicate hold for the given
  -- input value under the initial environments? For locations the value will
  -- be encoded as Value.num n; for variables it is the variable's Value.
  axiom qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop

  -- Abstract consistency predicate: the regime vector R reflects, for the
  -- given initial memory/varenv, whether each critical input is valid under
  -- its (optional) predicate from InputTyping. This glues together the chosen
  -- ordering of critical inputs with predicate evaluation. Details elided.
  axiom consistentRegime
    : Regime → InputPartition → InputTyping → Memory → VarEnv → Prop

  -- Abstract agreement predicate: when a regime bit for a critical input is
  -- true, the corresponding initial inputs in (μ₁,ρ₁) and (μ₂,ρ₂) are equal.
  -- When the bit is false and there is a predicate, both inputs must fail it.
  -- (We separate this from consistentRegime to keep responsibilities clear.)
  axiom agreeOnCriticalInputsUnderRegime
    : Regime → InputPartition → InputTyping
      → Memory → VarEnv
      → Memory → VarEnv → Prop

  axiom valueHasType : Value → ETyp → Prop

  def inputsConform (it : InputTyping) (μ : Memory) (ρ : VarEnv) : Prop :=
    (∀ {l qt}, (l, qt) ∈ it.critLocTypes → μ.get? l ≠ none ∧ qt.etyp = ETyp.int) ∧
    (∀ {x qt v}, (x, qt) ∈ it.critVarTypes → VarEnv.get ρ x = some v → valueHasType v qt.etyp)

  -- Helper: equality of observables in the final states
  def observablesEqual (obs : ObservableSpec)
      (c₁ c₂ : Config) (o₁ o₂ : ExprOrValue) : Prop :=
    let sameMem : Prop := ∀ l, l ∈ obs.Lobs → c₁.memory.get? l = c₂.memory.get? l
    let sameRet : Prop := if obs.observeRet then o₁ = o₂ else True
    sameMem ∧ sameRet

  -- Build initial configurations from initial inputs
  def mkInit (μ : Memory) (ρ : VarEnv) : Config :=
    { memory := μ, varEnv := ρ, nextLoc := 0 }

  -- Non-Interference property (semantic form)
  def Holds (e : Expr)
      (part : InputPartition)
      (ityp : InputTyping)
      (obs : ObservableSpec) : Prop :=
    wfPartition part ∧ wfTyping part ityp →
    ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
      (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
      regimeWellSized R part →
      inputsConform ityp μ₁ ρ₁ →
      inputsConform ityp μ₂ ρ₂ →
      consistentRegime R part ityp μ₁ ρ₁ →
      consistentRegime R part ityp μ₂ ρ₂ →
      agreeOnCriticalInputsUnderRegime R part ityp μ₁ ρ₁ μ₂ ρ₂ →
      terminatesTo e (mkInit μ₁ ρ₁) cf₁ o₁ →
      terminatesTo e (mkInit μ₂ ρ₂) cf₂ o₂ →
      observablesEqual obs cf₁ cf₂ o₁ o₂

end NonInterference
