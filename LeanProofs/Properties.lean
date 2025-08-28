-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.Eval
import Mathlib.Data.List.Forall2

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args are
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false
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

set_option maxHeartbeats 800000

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
    (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
    (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
    cases h3: typecheckExpr ctx e1 fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h3] at H
      have hpe1 : e1.toPExpr = .ok pe1 := by simp [h1]
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

  def sameElems {α} (xs ys : List α) : Prop :=
    ∀ a, a ∈ xs ↔ a ∈ ys

  -- What parts of the final state are observable
  structure ObservableSpec where
    Lobs       : List (Address × ETyp)
    retEtyp?   : Option ETyp
  deriving Repr

  -- Regime vector (split: locations and variables, fixed order given by s.locs/s.vars)
  structure Regime where
    locBits : List Bool
    varBits : List Bool
  deriving Repr

  -- Abstract predicate: does the QTyp-attached predicate hold for the given
  -- input value under the initial environments? For locations the value will
  -- be encoded as Value.num n; for variables it is the variable's Value.
  axiom qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop

  -- Check if a runtime value has the specified enriched type
  inductive valueHasType : Value → ETyp → Prop where
    | num (n): valueHasType (Value.num n) ETyp.int
    | bool (b): valueHasType (Value.bool b) ETyp.bool
    | unit : valueHasType Value.unit ETyp.unit
    | str (s): valueHasType (Value.str s) ETyp.string
    | loc (l t l'): valueHasType (Value.loc l) (ETyp.ref t l')  -- ignore concrete address in type
    | closure (x e env st1 st2 p tcl):
        valueHasType (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
    | peClosure (x pe env st1 st2 p tcl):
        valueHasType (Value.peClosure x pe env) (ETyp.arrow st1 st2 p tcl)

  -- Domains of typing environments
  def memDom (Γ : MemoryTypeEnv) : List Address := Γ.keys
  def varDom (σ : VarTypeEnv) : List Name := σ.map (·.1)

  -- Runtime instantiates the context: values exist for every typed variable
  -- and memory contains entries for each typed location.
  def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) : Prop :=
    (∀ {l}, l ∈ memDom ctx.memEnv → μ.get? l ≠ none) ∧
    (∀ {x qt}, (x, qt) ∈ ctx.varEnv → ∃ v, VarEnv.get ρ x = some v ∧ valueHasType v qt.etyp)

  -- Helper: equality of observables in the final states
  def observablesEqual (obs : ObservableSpec)
      (c₁ c₂ : Config) (o₁ o₂ : ExprOrValue) : Prop :=
    let sameMem : Prop := ∀ {l et}, (l, et) ∈ obs.Lobs → c₁.memory.get? l = c₂.memory.get? l
    let sameRet : Prop := match obs.retEtyp? with | some _ => o₁ = o₂ | none => True
    sameMem ∧ sameRet

  -- Build initial configurations from initial inputs
  def mkInit (μ : Memory) (ρ : VarEnv) : Config :=
    { memory := μ, varEnv := ρ, nextLoc := 0 }

  -- =================================================
  -- Combined input specification (partition + typing)
  -- =================================================

  structure LocEntry where
    addr : Address
    qt   : QTyp
    is_critical : Bool
  deriving Repr

  structure VarEntry where
    name : Name
    qt   : QTyp
    is_critical : Bool
  deriving Repr

  structure InputSpec where
    locs : List LocEntry
    vars : List VarEntry
  deriving Repr

  def specLocAddrs (s : InputSpec) : List Address := s.locs.map (·.addr)
  def specVarNames (s : InputSpec) : List Name := s.vars.map (·.name)

  def isCritLoc (s : InputSpec) (a : Address) : Prop :=
    ∃ le, le ∈ s.locs ∧ le.addr = a ∧ le.is_critical = true
  def isCritVar (s : InputSpec) (x : Name) : Prop :=
    ∃ ve, ve ∈ s.vars ∧ ve.name = x ∧ ve.is_critical = true

  -- critical lists in the fixed order of the spec
  def critLocs (s : InputSpec) : List LocEntry := s.locs.filter (·.is_critical)
  def critVars (s : InputSpec) : List VarEntry := s.vars.filter (·.is_critical)

  def numCritLocs (s : InputSpec) : Nat := (critLocs s).length
  def numCritVars (s : InputSpec) : Nat := (critVars s).length
  def numCriticalSpec (s : InputSpec) : Nat := numCritLocs s + numCritVars s

  -- Well-formedness of combined spec
  def wfInputSpec (s : InputSpec) : Prop :=
    (∀ {le}, le ∈ s.locs → le.qt.etyp = ETyp.int ∧ (le.is_critical = false → le.qt.poison = true ∧ le.qt.pred = none)) ∧
    (∀ {ve}, ve ∈ s.vars → (ve.is_critical = false → ve.qt.poison = true ∧ ve.qt.pred = none))

  -- Context matches the spec exactly (pc clean, empty logical env, exact coverage, exact typings)
  def ctxMatchesSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
    ctx.pc = false ∧ ctx.tagEnv = {} ∧
    sameElems (specLocAddrs s) (memDom ctx.memEnv) ∧
    sameElems (specVarNames s) (varDom ctx.varEnv) ∧
    (∀ {le}, le ∈ s.locs → ctx.memEnv.get? le.addr = some le.qt) ∧
    (∀ {ve}, ve ∈ s.vars → lookupVarEnv ctx.varEnv ve.name = some ve.qt)

  -- Runtime conforms to spec (availability + dynamic type compatibility for vars)
  def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
    (∀ {le}, le ∈ s.locs → μ.get? le.addr ≠ none) ∧
    (∀ {ve v}, ve ∈ s.vars → VarEnv.get ρ ve.name = some v → valueHasType v ve.qt.etyp)

  -- Elementwise predicates for regimes (inductive for easy inversion)
  inductive holdsLocBit (μ : Memory) (ρ : VarEnv) : Bool → LocEntry → Prop where
    | true_ok (le : LocEntry) (n : Int)
        (hmem : μ.get? le.addr = some n)
        (hpred : qtypPredHolds le.qt μ ρ (Value.num n)) :
        holdsLocBit μ ρ true le
    | false_ok (le : LocEntry)
        (hexists : ∃ n, μ.get? le.addr = some n)
        (hno : ∀ n, ¬ (μ.get? le.addr = some n ∧ qtypPredHolds le.qt μ ρ (Value.num n))) :
        holdsLocBit μ ρ false le

  inductive holdsVarBit (μ : Memory) (ρ : VarEnv) : Bool → VarEntry → Prop where
    | true_ok (ve : VarEntry) (v : Value)
        (hget : VarEnv.get ρ ve.name = some v)
        (hpred : qtypPredHolds ve.qt μ ρ v) :
        holdsVarBit μ ρ true ve
    | false_ok (ve : VarEntry)
        (hexists : ∃ v, VarEnv.get ρ ve.name = some v)
        (hno : ∀ v, ¬ (VarEnv.get ρ ve.name = some v ∧ qtypPredHolds ve.qt μ ρ v)) :
        holdsVarBit μ ρ false ve

  -- Regime consistency (aligned pairs via Forall₂ over fixed-order lists)
  -- Forall2 also enforces that the lists are the same length.
  def consistentRegimeSpec (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
    List.Forall₂ (holdsLocBit μ ρ) R.locBits (critLocs s) ∧
    List.Forall₂ (holdsVarBit μ ρ) R.varBits (critVars s)

  -- Agreement under regime as an elementwise relation, then lifted with Forall₂
  inductive agreeLocUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
      : Bool → LocEntry → Prop where
    | true_eq (le : LocEntry)
        (h : μ₁.get? le.addr = μ₂.get? le.addr) :
        agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ true le
    | false_none (le : LocEntry)
        (hnone : le.qt.pred = none) :
        agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ false le
    | false_some (le : LocEntry)
        (hsome : ∃ tp, le.qt.pred = some tp)
        (h1 : ∃ n1, μ₁.get? le.addr = some n1 ∧ ¬ qtypPredHolds le.qt μ₁ ρ₁ (Value.num n1))
        (h2 : ∃ n2, μ₂.get? le.addr = some n2 ∧ ¬ qtypPredHolds le.qt μ₂ ρ₂ (Value.num n2)) :
        agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ false le

  inductive agreeVarUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
      : Bool → VarEntry → Prop where
    | true_eq (ve : VarEntry)
        (h : VarEnv.get ρ₁ ve.name = VarEnv.get ρ₂ ve.name) :
        agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ true ve
    | false_none (ve : VarEntry)
        (hnone : ve.qt.pred = none) :
        agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ false ve
    | false_some (ve : VarEntry)
        (hsome : ∃ tp, ve.qt.pred = some tp)
        (h1 : ∃ v1, VarEnv.get ρ₁ ve.name = some v1 ∧ ¬ qtypPredHolds ve.qt μ₁ ρ₁ v1)
        (h2 : ∃ v2, VarEnv.get ρ₂ ve.name = some v2 ∧ ¬ qtypPredHolds ve.qt μ₂ ρ₂ v2) :
        agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ false ve

  def agreeOnCriticalInputsUnderRegimeSpec
    (R : Regime) (s : InputSpec)
    (μ₁ : Memory) (ρ₁ : VarEnv)
    (μ₂ : Memory) (ρ₂ : VarEnv) : Prop :=
    List.Forall₂ (agreeLocUnder μ₁ ρ₁ μ₂ ρ₂) R.locBits (critLocs s) ∧
    List.Forall₂ (agreeVarUnder μ₁ ρ₁ μ₂ ρ₂) R.varBits (critVars s)

  -- =================================================
  -- Non-Interference property
  -- =================================================
  def NonInterferenceSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) : Prop :=
    wfInputSpec s →
    ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
      (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
      inputsConformSpec s μ₁ ρ₁ → inputsConformSpec s μ₂ ρ₂ →
      consistentRegimeSpec R s μ₁ ρ₁ → consistentRegimeSpec R s μ₂ ρ₂ →
      agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂ →
      terminatesTo e (mkInit μ₁ ρ₁) cf₁ o₁ →
      terminatesTo e (mkInit μ₂ ρ₂) cf₂ o₂ →
      observablesEqual obs cf₁ cf₂ o₁ o₂

  -- Type system enforces Non-Interference (spec-based statement only)
  theorem TypeSystemEnforcesNonInterference_spec
    (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
    wfInputSpec s →
    (∃ (ctx0 : TypeContext),
        ctxMatchesSpec s ctx0 ∧
        ∃ (fuel : Nat) (res : TypeResult),
          typecheck ctx0 e fuel = .ok res ∧
          ((match obs.retEtyp? with | some et => res.qualType.etyp = et | none => True) ∧
           (∀ l et, (l, et) ∈ obs.Lobs → ∃ qt, res.memEnv'.get? l = some qt ∧ qt.etyp = et)) ∧
        (∀ (μ : Memory) (ρ : VarEnv), inputsConformSpec s μ ρ → runtimeInstantiatesCtx ctx0 μ ρ)) →
    NonInterferenceSpec e s obs := by
    intro _wf _assm
    -- Proof to be developed
    sorry

end NonInterference
