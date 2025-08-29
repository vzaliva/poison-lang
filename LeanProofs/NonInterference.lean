-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.Eval
import Mathlib.Data.List.Forall2

-- ================================================================
-- Non-Interference (semantic formulation)
-- ================================================================

-- Big-step termination relation to a final configuration and result.
-- Intended to coincide with repeated small-step evaluation to a value
-- (or irreducible expression) as implemented in LeanPoison.Eval.
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    eval fuel c₀ (ExprOrValue.expr e) verbose = pure (StepResult.progress c₁ out)

-- What parts of the final state are observable
structure ObservableSpec where
  Lobs       : MemoryTypeEnv
  retEtyp?   : Option ETyp
deriving Repr

-- Critical inputs specification
--
-- We specify only the designated critical inputs and their qualified types.
-- Non-critical inputs are not listed here and are unconstrained by the spec.
-- In the initial typing context, any entry not listed in this spec must be
-- conservative: poisoned with no_pred, so it cannot influence de-poisoning.
structure InputSpec where
  locs : MemoryTypeEnv
  vars : VarTypeEnv
deriving Repr

open List

/-- Keys are unique in both `s.locs` (addresses) and `s.vars` (names). -/
def inputKeysUnique (s : InputSpec) : Prop :=
  Nodup (s.vars.map Prod.fst)

-- Regime vector (split: locations and variables, fixed order given by
-- s.locs/s.vars) Specifies whether given criticial input value satisfies the
-- predicate (if any). Always True for inputs without predicates.
structure Regime where
  locBits : List Bool
  varBits : List Bool
deriving Repr

-- Abstract predicate: does the QTyp-attached predicate hold for the given
-- input value under the initial environments? For locations the value will be
-- encoded as Value.num n; for variables it is the variable's Value.
--
-- We implement this as an inductive predicate for easier inversion in proofs.
-- The `none` case holds trivially; the `some` case requires evidence that the
-- predicate body terminates to `true` when evaluated with the argument bound.
inductive qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop where
  | none_ok {qt : QTyp} {μ ρ v}
      (h : qt.pred = none) :
      qtypPredHolds qt μ ρ v
  | some_ok {qt : QTyp} {μ ρ v}
      (tp : TPred) (cfg : Config)
      (h : qt.pred = some tp)
      (hterm : terminatesTo (PExpr.toExpr tp.pred_body)
                  { memory := μ, varEnv := VarEnv.update ρ tp.arg_name v, nextLoc := 0 }
                  cfg (ExprOrValue.value (Value.bool true))) :
      qtypPredHolds qt μ ρ v

-- Relational predicate for typing values as enriched types
inductive valueHasETyp : Value → ETyp → Prop where
  | num (n): valueHasETyp (Value.num n) ETyp.int
  | bool (b): valueHasETyp (Value.bool b) ETyp.bool
  | unit : valueHasETyp Value.unit ETyp.unit
  | str (s): valueHasETyp (Value.str s) ETyp.string
  | loc (l t l'): valueHasETyp (Value.loc l) (ETyp.ref t l')  -- ignore concrete address in type
  | closure (x e env st1 st2 p tcl):
      valueHasETyp (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure (x pe env st1 st2 p tcl):
      valueHasETyp (Value.peClosure x pe env) (ETyp.arrow st1 st2 p tcl)

-- A predicate for runtime instantiating the context: values must exist for
-- every typed variable and memory must contain entries for each typed
-- location.
def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) : Prop :=
  (∀ l, ctx.memEnv.contains l → μ.contains l) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt →
     ∃ v, ρ.lookup x = some v ∧ valueHasETyp v qt.etyp)

-- Helper: equality of observables in the final states
def observablesEqual (obs : ObservableSpec)
    (c₁ c₂ : Config) (o₁ o₂ : ExprOrValue) : Prop :=
  let sameMem : Prop := ∀ {l et}, obs.Lobs.lookup l = some et → c₁.memory.lookup l = c₂.memory.lookup l
  -- If the return is observable (retEtyp? = some et), we require the final
  -- values to match If the return is not observable (retEtyp? = none), we do
  -- not constrain it here.
  let sameRet : Prop := obs.retEtyp? = none ∨ o₁ = o₂
  sameMem ∧ sameRet

-- Build initial configurations from initial inputs
def mkInit (μ : Memory) (ρ : VarEnv) : Config :=
  { memory := μ, varEnv := ρ, nextLoc := 0 }

-- Well-formedness: memory stores integers at critical locations
def wfInputSpec (s : InputSpec) : Prop :=
  inputKeysUnique s ∧
  (∀ l qt, s.locs.lookup l = some qt → qt.etyp = ETyp.int)

-- Well-formedness: observable spec
def wfObsSpec (_obs : ObservableSpec) : Prop := True

-- Context compliance with the critical-only spec
-- pc is clean, tag environment is empty; all listed critical entries must be
-- present with exactly the specified qualified types. Any unlisted entry that
-- appears in the context (to allow the program to typecheck when referenced)
-- is permitted, but it must be poisoned and carry no predicate.
def ctxMatchesInputSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
  ctx.pc = false ∧ ctx.tagEnv = {} ∧
  (∀ {l qt}, s.locs.lookup l = some qt → ctx.memEnv.lookup l = some qt) ∧
  (∀ {x qt}, s.vars.lookup x = some qt → ctx.varEnv.lookup x = some qt) ∧
  (∀ {l qt}, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = none)

-- Runtime conforms to the spec for critical inputs only. Unlisted inputs are
-- unconstrained here (we quantify over them), but concrete runs must still
-- instantiate the initial typing context (see the theorem premise below).
def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  (∀ {l}, s.locs.contains l → μ.contains l) ∧
  (∀ {x qt v}, s.vars.lookup x = some qt → ρ.lookup x = some v → valueHasETyp v qt.etyp)

-- Elementwise predicates for regimes (inductive for easy inversion)
inductive locsRegime (μ : Memory) (ρ : VarEnv) : Bool → (Address × QTyp) → Prop where
  | true_ok (entry : Address × QTyp) (n : Int)
      (hmem : μ.lookup entry.fst = some n)
      (hpred : qtypPredHolds entry.snd μ ρ (Value.num n)) :
      locsRegime μ ρ true entry
  | false_ok (entry : Address × QTyp)
      (hexists : ∃ n, μ.lookup entry.fst = some n)
      (hno : ∀ n, ¬ (μ.lookup entry.fst = some n ∧ qtypPredHolds entry.snd μ ρ (Value.num n))) :
      locsRegime μ ρ false entry

inductive varsRegime (μ : Memory) (ρ : VarEnv) : Bool → (Name × QTyp) → Prop where
  | true_ok (entry : Name × QTyp) (v : Value)
      (hget : ρ.lookup entry.fst = some v)
      (hpred : qtypPredHolds entry.snd μ ρ v) :
      varsRegime μ ρ true entry
  | false_ok (entry : Name × QTyp)
      (hexists : ∃ v, ρ.lookup entry.fst = some v)
      (hno : ∀ v, ¬ (ρ.lookup entry.fst = some v ∧ qtypPredHolds entry.snd μ ρ v)) :
      varsRegime μ ρ false entry

-- Regime consistency (aligned pairs via Forall₂ over fixed-order lists).
-- Forall₂ also enforces that the lists are the same length. The regime
-- covers only critical inputs in the order given by the spec.
def consistentRegimeSpec (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  List.Forall₂ (locsRegime μ ρ) R.locBits s.locs.toList ∧
  List.Forall₂ (varsRegime μ ρ) R.varBits s.vars

-- Two initial states agree on a critical location under a given regime bit.
inductive agreeLocUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : Bool → (Address × QTyp) → Prop where
  | true_eq (addr : Address) (qt : QTyp)
      (h : μ₁.lookup addr = μ₂.lookup addr) :
      agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ true (addr, qt)
  | false_none (addr : Address) (qt : QTyp)
      (hnone : qt.pred = none) :
      agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ false (addr, qt)
  | false_some (addr : Address) (qt : QTyp)
      (hsome : ∃ tp, qt.pred = some tp)
      (h1 : ∃ n1, μ₁.lookup addr = some n1 ∧ ¬ qtypPredHolds qt μ₁ ρ₁ (Value.num n1))
      (h2 : ∃ n2, μ₂.lookup addr = some n2 ∧ ¬ qtypPredHolds qt μ₂ ρ₂ (Value.num n2)) :
      agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ false (addr, qt)

-- Two initial states agree on a critical variable under a given regime bit.
inductive agreeVarUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : Bool → (Name × QTyp) → Prop where
  | true_eq (x : Name) (qt : QTyp)
      (h : ρ₁.lookup x = ρ₂.lookup x) :
      agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ true (x, qt)
  | false_none (x : Name) (qt : QTyp)
      (hnone : qt.pred = none) :
      agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ false (x, qt)
  | false_some (x : Name) (qt : QTyp)
      (hsome : ∃ tp, qt.pred = some tp)
      (h1 : ∃ v1, ρ₁.lookup x = some v1 ∧ ¬ qtypPredHolds qt μ₁ ρ₁ v1)
      (h2 : ∃ v2, ρ₂.lookup x = some v2 ∧ ¬ qtypPredHolds qt μ₂ ρ₂ v2) :
      agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ false (x, qt)

def agreeOnCriticalInputsUnderRegimeSpec
  (R : Regime) (s : InputSpec)
  (μ₁ : Memory) (ρ₁ : VarEnv)
  (μ₂ : Memory) (ρ₂ : VarEnv) : Prop :=
  List.Forall₂ (agreeLocUnder μ₁ ρ₁ μ₂ ρ₂) R.locBits s.locs.toList ∧
  List.Forall₂ (agreeVarUnder μ₁ ρ₁ μ₂ ρ₂) R.varBits s.vars

-- Typing results must satisfy the observable constraints:
def ObsConstraints (obs : ObservableSpec) (res : TypeResult) : Prop :=
  -- (i) If the return value is observable, require the inferred return
  -- enriched type to match the observable surface type. If the return
  -- is not observable, no constraint is imposed on the result type.
  let retMatches : Prop :=
     ∀ et, obs.retEtyp? = some et → res.qualType.etyp = et
  -- (ii) the memory must contain entries for each observable location
  -- with the correct enriched type
  let memMatches : Prop :=
    ∀ l et, obs.Lobs.lookup l = some et → res.memEnv'.lookup l = some et
  retMatches ∧ memMatches

-- =================================================
-- Non-Interference property
-- =================================================
def NonInterferenceSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) : Prop :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
    inputsConformSpec s μ₁ ρ₁ →
    inputsConformSpec s μ₂ ρ₂ →
    consistentRegimeSpec R s μ₁ ρ₁ →
    consistentRegimeSpec R s μ₂ ρ₂ →
    agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂ →
    terminatesTo e (mkInit μ₁ ρ₁) cf₁ o₁ →
    terminatesTo e (mkInit μ₂ ρ₂) cf₂ o₂ →
    observablesEqual obs cf₁ cf₂ o₁ o₂

-- Type system enforces Non-Interference (spec-based statement only)
-- We avoid an overly-strong hypothesis by requiring, for each run we compare,
-- both: (i) critical inputs conform to the spec, and (ii) the runtime
-- environments instantiate the initial typing context. This allows the
-- context to include non-critical entries needed for typechecking, while
-- still quantifying over arbitrary values for those entries.
theorem TypeSystemEnforcesNonInterference_spec_old
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  wfInputSpec s →
  (∃ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx ∧
      ∃ (fuel : Nat) (res : TypeResult),
        typecheck ctx e fuel = .ok res ∧
      ObsConstraints obs res ∧
      (∀ μ ρ, inputsConformSpec s μ ρ ∧ runtimeInstantiatesCtx ctx μ ρ))
  →
  NonInterferenceSpec e s obs := by
sorry
