-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2
import Std.Data.HashMap
open Std

-- ================================================================
-- Non-Interference (semantic formulation)
-- ================================================================

-- Big-step termination relation to a final configuration and result
-- (coincides with the reflexive-transitive closure of small-step evaluation).
-- TODO: make it return Value
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure (Except.ok (c₁, out.toValue?.getD Value.unit)) ∧
    out.toExpr? = none

abbrev MemoryETypEnv := HashMap Address ETyp
namespace MemoryETypEnv

  @[inline] def lookup (m : MemoryETypEnv) (a : Address) : Option ETyp :=
    m.get? a

  @[inline] def update (m : MemoryETypEnv) (a : Address) (qt : ETyp) : MemoryETypEnv :=
    m.insert a qt

  /-- `m` contains a binding for `a`. -/
  def hasKey (m : MemoryETypEnv) (a : Address) : Prop :=
    m.contains a

end MemoryETypEnv

-- What parts of the final state are observable
structure ObservableSpec where
  locs       : MemoryETypEnv
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
  -- for `s.locs` we don't need to check uniqueness because it is implemented as a HashMap

-- Regime: partial mapping from guard tags to their truth values.
-- A regime R : K_S → {true, false} assigns a truth value to each guard tag
-- that occurs in predicates attached to entries of the input specification S.
-- We model this as Tag → Option Bool where the regime is defined exactly for
-- tags appearing in S (enforced by wfRegime predicate).
abbrev Regime := Tag → Option Bool

-- Extract the guard tag from a QTyp's predicate (if it has one)
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

-- Extract all guard tags from the input specification
def inputSpecTags (s : InputSpec) : List Tag :=
  let locTags := s.locs.toList.filterMap (fun (_, qt) => qtypGuardTag qt)
  let varTags := s.vars.filterMap (fun (_, qt) => qtypGuardTag qt)
  locTags ++ varTags

-- Predicate-shape helpers
def isGuardClosure (qt : QTyp) : Prop :=
  ∃ k arg_name pred_body var_env, qt.pred = Predicate.guardClosure k arg_name pred_body var_env

def isGuardOnly (qt : QTyp) : Prop :=
  ∃ k, qt.pred = Predicate.guardOnly k

-- Regime is well-formed with respect to spec S if it's defined exactly for tags in S
def wfRegime (R : Regime) (s : InputSpec) : Prop :=
  let tags := inputSpecTags s
  (∀ k, k ∈ tags → (R k).isSome) ∧
  (∀ k, (R k).isSome → k ∈ tags)

inductive wfRegimeForReturn (R : Regime) : QTyp → Prop where
  | noPred (retType : QTyp)
      (hpred : retType.pred = Predicate.noPred) :
      wfRegimeForReturn R retType
  | guardOnly (retType : QTyp) (k : Tag)
      (hpred : retType.pred = Predicate.guardOnly k)
      (hregime : R k = some true) :
      wfRegimeForReturn R retType
  | guardClosure (retType : QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (hpred : retType.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some true) :
      wfRegimeForReturn R retType

-- Abstract predicate: does the QTyp-attached predicate hold for the given
-- input value under the initial environments? For locations the value will be
-- encoded as Value.num n; for variables it is the variable's Value.
--
-- We implement this as an inductive predicate for easier inversion in proofs.
-- The noPred case holds trivially; the guardClosure case requires evidence that the
-- predicate body terminates to `true` when evaluated with the argument bound;
-- the guardOnly case holds trivially (no syntactic test to check).
inductive qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop where
  | noPred_ok {qt : QTyp} {μ ρ v}
      (h : qt.pred = Predicate.noPred) :
      qtypPredHolds qt μ ρ v
  | guardClosure_ok {qt : QTyp} {μ ρ v k arg_name pred_body var_env}
      (cfg : Config)
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hterm : terminatesTo (PExpr.toExpr pred_body)
                  { memory := μ, varEnv := VarEnv.update ρ arg_name v, nextLoc := 0, pureMode := true }
                  cfg (ExprOrValue.value (Value.bool true))) :
      qtypPredHolds qt μ ρ v
  | guardOnly_ok {qt : QTyp} {μ ρ v k}
      (h : qt.pred = Predicate.guardOnly k) :
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
      valueHasETyp (Value.peClosure x pe env) (ETyp.parrow st1 st2 p tcl)

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
  let sameMem : Prop := ∀ {l et}, obs.locs.lookup l = some et → c₁.memory.lookup l = c₂.memory.lookup l
  -- If the return is observable (retEtyp? = some et), we require the final
  -- values to match If the return is not observable (retEtyp? = none), we do
  -- not constrain it here.
  let sameRet : Prop := obs.retEtyp? = none ∨ o₁ = o₂
  sameMem ∧ sameRet

-- Helper: check if guard tag present
def hasGuardTag (p : Predicate) : Bool :=
  match p with
  | Predicate.noPred => false
  | _ => true

-- Well-formedness: memory stores integers at critical locations; additionally,
-- align predicate and poison for critical inputs: no predicate ⇒ clean;
-- predicate present ⇒ initially poisoned.
def wfInputSpec (s : InputSpec) : Prop :=
  inputKeysUnique s ∧
  (∀ l qt, s.locs.lookup l = some qt →
     qt.etyp = ETyp.int ∧ qt.poison = hasGuardTag qt.pred) ∧
  (∀ x qt, s.vars.lookup x = some qt →
     qt.poison = hasGuardTag qt.pred)

-- Well-formedness: observable spec
-- Always correct by construction
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
  (∀ {l qt}, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = Predicate.noPred) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = Predicate.noPred)

-- Runtime conforms to the spec for critical inputs only. Unlisted inputs are
-- unconstrained here (we quantify over them), but concrete runs must still
-- instantiate the initial typing context (see the theorem premise below).
def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  (∀ {l}, s.locs.contains l → μ.contains l) ∧
  (∀ {x qt v}, s.vars.lookup x = some qt → ρ.lookup x = some v → valueHasETyp v qt.etyp)

-- Elementwise predicate for location regime consistency (inductive for easy inversion)
inductive locsRegime (R : Regime) (μ : Memory) (ρ : VarEnv) : (Address × QTyp) → Prop where
  | noPred_ok (entry : Address × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      locsRegime R μ ρ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Address × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      locsRegime R μ ρ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Address × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (n : Int) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some b)
      (hmem : μ.lookup entry.fst = some n)
      (hconsist : (b = true → qtypPredHolds entry.snd μ ρ (Value.num n)) ∧
                  (b = false → ¬qtypPredHolds entry.snd μ ρ (Value.num n))) :
      locsRegime R μ ρ entry

-- Elementwise predicate for variable regime consistency (inductive for easy inversion)
inductive varsRegime (R : Regime) (μ : Memory) (ρ : VarEnv) : (Name × QTyp) → Prop where
  | noPred_ok (entry : Name × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      varsRegime R μ ρ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Name × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      varsRegime R μ ρ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Name × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : List (Name × QTyp))
      (v : Value) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R k = some b)
      (hvar : ρ.lookup entry.fst = some v)
      (hconsist : (b = true → qtypPredHolds entry.snd μ ρ v) ∧
                  (b = false → ¬qtypPredHolds entry.snd μ ρ v)) :
      varsRegime R μ ρ entry

-- Regime consistency (via Forall over lists).
-- The regime must be defined for all critical inputs in the spec.
def consistentRegimeSpec (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  List.Forall (locsRegime R μ ρ) s.locs.toList ∧
  List.Forall (varsRegime R μ ρ) s.vars

-- Two values agree under a given regime and memory environments
inductive agreeValueUnder (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv) (qt: QTyp) (v₁ v₂ : Value) : Prop where
  | noPred_eq
      (hpred : qtypGuardTag qt = none)
      (hagree : v₁ = v₂) :
      agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt v₁ v₂
  | withPred_true_eq (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some true)
      (hagree : v₁ = v₂) :
      agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt v₁ v₂
  -- False-regime case for guard-closures: both runs fail the predicate
  | withPred_false_both_fail (k : Tag)
      (hclos : isGuardClosure qt)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some false)
      -- TODO: potential bug here: predicate must use captured variables, not ρ
      (hfail1 : ¬qtypPredHolds qt μ₁ ρ₁ v₁)
      (hfail2 : ¬qtypPredHolds qt μ₂ ρ₂ v₂) :
      agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt v₁ v₂
  -- False-regime case for guard-only: unconstrained (values may differ)
  | guardOnly_false_any (k : Tag)
      (hgo : qt.pred = Predicate.guardOnly k)
      (hregime : R k = some false) :
      agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt v₁ v₂

-- Two initial states agree on a critical location under a given regime.
-- Refactored to use agreeValueUnder
inductive agreeLocUnder (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : (Address × QTyp) → Prop where
  | agree_values (addr : Address) (qt : QTyp) (n₁ n₂ : Nat)
      (hlookup1 : μ₁.lookup addr = some n₁)
      (hlookup2 : μ₂.lookup addr = some n₂)
      (hagree : agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt (Value.num n₁) (Value.num n₂)) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)
  | both_none (addr : Address) (qt : QTyp)
      (hlookup1 : μ₁.lookup addr = none)
      (hlookup2 : μ₂.lookup addr = none) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)

-- Two initial states agree on a critical variable under a given regime.
-- Refactored to use agreeValueUnder
inductive agreeVarUnder (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : (Name × QTyp) → Prop where
  | agree_values (x : Name) (qt : QTyp) (v₁ v₂ : Value)
      (hlookup1 : ρ₁.lookup x = some v₁)
      (hlookup2 : ρ₂.lookup x = some v₂)
      (hagree : agreeValueUnder R μ₁ ρ₁ μ₂ ρ₂ qt v₁ v₂) :
      agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂ (x, qt)
  | both_none (x : Name) (qt : QTyp)
      (hlookup1 : ρ₁.lookup x = none)
      (hlookup2 : ρ₂.lookup x = none) :
      agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂ (x, qt)

-- Two initial states agree on critical inputs under a given regime.
def agreeOnCriticalInputsUnderRegimeSpec
  (R : Regime) (s : InputSpec)
  (μ₁ : Memory) (ρ₁ : VarEnv)
  (μ₂ : Memory) (ρ₂ : VarEnv) : Prop :=
  List.Forall (agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂) s.locs.toList ∧
  List.Forall (agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂) s.vars

-- Typing results must satisfy the observable constraints:
def ObsConstraints (obs : ObservableSpec) (res : TypeResult) : Prop :=
  -- (i) If the return value is observable, require the inferred return
  -- enriched type to match the observable enriched type. If the return
  -- is not observable, no constraint is imposed on the result type.
  let retMatches : Prop :=
    ∀ et, obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false
  -- (ii) the memory must contain entries for each observable location
  -- with the correct enriched type
  let memMatches : Prop :=
    ∀ l et, obs.locs.lookup l = some et → ∃ qt, (res.memEnv'.lookup l = some qt ∧ qt.etyp = et ∧ qt.poison = false)
  retMatches ∧ memMatches

-- --------------------------- Internal fomulation used in proofs ----------------------------------------

-- Parition context into critical and non-critical
structure PartitionSpec where
  locs:  List Address
  vars:  List Name

-- Well-formedness: partition specification
-- Trivially true - duplicates in partitions are handled by conversion
-- (HashMap.insert for locs, and wfInputSpec ensures result is well-formed for vars)
def wfPartitionSpec (_s : PartitionSpec) : Prop := True

-- Context matches partition specification
-- all locations and variables in the partition specification must be present in the context
def ctxMatchesPartitionSpec (s : PartitionSpec) (ctx : TypeContext) : Prop :=
  (∀ l, l ∈ s.locs → ctx.memEnv.contains l) ∧
  (∀ x, x ∈ s.vars → ctx.varEnv.hasKey x)

-- Convert partition specification to input specification
-- all locations and variables in the partition specification must be present in the context
-- which is normally ensured by `ctxMatchesPartitionSpec`
-- TODO: this could be a logical relation between PartitionSpec, Context and InputSpec
def partionSpecToInputSpec (S : PartitionSpec) (ctx : TypeContext) : InputSpec :=
  InputSpec.mk
    (S.locs.foldl (init := {}) fun acc l =>
      match ctx.memEnv.lookup l with
      | some qt => acc.insert l qt
      | none => acc)
    (S.vars.foldl (init := []) fun acc x =>
      match ctx.varEnv.lookup x with
      | some qt => (x, qt) :: acc
      | none => acc)

-- Convert partition specification and return type to observable specification
-- Extract enriched types from qualified types in the context
-- Only non-poisoned locations and return values are observable
-- TODO: this could be a logical relation between PartitionSpec, Context and ObservableSpec
def partitionSpecToObservableSpec (S : PartitionSpec) (retType : QTyp) (ctx : TypeContext) : ObservableSpec :=
  ObservableSpec.mk
    -- Extract enriched types for observable locations (only non-poisoned)
    (S.locs.foldl (init := {}) fun acc l =>
      match ctx.memEnv.lookup l with
      | some qt => if qt.poison then acc else acc.insert l qt.etyp
      | none => acc)
    -- Return enriched type (only if not poisoned)
    (if retType.poison then none else some retType.etyp)

-- `i` and `o` subscript indexes correspond to input and outputs
-- `0` and `1` subscript indexes correspond to two runs of the program
def NonInterferenceSpec_step
  (e : Expr)
  (Sᵢ Sₒ: PartitionSpec)
  (ctxᵢ ctxₒ: TypeContext)
  (retType: QTyp)
  : Prop :=
    -- Ensure well-formedness and consistency of arguments
    wfPartitionSpec Sᵢ →  ctxMatchesPartitionSpec Sᵢ ctxᵢ →
    wfPartitionSpec Sₒ →  ctxMatchesPartitionSpec Sₒ ctxₒ →
    -- Convert partition specification to input specification, do not need Sᵢ after this
    forall sᵢ,
      sᵢ = partionSpecToInputSpec Sᵢ ctxᵢ →
      -- We universally quantify over the input regime Rᵢ
      ∀ (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (Rᵢ: Regime)
        (cf₀ cf₁ : Config) (o₀ o₁ : ExprOrValue),
        wfRegime Rᵢ sᵢ →
        inputsConformSpec sᵢ μ₀ ρ₀ →  inputsConformSpec sᵢ μ₁ ρ₁ →
        runtimeInstantiatesCtx ctxᵢ μ₀ ρ₀ →  runtimeInstantiatesCtx ctxᵢ μ₁ ρ₁ →
        consistentRegimeSpec Rᵢ sᵢ μ₀ ρ₀ → consistentRegimeSpec Rᵢ sᵢ μ₁ ρ₁ →
        agreeOnCriticalInputsUnderRegimeSpec Rᵢ sᵢ μ₀ ρ₀ μ₁ ρ₁ →
        forall (l : Address) (pm : Bool),
          terminatesTo e { memory := μ₀, varEnv := ρ₀, nextLoc := l, pureMode := pm } cf₀ o₀ →
          terminatesTo e { memory := μ₁, varEnv := ρ₁, nextLoc := l, pureMode := pm } cf₁ o₁ →
          -- Output properties below:
          -- Convert partition specification to input specification, do not need Sₒ after this
          forall sₒ,
            sₒ = partionSpecToInputSpec Sₒ ctxₒ →
            -- Rₒ is output regime
            exists Rₒ,
              wfRegime Rₒ sₒ ∧
              wfRegimeForReturn Rₒ retType → -- return type tag may appear only in output
              consistentRegimeSpec Rₒ sₒ cf₀.memory cf₀.varEnv ∧ consistentRegimeSpec Rₒ sₒ cf₁.memory cf₁.varEnv ∧
              agreeOnCriticalInputsUnderRegimeSpec Rₒ sₒ cf₀.memory cf₀.varEnv cf₁.memory cf₁.varEnv
              --TODO: /\ agreeValueUnder Rₒ cf₀.memory cf₀.varEnv cf₁.memory cf₁.varEnv retType o₀ o₁

def ctxMatchesResult (ctx : TypeContext) (res : TypeResult) : Prop :=
  ctx.memEnv = res.memEnv'

-- Sᵢ Sₒ - input and output partition specifications
def TypeSystemEnforcesNonInterference_step_spec
  (e : Expr)
  (Sᵢ Sₒ: PartitionSpec)
  (ctxᵢ ctxₒ: TypeContext)
  (retType: QTyp) -- return type
  : Prop :=
    -- Ensure well-formedness and consistency of arguments
    wfPartitionSpec Sᵢ →  ctxMatchesPartitionSpec Sᵢ ctxᵢ →
    wfPartitionSpec Sₒ →  ctxMatchesPartitionSpec Sₒ ctxₒ →
    -- Fuel-based termination of typechecking
    (∃ (fuel : Nat) (res : TypeResult),
      -- If typechecking succeeds,
      typecheck ctxᵢ e fuel = .ok res →
      -- and the result must match the output context
      ctxMatchesResult ctxₒ res →
      -- then the program satisfies non-interference
      NonInterferenceSpec_step e Sᵢ Sₒ ctxᵢ ctxₒ retType)

-- ------------------------ Top-level definitions -------------------------------

-- Non-Interference property
-- ==========================
def NonInterferenceSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (l : Address) (pm : Bool) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
    wfRegime R s →
    inputsConformSpec s μ₁ ρ₁ →  inputsConformSpec s μ₂ ρ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ →
    consistentRegimeSpec R s μ₁ ρ₁ →  consistentRegimeSpec R s μ₂ ρ₂ →
    agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂ →
    terminatesTo e { memory := μ₁, varEnv := ρ₂, nextLoc := l, pureMode := pm } cf₁ o₁ →
    terminatesTo e { memory := μ₁, varEnv := ρ₂, nextLoc := l, pureMode := pm } cf₂ o₂ →
    observablesEqual obs cf₁ cf₂ o₁ o₂

-- Type system enforces Non-Interference
def TypeSystemEnforcesNonInterference_spec
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      ((∃ (fuel : Nat) (res : TypeResult),
        typecheck ctx e fuel = .ok res ∧
        ObsConstraints obs res) →
        NonInterferenceSpec e s obs ctx)

-- ------------------------ Proofs -------------------------------
--
-- PROOF STRATEGY:
-- ================
-- Prove that TypeSystemEnforcesNonInterference_step_spec (partition-based)
-- implies TypeSystemEnforcesNonInterference_spec (input/observable-based).
--
-- The proof uses supporting lemmas to derive context matching from conversions.
--
-- SUPPORTING LEMMAS:
-- ==================
--
-- ctxMatchesPartition_from_inputSpec:
--   Not provable as stated. The conversion filters elements not in context, so we
--   cannot prove the backward direction: l ∈ S.locs → l ∈ ctx.memEnv.
--   Left with sorry.
--
-- ctxMatchesPartition_from_obsSpec:
--   Not provable as stated. Same filtering issue for locations, and the conversion
--   doesn't use S.vars at all.
--   Left with sorry.
--

-- Derive partition-context matching from conversion equality.
-- Not provable: conversion filters elements not in context.
lemma ctxMatchesPartition_from_inputSpec
  (S : PartitionSpec) (ctx : TypeContext) (s : InputSpec)
  (h_convert : partionSpecToInputSpec S ctx = s)
  (h_matches : ctxMatchesInputSpec s ctx) :
  ctxMatchesPartitionSpec S ctx := by
  unfold ctxMatchesPartitionSpec
  constructor
  · -- Show: ∀ l, l ∈ S.locs → ctx.memEnv.contains l
    intro l hl
    sorry
  · -- Show: ∀ x, x ∈ S.vars → ctx.varEnv.hasKey x
    intro x hx
    sorry

-- Derive partition-context matching from observable conversion.
-- Not provable: conversion filters locations and doesn't use S.vars.
lemma ctxMatchesPartition_from_obsSpec
  (S : PartitionSpec) (retType : QTyp) (ctx : TypeContext) (obs : ObservableSpec)
  (h_convert : partitionSpecToObservableSpec S retType ctx = obs) :
  ctxMatchesPartitionSpec S ctx := by
  unfold ctxMatchesPartitionSpec
  constructor
  · -- Show: ∀ l, l ∈ S.locs → ctx.memEnv.contains l
    intro l hl
    sorry
  · -- Show: ∀ x, x ∈ S.vars → ctx.varEnv.hasKey x
    intro x hx
    sorry

-- Bridge theorem: TypeSystemEnforcesNonInterference_step_spec implies
-- TypeSystemEnforcesNonInterference_spec.
--
-- If there exists a partition decomposition (Sᵢ, Sₒ, retType) such that:
-- - Sᵢ converts to the input spec s
-- - Sₒ and retType convert to the observable spec obs
-- - The step specification holds for this decomposition
-- Then the general specification holds.
theorem step_spec_implies_general_spec
  -- ========== INPUTS (same as TypeSystemEnforcesNonInterference_spec) ==========
  (e : Expr)         -- The expression to check
  (s : InputSpec)    -- Input specification (critical locations and variables)
  (obs : ObservableSpec)  -- Observable specification (what outputs are observable)
  -- ========== WELL-FORMEDNESS PRECONDITIONS ==========
  (hwf_s : wfInputSpec s)
  (hwf_obs : wfObsSpec obs)
  -- ========== MAIN HYPOTHESIS: Existence of suitable partition decomposition ==========
  (h_exists_partition : ∃ (Sᵢ Sₒ : PartitionSpec) (retType : QTyp),
    -- Partitions must be well-formed (trivially True, but kept for clarity)
    wfPartitionSpec Sᵢ ∧
    wfPartitionSpec Sₒ ∧
    -- All hypotheses hold for all relevant contexts
    ∀ (ctxᵢ ctxₒ : TypeContext),
      -- H1: The input partition Sᵢ must represent the same critical inputs as s
      (ctxMatchesInputSpec s ctxᵢ → partionSpecToInputSpec Sᵢ ctxᵢ = s) ∧
      -- H2: The output partition Sₒ and retType must represent the same observables as obs
      (partitionSpecToObservableSpec Sₒ retType ctxₒ = obs) ∧
      -- H3: The step specification holds for this decomposition
      (TypeSystemEnforcesNonInterference_step_spec e Sᵢ Sₒ ctxᵢ ctxₒ retType)) :
  -- ========== CONCLUSION ==========
  TypeSystemEnforcesNonInterference_spec e s obs := fun _hwf_s _hwf_obs => by
  -- Extract the partition decomposition from the existential
  obtain ⟨Sᵢ, Sₒ, retType, hwf_Sᵢ, hwf_Sₒ, h_partition⟩ := h_exists_partition

  -- Unfold TypeSystemEnforcesNonInterference_spec
  intro ctx hctx_matches_s
  intro ⟨fuel, res, htypecheck, hobs_constraints⟩

  -- Unfold NonInterferenceSpec
  intro μ₁ μ₂ ρ₁ ρ₂ l pm R cf₁ cf₂ o₁ o₂
  intro hwf_R hconform₁ hconform₂ hinst₁ hinst₂ hconsist₁ hconsist₂ hagree hterm₁ hterm₂

  -- Goal: observablesEqual obs cf₁ cf₂ o₁ o₂

  -- Instantiate partition hypothesis with ctx
  have h_ctx := h_partition ctx ctx
  obtain ⟨h_input_equiv, h_obs_equiv, h_step_spec⟩ := h_ctx

  -- Derive conversion equalities
  have h_input_eq : partionSpecToInputSpec Sᵢ ctx = s := h_input_equiv hctx_matches_s
  have h_obs_eq := h_obs_equiv

  -- Derive context matching (using lemmas with sorry)
  have hctx_Sᵢ : ctxMatchesPartitionSpec Sᵢ ctx :=
    ctxMatchesPartition_from_inputSpec Sᵢ ctx s h_input_eq hctx_matches_s
  have hctx_Sₒ : ctxMatchesPartitionSpec Sₒ ctx :=
    ctxMatchesPartition_from_obsSpec Sₒ retType ctx obs h_obs_eq

  -- Remaining proof gaps:
  --
  -- 1. Need ctxMatchesResult ctx res to apply step spec.
  --    This requires ctx.memEnv = res.memEnv', which is not derivable from current hypotheses.
  --
  -- 2. The step spec provides regime-based agreement on critical outputs.
  --    Need to prove this implies observablesEqual obs cf₁ cf₂ o₁ o₂.
  --    Requires connecting NonInterferenceSpec_step output (regime agreement) to
  --    NonInterferenceSpec output (observable equality).

  sorry
