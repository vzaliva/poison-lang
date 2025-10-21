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

-- Two initial states agree on a critical location under a given regime.
inductive agreeLocUnder (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : (Address × QTyp) → Prop where
  | noPred_eq (addr : Address) (qt : QTyp)
      (hpred : qtypGuardTag qt = none)
      (hagree : μ₁.lookup addr = μ₂.lookup addr) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)
  | withPred_true_eq (addr : Address) (qt : QTyp) (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some true)
      (hagree : μ₁.lookup addr = μ₂.lookup addr) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)
  -- False-regime case for guard-closures: both runs fail the predicate
  | withPred_false_both_fail (addr : Address) (qt : QTyp) (k : Tag)
      (hclos : isGuardClosure qt)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some false)
      (hfail1 : ∃ n1, μ₁.lookup addr = some n1 ∧ ¬qtypPredHolds qt μ₁ ρ₁ (Value.num n1))
      (hfail2 : ∃ n2, μ₂.lookup addr = some n2 ∧ ¬qtypPredHolds qt μ₂ ρ₂ (Value.num n2)) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)
  -- False-regime case for guard-only: unconstrained (values may differ)
  | guardOnly_false_any (addr : Address) (qt : QTyp) (k : Tag)
      (hgo : qt.pred = Predicate.guardOnly k)
      (hregime : R k = some false) :
      agreeLocUnder R μ₁ ρ₁ μ₂ ρ₂ (addr, qt)

-- Two initial states agree on a critical variable under a given regime.
inductive agreeVarUnder (R : Regime) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : (Name × QTyp) → Prop where
  | noPred_eq (x : Name) (qt : QTyp)
      (hpred : qtypGuardTag qt = none)
      (hagree : ρ₁.lookup x = ρ₂.lookup x) :
      agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂ (x, qt)
  | withPred_true_eq (x : Name) (qt : QTyp) (k : Tag)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some true)
      (hagree : ρ₁.lookup x = ρ₂.lookup x) :
      agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂ (x, qt)
  -- False-regime case for guard-closures: both runs fail the predicate
  | withPred_false_both_fail (x : Name) (qt : QTyp) (k : Tag)
      (hclos : isGuardClosure qt)
      (htag : qtypGuardTag qt = some k)
      (hregime : R k = some false)
      (hfail1 : ∃ v1, ρ₁.lookup x = some v1 ∧ ¬qtypPredHolds qt μ₁ ρ₁ v1)
      (hfail2 : ∃ v2, ρ₂.lookup x = some v2 ∧ ¬qtypPredHolds qt μ₂ ρ₂ v2) :
      agreeVarUnder R μ₁ ρ₁ μ₂ ρ₂ (x, qt)
  -- False-regime case for guard-only: unconstrained (values may differ)
  | guardOnly_false_any (x : Name) (qt : QTyp) (k : Tag)
      (hgo : qt.pred = Predicate.guardOnly k)
      (hregime : R k = some false) :
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

-- --------------------------- WIP ----------------------------------------

-- Parition context into critical and non-critical
structure PartitionSpec where
  locs:  List Address
  vars:  List Name

def wfPartitionSpec (s : PartitionSpec) : Prop :=
  List.Nodup s.locs ∧ List.Nodup s.vars


def ctxMatchesPartitionSpec (s : PartitionSpec) (ctx : TypeContext) : Prop := sorry
/- Ex

; inputs a,b, outputs c
; a0,a1-critical, b-non-critical, c-observable

let d = a0 in
; a0,a1,d-critical, b-non-critical, d,c-observable
if a0 > 0
then
  if a1 > 0
  then
    c := d
  else
    c := a1
else
  c := b
-/

def consistentRegimeSpec_alt (R : Regime) (S : PartitionSpec) (μ : Memory) (ρ : VarEnv) : Prop := sorry

def wfRegime_alt (R : Regime) (S : PartitionSpec) (ctx : TypeContext) : Prop := sorry

def agreeOnCriticalInputsUnderRegimeSpec_alt (R : Regime) (S : PartitionSpec) (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv): Prop := sorry

def inputsConformPartitionSpec (S : PartitionSpec) (μ : Memory) (ρ : VarEnv) : Prop := sorry

def NonInterferenceSpec_alt (e : Expr)
(S₁ S₂ : PartitionSpec) (ctx₁ ctx₂: TypeContext)
: Prop :=
  wfPartitionSpec S₁ → wfPartitionSpec S₂ →
  ctxMatchesPartitionSpec S₁ ctx₁ → ctxMatchesPartitionSpec S₂ ctx₂ →

  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (l : Address) (pm : Bool) (R₁: Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
    wfRegime_alt R₁ S₁ ctx₁ →
    inputsConformPartitionSpec S₁ μ₁ ρ₁ →  inputsConformPartitionSpec S₁ μ₂ ρ₂ →
    runtimeInstantiatesCtx ctx₁ μ₁ ρ₁ →  runtimeInstantiatesCtx ctx₂ μ₂ ρ₂ →
    consistentRegimeSpec_alt R₁ S₁ μ₁ ρ₁ →  consistentRegimeSpec_alt R₁ S₂ μ₂ ρ₂ →
    agreeOnCriticalInputsUnderRegimeSpec_alt R₁ S₁ μ₁ ρ₁ μ₂ ρ₂ →
    terminatesTo e  { memory := μ₁, varEnv := ρ₂, nextLoc := l, pureMode := pm } cf₁ o₁ →
    terminatesTo e  { memory := μ₁, varEnv := ρ₂, nextLoc := l, pureMode := pm } cf₂ o₂ →
    exists R₂,
    wfRegime_alt R₂ S₂ ctx₂ ∧
    consistentRegimeSpec_alt R₂ S₂ cf₁.memory cf₁.varEnv ∧ consistentRegimeSpec_alt R₂ S₂ cf₂.memory cf₂.varEnv ∧
    agreeOnCriticalInputsUnderRegimeSpec_alt R₂ S₂ cf₁.memory cf₁.varEnv cf₂.memory cf₂.varEnv

def TypeSystemEnforcesNonInterference_spec_alt  (e : Expr) (S₁ S₂: PartitionSpec) : Prop :=
  wfPartitionSpec S₁ → wfPartitionSpec S₂ →
  ∀ (ctx₁ : TypeContext),
      ctxMatchesPartitionSpec S₁ ctx₁ →
      (∃ (fuel : Nat) (res : TypeResult),
        typecheck ctx₁ e fuel = .ok res →
        (∃ ctx₂,
          ctx₂.memEnv = res.memEnv' ∧
          ctx₂.varEnv = ctx₁.varEnv ∧
          ctxMatchesPartitionSpec S₂ ctx₂ ∧
          NonInterferenceSpec_alt e S₁ S₂ ctx₁ ctx₂))

-- ------------------------ OLD -------------------------------


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
