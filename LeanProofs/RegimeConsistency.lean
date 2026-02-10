-- Regime consistency definitions shared by Preservation and FaultRobustness.
-- Extracted for Issue #112 fix to avoid circular imports.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties

-- Abstract predicate satisfaction: does a predicate with the given tag hold
-- for a value in a given memory state?
abbrev PredSat := Tag → Memory → Value → Prop

-- Laws that constrain the abstract `PredSat` relation.
structure PredSatLaws (predSat : PredSat) : Prop where
  -- Bidirectional match law: if match_guard recognizes the condition as tag k,
  -- then the condition's boolean result matches predSat on the owning value.
  match_iff : ∀ (mode : LeanPoison.EvalMode) (condition : Expr) (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
                  (k : Tag) (deps : Deps)
                  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (addr : Address) (pm : Bool) (cfg : Config)
                  (v : Value) (b : Bool),
    matchGuard condition Γ σ = .ok (k, deps) →
    terminatesTo mode condition { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm } cfg (Value.bool b) →
    ( (∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧
          qtypGuardTag qt = some k ∧
          ρ.lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (t : ETyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref t ls ∧
          l0 ∈ ls ∧
          Γ.lookup l0 = some memQt ∧
          qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) →
    (b = true ↔ predSat k μ v)

  mem_monotone : ∀ (k : Tag) (pred : Predicate) (μ μ' : Memory) (v : Value) (deps : Deps) (θ : RealizationMap),
    extractDepsFromPred pred = .ok deps →
    (∀ l, l ∈ deps → ∀ a, θ.lookup l = some a → μ.lookup a = μ'.lookup a) →
    (predSat k μ v ↔ predSat k μ' v)

-- Check if a QTyp-attached predicate holds using abstract satisfaction relation
inductive qtypPredHolds (predSat : PredSat) : QTyp → Memory → Value → Prop where
  | noPred_ok {qt : QTyp} {μ v}
      (h : qt.pred = Predicate.noPred) :
      qtypPredHolds predSat qt μ v
  | guardClosure_ok {qt : QTyp} {μ v k arg_name pred_body var_env}
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v
  | guardOnly_ok {qt : QTyp} {μ v k}
      (h : qt.pred = Predicate.guardOnly k)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v

-- Elementwise predicate for location regime consistency (inductive for easy inversion)
inductive locsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) : (Loc × QTyp) → Prop where
  | noPred_ok (entry : Loc × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      locsRegime predSat R μ θ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Loc × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      locsRegime predSat R μ θ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Loc × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
      (a : Address) (n : Int) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hreal : θ.lookup entry.fst = some a)
      (hmem : μ.lookup a = some n)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ (Value.num n)) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ (Value.num n))) :
      locsRegime predSat R μ θ entry

-- Elementwise predicate for variable regime consistency (inductive for easy inversion)
inductive varsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (ρ : VarEnv) : (Name × QTyp) → Prop where
  | noPred_ok (entry : Name × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      varsRegime predSat R μ ρ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Name × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      varsRegime predSat R μ ρ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Name × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
      (v : Value) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hvar : ρ.lookup entry.fst = some v)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ v) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ v)) :
      varsRegime predSat R μ ρ entry

-- Context-indexed runtime-regime consistency: constrains only tags the regime interprets
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l qt k, ctx.memEnv.lookup l = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     locsRegime predSat R μ θ (l, qt)) ∧
  (∀ x qt k, ctx.varEnv.lookup x = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     varsRegime predSat R μ ρ (x, qt))
