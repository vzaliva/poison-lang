# Issue 112 Proposal

## 1) Issue Link
- https://github.com/vzaliva/poison-lang/issues/112

## 2) Root Cause (brief)
- `typecheckIf` can commit to a single branch when `matchGuard` succeeds and `ctx.regime.lookup? k = some b`.
- Runtime `ite` always branches on the concrete boolean value produced by evaluating the condition.
- Current `Preservation` does not assume any relation between regime decisions and runtime guard outcomes.
- Therefore typed branch and runtime branch can diverge (the #112 witness).

## 3) Proposal: change `Preservation` definition itself (reuse existing FR assumptions)
No new semantic predicate is required. Reuse assumptions already present in StepFR proofs (`PredSatLaws` + `consistentWithRegime`) and add them directly to `Preservation`.

To preserve layering (`Preservation` foundational, FR above it), do **not** import `FaultRobustness` from `Preservation`.
Instead, extract the needed regime-consistency interfaces into a shared base module (suggested: `LeanProofs/RegimeConsistency.lean`) imported by both.

### Lean sketch
```lean
-- CHANGED in #112 fix: import shared regime-consistency defs
import LeanProofs.RegimeConsistency

/-- CHANGED in #112 fix:
    same postcondition as before, but with reused FR premises. -/
def Preservation (mode : LeanPoison.EvalMode) (e : Expr) (ctx : TypeContext) : Prop :=
  ∀ (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ : RealizationMap)
    (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value)
    (predSat : PredSat),
    wfTypeContext ctx →
    typecheck ctx e fuel_tc = .ok res →
    wfRealizationMap θ₀ →
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    PredSatLaws predSat →                                         -- ADDED
    consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →        -- ADDED
    wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } →
    terminatesTo mode e
      { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
      { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
      v →
    ∃ (θ₁ : RealizationMap),
      wfExtendsMap θ₀ θ₁ ∧
      valueHasETyp θ₁ v res.qualType.etyp ∧
      wfTypeResult res ∧
      runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ θ₁ ∧
      wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
```

Notes:
- This keeps the theorem name and postcondition shape.
- The only semantic strengthening is via assumptions already standard in FR development.
- For empty-regime runs (`R = emptyRegime`), conditionals are conservative joins, so these added assumptions are easy to satisfy.

Dependency refactor (required to avoid Preservation -> FR dependency):
- Create `LeanProofs/RegimeConsistency.lean` and move these definitions from `LeanProofs/FaultRobustness.lean`:
  - `PredSat`
  - `PredSatLaws`
  - `qtypPredHolds`
  - `locsRegime`
  - `varsRegime`
  - `consistentWithRegime`
- Keep FR-specific specs/properties in `LeanProofs/FaultRobustness.lean` (e.g. `InputSpec`, `ObservableSpec`, `wfRegime`, `consistentRegimeSpec`, agreement properties).
- Update imports:
  - `LeanProofs/Preservation.lean` imports `LeanProofs/RegimeConsistency`.
  - `LeanProofs/FaultRobustness.lean` imports `LeanProofs/RegimeConsistency`.

Additional proof obligations (explicit):
- `PredSatLaws.match_iff` needs a third premise (owner witness): existence of a variable-owner or reference-owner at runtime.
- This does not come for free from `matchGuard = .ok (...)`; it needs bridge lemmas.
- Suggested bridge lemmas (proof-level, not theorem interface):
  - `matchGuard_ok_owner_in_ctx`: from `matchGuard` success, extract owner shape in typing context (var-owner or ref-owner).
  - `owner_in_ctx_to_runtime`: using `runtimeInstantiatesCtx`, convert the typing owner into runtime witness required by `match_iff`.
- Ref-owner path is non-trivial: must use both parts of `runtimeInstantiatesCtx`
  - variable typing instantiation (to find reference value in `ρ`),
  - memory/realization instantiation (to find concrete address/value in `μ` via `θ`).
- Sanity check during implementation: `guardOnly` is intentionally excluded from regime-directed `if` branching
  (current `matchGuard` returns no match for `guardOnly`; regime consistency for guard-only does not constrain truth value).

Optional helper snippet (private, suggested):
```lean
/-- OPTIONAL proof helper (private): suggested way to avoid repeating the same
    branch-alignment argument in each `if` proof case.
    Not part of the theorem statement.
    Derived from existing FR assumptions:
    `PredSatLaws.match_iff` + `consistentWithRegime`. -/
private lemma guard_branch_alignment
    (predSat : PredSat) (mode : LeanPoison.EvalMode)
    (ctx : TypeContext) (μ₀ : Memory) (ρ₀ : VarEnv) (θ₀ : RealizationMap)
    (l₀ : Address) (pm₀ : Bool)
    (hric : runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀)   -- ADDED: used to discharge match_iff premise (iii)
    (hpred : PredSatLaws predSat)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config) :
    matchGuard cond ctx.memEnv ctx.varEnv = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    terminatesTo mode cond
      { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
      cfg' (Value.bool b') →
    b' = b := by
  -- proof outline:
  -- 1. get owner witness (var-owner OR ref-owner) from matchGuard success via bridge lemmas
  -- 2. apply hpred.match_iff with that witness
  -- 3. use hcwr (varsRegime.withPred_ok OR locsRegime.withPred_ok) to force predSat truth value
  -- 4. conclude b' = b
  sorry
```

Soundness checkpoint (recommended before full `ite` proof is finished):
- Even if `preservation_ite` remains `sorry`, prove these three lemmas to validate the approach:
  - `matchGuard_ok_owner_in_ctx`
  - `owner_in_ctx_to_runtime`
  - `guard_branch_alignment`
- Rationale: these lemmas are the core branch-alignment argument; if they are provable, the proposed direction is semantically credible.

Revised `preservation_valueW` sketch (critical for FR call sites):
```lean
theorem preservation_valueW (mode : LeanPoison.EvalMode) (e : Expr) (ctx : TypeContext) :
  ∀ (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (a₀ a₁ : Address) (pm₀ pm₁ : Bool) (v : Value) (w₀ w₁ : Void IO.RealWorld)
    (predSat : PredSat),                                              -- ADDED
    wfTypeContext ctx →
    typecheck ctx e fuel_tc = .ok res →
    wfRealizationMap θ₀ →
    wfRealizationMap θ₁ →
    wfExtendsMap θ₀ θ₁ →
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    PredSatLaws predSat →                                             -- ADDED
    consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀ →           -- ADDED
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ θ₁ →
    wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ } →
    terminatesToW mode w₀ w₁ e
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } v →
    valueHasETyp θ₁ v res.qualType.etyp ∧ wfTypeResult res
```
- FR call sites already carry `PredSatLaws` and `consistentWithRegime`; threading them through should be mostly mechanical.

## 4) How this fixes #112 (tied to sketch)
In the #112 witness:
- `matchGuard (var "x") ... = .ok (0, deps)`
- `ctx.regime.lookup? 0 = some true`
- runtime condition evaluates to `Value.bool false`

With the modified `Preservation` assumptions:
- `PredSatLaws predSat` and
- `consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀`
- `runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀` (already present; used for `match_iff` premise (iii))

the (optional) helper `guard_branch_alignment` proves runtime condition result must equal regime decision (`b' = b`). The same reasoning can also be inlined directly in the `if` proof case. Therefore the above triple is inconsistent, so the counterexample no longer satisfies theorem premises.

In the `if` proof case:
- typing commits using `ctx.regime.lookup? k = some b`,
- runtime yields `Value.bool b'`,
- `guard_branch_alignment` gives `b' = b`,
- runtime and typing pick the same branch.

## 5) Proof impact (active/partially-proven only)
This section lists proof surfaces that are currently active (proved or partially proved) and would need adjustment.

Main affected code:
- `LeanProofs/RegimeConsistency.lean` (new)
  - extracted shared definitions listed above.
- `LeanProofs/Preservation.lean`
  - update `Preservation` definition to add reused FR premises (`PredSatLaws`, `consistentWithRegime`).
  - import `LeanProofs.RegimeConsistency` (not `FaultRobustness`).
- `LeanProofs/FaultRobustness.lean`
  - remove moved shared definitions and import `LeanProofs.RegimeConsistency`.
- `LeanProofs/FaultRobustnessProofs.lean`
  - update `preservation_valueW` call sites (currently around line ~4830) to pass new assumptions (`predSat`, `PredSatLaws`, `consistentWithRegime`).
  - in `ite` mode proofs (notably mode1/mode2 region around ~6168), use branch-alignment reasoning derived from `match_iff` + `consistentWithRegime`, with explicit var-owner/ref-owner handling.

Expected effort profile:
- Signature churn is mechanical.
- Real semantic work is concentrated in `ite` StepFR branches, deriving branch alignment from `match_iff` + `consistentWithRegime`.
