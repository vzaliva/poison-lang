# Probe 2 Plan: Boundary Contract Payload Validation

## Status

Probe 1 baseline is clean. The six `StepFRApp.lean` `closure_extern` / `peClosure_extern` arms that Probe 1 introduced were already discharged by local-hypothesis vacuity (see "Probe 1 cleanup history" below). `StepFRApp.lean` now has zero `sorry`, the build is green, and `make test` passes 95/95.

**The current Probe 2 goal is no longer "discharge the six sorries"** — that is done. The goal is to **validate the boundary-contract payload shape** so that when registries actually populate (Probes 4–5), the existing arrow vacuity discharges can be cleanly replaced with real contract invocations *without* discovering a payload-fit problem mid-refactor.

The arrow vacuity discharges (lines ~2342, ~3636, ~3641 in current `StepFRApp.lean`) are **specific to the current empty-registry theorem** and must be replaced in a future populated-registry theorem. The parrow vacuity arguments stay sound regardless (they rely on `Expr.toPExpr?` returning `none` for `externPfn`, a property of the language definition), so only the three arrow sites carry future replacement work under populated registries.

## Scope of This Step

1. **Keep the current clean baseline.** No new `sorry`, no new `axiom`, no top-level theorem changes.
2. **Boundary/registry infrastructure is future work** unless this spike proves the contract shape fits at the consumption point.
3. **Do not introduce `TrustedRegistry`** in this step.
4. **Introduce only a local contract-shaped hypothesis** at one arrow site, named close to the future API (e.g. `ExternCallBoundarySingleFnContract`).
5. **Shape the hypothesis like the future `ExternCallBoundarySingle.fn`**: it takes the local extern call payload available at the proof site and returns exactly the single-run postcondition this branch needs.
6. **Replace the inline vacuity proof at that one arrow site** with an invocation of this contract-shaped hypothesis.
7. **Discharge the contract hypothesis at the caller** using the existing empty-registry vacuity, not by adding registry plumbing.
8. **Stop after one site builds.**

## Spike Target

`stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg` in `LeanProofs/StepFRApp.lean`, the `closure_extern _ _ _` arm (current line ~2342). Single-run masked-reg arrow:

- Single-run is structurally simpler than two-run (no cross-side closure-list synchronization, no `agreeCapturedEnv`).
- Arrow is the harder shape that needs contracts post-Probe-2 (parrow stays sound under populated registry via `Expr.toPExpr?` vacuity). Validating arrow first means parrow is mechanical when needed.
- The site already has a working vacuity discharge to compare against, so the contract version's correctness can be cross-checked.

## Acceptance Criteria

- `lake build LeanProofs` succeeds.
- `make test` still passes 95/95.
- `git diff --check` clean.
- `StepFRApp.lean` still has zero `sorry`.
- No new `sorry` or `axiom` anywhere.
- This file records what payload the contract needed, what fit cleanly, and what did not.

## Hard Stops

- **If the contract needs facts not available locally** at the target site, stop and report. Do not widen the contract with vague global premises just to make the spike compile.
- **If satisfying the hypothesis at callers requires changing top-level theorem statements**, stop.

## Spike Outcome (post-execution)

**Status:** ✅ Spike complete. Single arrow site refactored to consume a contract-shaped hypothesis named `ExternCallBoundarySingleFnContract`. Caller discharges the contract via `ExternCallBoundarySingleFnContract.of_emptyExternRegistry`, which uses the existing empty-registry vacuity argument. **No new `sorry`, no new `axiom`, no top-level theorem changes.** `lake build LeanProofs` clean. `make test` 95/95. `git diff --check` clean. `StepFRApp.lean` still has zero `sorry`.

### Contract shape that fit cleanly

```lean
private def ExternCallBoundarySingleFnContract
    (masked : Tag → Prop)
    (CtxCons : TypeContext → Memory → VarEnv → RealizationMap → Prop)
    (ValCons : Regime → QTyp → Memory → RealizationMap → Value → Prop)
    (ctxᵢ : TypeContext) (res : TypeResult)
    (e1 e2 : Expr) : Prop :=
  ∀ -- Initial-state payload (matches the StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost interface)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value)
    (hθwf : wfRealizationMap θ) (hwf : wfTypeContext ctxᵢ)
    (hric : runtimeInstantiatesCtx ctxᵢ μ ρ θ)
    (hreg : regimeConsistentWithCtxMasked masked ctxᵢ)
    (hmasked_none : ∀ k, masked k → ctxᵢ.regime.lookup? k = none)
    (hctxCons : CtxCons ctxᵢ μ ρ θ)
    (a : Address) (pm : Bool)
    (hwfcfg : wfConfig { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm })
    -- Operational extern-call payload from the proof site
    (c₂' : Config) (v₂ : Value) (c₁ : Config) (evalCfg : Config)
    (id : ExternId) (x y : Name) (argTyp : Typ) (retSpec : ExternReturn)
    (eff : List Effect) (capturedEnv : VarEnv),
    terminatesTo e2 { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.closure x (Expr.externFn id y argTyp retSpec eff) capturedEnv) →
    terminatesTo (Expr.externFn id y argTyp retSpec eff)
      { c₁ with varEnv := VarEnv.update capturedEnv x v₂, pureMode := false }
      evalCfg o →
    cf = { c₁ with memory := evalCfg.memory, nextAddr := evalCfg.nextAddr,
                   pureMode := c₁.pureMode } →
    ctxᵢ.pc = true →
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked CtxCons ValCons ctxᵢ res μ ρ θ cf o
      hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
```

### What payload was needed (and fit cleanly)

The contract takes 30 parameters, organized into three blocks:

1. **Initial-state payload (14 params).** `μ ρ θ cf o` plus the seven well-formedness / runtime-instantiation / regime / masked-registry / wfConfig hypotheses, plus the `a pm` address-mode-pair. Every one of these is in scope at the discharge site by the time `cases hv₁_arrow` runs — they came from the lemma's outer signature.
2. **Operational extern-call payload (11 params).** `c₂' v₂ c₁ evalCfg` from `terminatesTo_app_inv'` peClosure→closure case destructure; `id x y argTyp retSpec eff capturedEnv` from the `closure_extern` constructor's implicit unification with `body = Expr.externFn id y argTyp retSpec eff`. All 11 are in scope at the discharge site.
3. **Operational predicates (5 hypotheses).** Three `terminatesTo` chain links (`e2`, `e1`, body), the output-config equation `cf = { c₁ with … }`, and `ctxᵢ.pc = true`. All five are direct destructure outputs of `terminatesTo_app_inv'` plus the surrounding lemma's `hpc` premise.

**Everything the contract needs comes from local hypotheses at the discharge site.** No global premise-widening, no fabricated facts, no need to thread `TrustedRegistry` or any other infrastructure into the lemma signature. The payload-fit question — "does the future contract shape match what the proof site can supply?" — answers cleanly: **yes**.

### Default discharge under empty registry

Bundled as `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` (next to the contract definition). It introduces all 30 contract parameters, then derives False from the chain `cinit (default Config.mk → emptyExternRegistry) → c₂' (terminatesTo_preserves_registry) → c₁ → body's call config → terminatesTo on Expr.externFn under empty registry fails (beval returns runtimeError)`. ~14 lines, mechanical.

The caller (`stepFRSingleRunFinalCleanPcTrue_app_maskedReg` in `StepFRApp.lean`) passes `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` directly into the parametric lemma's `extCallSpec` argument. No top-level theorem signature changed; no `TrustedRegistry` introduced.

### What did not fit cleanly (and was redesigned mid-spike)

- **Original try: `let cinit := …` inside the contract definition.** Lean's `intro` tactic doesn't pass through `let` bindings transparently in this context, causing an off-by-one mismatch where the implication intros got assigned to the inner-forall binders. Fixed by inlining `cinit` as `{ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }` directly in the `terminatesTo e2 …` premise.
- **Original try: `simpa using terminatesTo_preserves_registry ht_e2`.** Failed because the inlined config doesn't have a `cinit` simp lemma. Fixed by directly using the result `c₂'.registry = (config-mk).registry = emptyExternRegistry` — the equality holds by `Config.mk` default-registry definitional equality, no `simp` needed.

Neither redesign required widening the contract or adding global premises.

### What this tells us about the next step

**The single-run arrow consumption point is validated.** The contract type fits one proof site cleanly, with all 30 parameters supplied from local hypotheses already in scope.

**Several risks remain unvalidated and should be treated as future work, not as mechanical follow-on:**

- **Two-run payload fit.** `stepFR_app`'s arrow case (lines ~3636, ~3641 post-cleanup) involves *two* `terminatesTo_app_inv'` destructures with cross-side closure-list synchronization (`agreeCapturedEnv`-flavored constraints). The single-run spike says nothing about whether a two-run boundary contract's payload aligns with what the cross-side proof needs, particularly for shared closure-list membership and synchronized argument-value evidence.
- **Static `FnTClosure.extern … ∈ tcls` / captured-env evidence.** The current spike contract takes the operational `terminatesTo` chain but does **not** require static evidence that the dispatched extern actually appears as a `FnTClosure.extern id x retSpec eff capturedEnv` member of the closure-list `tcls` from the typing context. A future registry-keyed contract will likely need this membership fact to discharge the registry lookup correctly (the registry maps `id` → impl, but the proof needs to relate the runtime `id` back to a typing-side `tcls` member). The next slice should validate this explicitly — extend the contract with the membership premise, see whether it can be supplied at the discharge site, and check whether the empty-registry default discharge can still be provided without it.
- **`TrustedRegistry` lookup mechanism.** Replacing `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` with a per-id registry lookup that delegates to `ExternBoundarySpec.callSingle` is unvalidated. The lookup needs to thread the extern id from the consumption site to the registry key; any mismatch in how `id` is exposed (through the closure-list, through the closure body, through `runtimeInstantiatesCtx`) will surface here.
- **Top-level theorem threading.** Adding `TrustedRegistry` and `TrustedRegistryAgreesWithProgram` to `FaultRobustnessSpec` and propagating both to every consumer of the registry-relative theorem changes a public API surface. None of that has been validated.

Generalization order (post-spike, when ready):
1. Add the static `FnTClosure.extern … ∈ tcls` membership premise to `ExternCallBoundarySingleFnContract` and reverify that the discharge site can supply it (from `htcl` on the `closure_extern` constructor) and that the empty-registry default discharge still works. **Validate this before generalizing further.**
2. Mirror the (extended) contract for the other two arrow sites (`stepFR_app` arrow case, sides 0 and 1). Surface and address two-run payload-fit issues.
3. **Skip parrow sites.** Their `Expr.toPExpr?` vacuity stays sound under populated registries, so they don't need contracts.
4. Build the `TrustedRegistry` layer: replace `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` with a registry-keyed lookup that delegates to a per-id `ExternBoundarySpec`.
5. Thread `TrustedRegistry` through `FaultRobustnessSpec`. Top-level theorem becomes registry-relative.

But none of that is in scope for this spike. The spike's only job was to validate one single-run arrow site's contract-shape fit at the consumption point, and that's done.

---

## Probe 1 Cleanup History (Reference)

Probe 1 added `valueHasETyp.{closure,peClosure}_extern` constructors. Lean's exhaustivity check then forced six new `closure_extern` / `peClosure_extern` arms in `LeanProofs/StepFRApp.lean` — initially stubbed with `sorry`. All six closed via local-hypothesis vacuity, **not** boundary contracts.

| Site (original line) | Lemma | Closure kind | Vacuity argument |
|---|---|---|---|
| 2342 | `stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg` | `closure_extern` | empty-registry → `beval` on `Expr.externFn` fails |
| 2976 | `stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric_maskedReg` | `peClosure_extern` | `Expr.toPExpr? body ≠ none` becomes `none ≠ none` |
| 3622 | `stepFR_app` (arrow case, side 0) | `closure_extern` | empty-registry chain via `terminatesTo_preserves_registry` |
| 3627 | `stepFR_app` (arrow case, side 1) | `closure_extern` | empty-registry chain via `terminatesTo_preserves_registry` |
| 6299 | `stepFR_app` (parrow case, side 0) | `peClosure_extern` | `Expr.toPExpr?` mismatch via `htoP₀` |
| 6304 | `stepFR_app` (parrow case, side 1) | `peClosure_extern` | `Expr.toPExpr?` mismatch via `htoP₁` |

**Parrow vacuity (3 sites, ~1 line each).** `peClosure_extern` constructor unifies `body = Expr.externPfn id y argTyp retSpec`. `terminatesTo_app_inv'`'s peClosure case carries `Expr.toPExpr? body ≠ none`. `Expr.toPExpr?` returns `none` for `externPfn` (default `_ => none` fallthrough at `LeanPoison/Syntax.lean:446`). So the precondition is contradictory.

**Arrow vacuity (3 sites, ~9–14 lines each).** `closure_extern` constructor unifies `body = Expr.externFn id y argTyp retSpec eff`. `cinit.registry = emptyExternRegistry` by default `Config.mk`. `terminatesTo_preserves_registry` propagates this through `e2` and `e1` to `c₁.registry`. Then `terminatesTo body { c₁ with … }` for `body = Expr.externFn …` requires `beval` to succeed under empty registry — but the runtime returns `runtimeError` when `config.registry.get? id = none` (`LeanPoison/BigStep.lean:204`). Contradiction.

## Future Probe 2 Scope (After Payload Validation)

Once the contract shape is validated, the remaining work matches `doc/ffi-axioms.md`:

1. Factor `StepFRPost` out of the existing `StepFR` conclusion shape.
2. Define `ExternCallEntry`, `ExternCallBoundaryRun.{fn,pfn}`, `ExternCallBoundarySingle.{fn,pfn}`, `ExternCallBoundaryFR.{fn,pfn}`.
3. Define `TrustedRegistry`, `TrustedExternEntry`, `ExternBoundarySpec`, `TrustedRegistryAgreesWithProgram`.
4. Thread `TrustedRegistry` through `FaultRobustnessSpec` so the top-level theorem becomes registry-relative.
5. Replace the three arrow vacuity discharges in `StepFRApp.lean` with real boundary-contract invocations once registry is non-empty.
