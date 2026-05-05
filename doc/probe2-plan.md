# Probe 2 Plan: Boundary Contract Payload Validation

## Status

Probe 1 baseline is clean. The six `StepFRApp.lean` `closure_extern` / `peClosure_extern` arms that Probe 1 introduced were already discharged by local-hypothesis vacuity (see "Probe 1 cleanup history" below). `StepFRApp.lean` now has zero `sorry`, the build is green, and `make test` passes 95/95.

**The current Probe 2 goal is no longer "discharge the six sorries"** — that is done. The goal is to **validate the boundary-contract payload shape** so that when registries actually populate (Probes 4–5), the existing arrow vacuity discharges can be cleanly replaced with real contract invocations *without* discovering a payload-fit problem mid-refactor. The first single-run arrow slice validated the operational payload; the follow-up slice validated the static `FnTClosure.extern … ∈ tcls` membership payload; the third slice validated that the two-run side-0 arrow branch can supply the same strengthened payload to an FR-shaped contract.

The arrow vacuity discharges (lines ~2342, ~3636, ~3641 in current `StepFRApp.lean`) are **specific to the current empty-registry theorem** and must be replaced in a future populated-registry theorem. The parrow vacuity arguments stay sound regardless (they rely on `Expr.toPExpr?` returning `none` for `externPfn`, a property of the language definition), so only the three arrow sites carry future replacement work under populated registries.

## Latest Slice Scope

1. **Keep the current clean baseline.** No new `sorry`, no new `axiom`, no top-level theorem changes.
2. **Do not introduce `TrustedRegistry`** in this step.
3. **Add a two-run side-0 contract-shaped hypothesis** for `stepFR_app`'s arrow branch, named `ExternCallBoundaryFRFnSide0Contract`.
4. **Return the already-applied `StepFR` post** for the surrounding `Expr.app`. This is factored locally as `StepFRAppliedPost`; the slice does not introduce the global `StepFRPost` planned for later.
5. **Keep the strengthened extern payload:** `tcls`, `tenv₀`, runtime `env₀`, and `FnTClosure.extern id₀ x₀ retSpec₀ eff₀ tenv₀ ∈ tcls`.
6. **Use only side-0 operational evidence** (`e2`, `e1`, extern body, output-config equation) plus the ambient two-run inputs already in scope.
7. **Discharge the contract with the current empty-registry contradiction** and stop after the side-0 branch builds.

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

**Status:** ✅ Spike complete. Single arrow site refactored to consume a contract-shaped hypothesis named `ExternCallBoundarySingleFnContract`. Caller discharges the contract via `ExternCallBoundarySingleFnContract.of_emptyExternRegistry`, which uses the existing empty-registry vacuity argument. The follow-up static-membership slice also succeeded: the contract now takes `tcls`, `tenv`, and `FnTClosure.extern id x retSpec eff tenv ∈ tcls`; the consuming branch supplies the membership directly from `closure_extern htcl`. **No new `sorry`, no new `axiom`, no top-level theorem changes.** `lake build LeanProofs` clean. `make test` 95/95. `git diff --check` clean. `StepFRApp.lean` still has zero `sorry`.

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
    (eff : List Effect) (tcls : List FnTClosure) (tenv : CapturedVarEnv)
    (env : VarEnv),
    FnTClosure.extern id x retSpec eff tenv ∈ tcls →
    terminatesTo e2 { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm } c₂' v₂ →
    terminatesTo e1 c₂' c₁
      (Value.closure x (Expr.externFn id y argTyp retSpec eff) env) →
    terminatesTo (Expr.externFn id y argTyp retSpec eff)
      { c₁ with varEnv := VarEnv.update env x v₂, pureMode := false }
      evalCfg o →
    cf = { c₁ with memory := evalCfg.memory, nextAddr := evalCfg.nextAddr,
                   pureMode := c₁.pureMode } →
    ctxᵢ.pc = true →
    StepFRSingleRunFinalCleanPcTrueMaskedRegParamPost
      masked CtxCons ValCons ctxᵢ res μ ρ θ cf o
      hθwf hwf hric hreg hmasked_none hctxCons a pm hwfcfg
```

### What payload was needed (and fit cleanly)

The strengthened contract takes 33 parameters/hypotheses, organized into four blocks:

1. **Initial-state payload (14 params).** `μ ρ θ cf o` plus the seven well-formedness / runtime-instantiation / regime / masked-registry / wfConfig hypotheses, plus the `a pm` address-mode-pair. Every one of these is in scope at the discharge site by the time `cases hv₁_arrow` runs — they came from the lemma's outer signature.
2. **Runtime/static extern-call payload (13 params).** `c₂' v₂ c₁ evalCfg` from `terminatesTo_app_inv'`; `id x y argTyp retSpec eff env` from the runtime closure/body; and `tcls tenv` from the typing-side closure-list evidence. The runtime `env : VarEnv` and static `tenv : CapturedVarEnv` are intentionally distinct.
3. **Static membership evidence (1 hypothesis).** `FnTClosure.extern id x retSpec eff tenv ∈ tcls`, supplied directly by the `htcl` field of `valueHasETyp.closure_extern`.
4. **Operational predicates (5 hypotheses).** Three `terminatesTo` chain links (`e2`, `e1`, body), the output-config equation `cf = { c₁ with … }`, and `ctxᵢ.pc = true`. All five are direct destructure outputs of `terminatesTo_app_inv'` plus the surrounding lemma's `hpc` premise.

**Everything the strengthened contract needs comes from local hypotheses at the discharge site.** No global premise-widening, no fabricated facts, no need to thread `TrustedRegistry` or any other infrastructure into the lemma signature. The payload-fit question — "does the future contract shape match what the proof site can supply?" — answers cleanly for this single-run arrow site: **yes**.

### Default discharge under empty registry

Bundled as `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` (next to the contract definition). It introduces all contract parameters, ignores the static `tcls` / `tenv` / membership payload, then derives False from the chain `cinit (default Config.mk → emptyExternRegistry) → c₂' (terminatesTo_preserves_registry) → c₁ → body's call config → terminatesTo on Expr.externFn under empty registry fails (beval returns runtimeError)`. ~14 lines, mechanical.

The caller (`stepFRSingleRunFinalCleanPcTrue_app_maskedReg` in `StepFRApp.lean`) passes `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` directly into the parametric lemma's `extCallSpec` argument. No top-level theorem signature changed; no `TrustedRegistry` introduced.

### What did not fit cleanly (and was redesigned mid-spike)

- **Original try: `let cinit := …` inside the contract definition.** Lean's `intro` tactic doesn't pass through `let` bindings transparently in this context, causing an off-by-one mismatch where the implication intros got assigned to the inner-forall binders. Fixed by inlining `cinit` as `{ memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }` directly in the `terminatesTo e2 …` premise.
- **Original try: `simpa using terminatesTo_preserves_registry ht_e2`.** Failed because the inlined config doesn't have a `cinit` simp lemma. Fixed by directly using the result `c₂'.registry = (config-mk).registry = emptyExternRegistry` — the equality holds by `Config.mk` default-registry definitional equality, no `simp` needed.

Neither redesign required widening the contract or adding global premises.

### Two-run side-0 spike outcome

**Status:** ✅ Complete. `stepFR_app`'s side-0 `closure_extern` arm now invokes `ExternCallBoundaryFRFnSide0Contract`. The contract takes the ambient two-run `StepFR` inputs plus the side-0 extern dispatch payload and returns `StepFRAppliedPost` for the surrounding application. The branch supplies `tcls`, `tenv₀`, runtime `env₀`, `htcl₀`, and the side-0 operational chain directly from local hypotheses. The default discharge `ExternCallBoundaryFRFnSide0Contract.of_emptyExternRegistry` ignores the static payload and closes by the same `terminatesTo_preserves_registry` contradiction as the old inline proof.

Two small engineering notes:

- The contract cannot use `StepFR ctxᵢ (Expr.app e1 e2) res predSat tm` as a function applied to the already-introduced premises; Lean treats that term as `Prop` without unfolding the definition at that application site. The spike uses a private local abbreviation `StepFRAppliedPost` that spells out the already-applied `StepFR` post.
- The branch uses `change StepFRAppliedPost ...` before `exact extCallSpec₀ ...` so the contract result lines up with the existing existential goal without changing the public theorem statement.

### What this tells us about the next step

**The single-run arrow consumption point is validated.** The contract type fits one proof site cleanly, including static closure-list membership; all parameters are supplied from local hypotheses already in scope.

**Several risks remain unvalidated and should be treated as future work, not as mechanical follow-on:**

- **Two-run payload fit.** Side 0 of `stepFR_app`'s arrow case now fits an FR-shaped contract with static membership. Side 1 remains unvalidated. A future non-vacuous registry contract may also need more cross-side evidence than this empty-registry slice exercises.
- **Registry agreement from static membership.** The single-run site now supplies `FnTClosure.extern id x retSpec eff tenv ∈ tcls`, but no `TrustedRegistryAgreesWithProgram` relation exists yet to turn that static membership into a registry lookup and boundary-spec witness.
- **`TrustedRegistry` lookup mechanism.** Replacing `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` with a per-id registry lookup that delegates to `ExternBoundarySpec.callSingle` is unvalidated. The lookup needs to thread the extern id from the consumption site to the registry key; any mismatch in how `id` is exposed (through the closure-list, through the closure body, through `runtimeInstantiatesCtx`) will surface here.
- **Top-level theorem threading.** Adding `TrustedRegistry` and `TrustedRegistryAgreesWithProgram` to `FaultRobustnessSpec` and propagating both to every consumer of the registry-relative theorem changes a public API surface. None of that has been validated.

Generalization order (post-spike, when ready):
1. Mirror the strengthened two-run contract for side 1 of `stepFR_app`'s arrow case. If it fits, consider unifying the side-0 and side-1 contracts or leaving them separate until the registry layer is introduced.
2. **Skip parrow sites.** Their `Expr.toPExpr?` vacuity stays sound under populated registries, so they don't need contracts.
3. Build the `TrustedRegistry` layer: replace `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` with a registry-keyed lookup that delegates to a per-id `ExternBoundarySpec`.
4. Thread `TrustedRegistry` through `FaultRobustnessSpec`. Top-level theorem becomes registry-relative.

The completed slices validated the single-run arrow site's operational/static payload and the two-run side-0 payload. They do not validate side 1, non-vacuous cross-run boundary evidence, or registry plumbing.

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
