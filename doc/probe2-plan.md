# Probe 2 Plan: Boundary Contract Payload Validation

## Status

Probe 1 baseline is clean. The six `StepFRApp.lean` `closure_extern` / `peClosure_extern` arms that Probe 1 introduced were already discharged by local-hypothesis vacuity (see "Probe 1 cleanup history" below). `StepFRApp.lean` now has zero `sorry`, the build is green, and `make test` passes 95/95.

**The current Probe 2 goal is no longer "discharge the six sorries"** — that is done. The goal is to **validate the boundary-contract payload shape** so that when registries actually populate (Probes 4–5), the existing arrow vacuity discharges can be cleanly replaced with real contract invocations *without* discovering a payload-fit problem mid-refactor. The first single-run arrow slice validated the operational payload; the follow-up slice validated the static `FnTClosure.extern … ∈ tcls` membership payload; the two-run slices validated that both arrow branches can supply the same strengthened payload to FR-shaped contracts. The provider slices validate that static membership can act as the local lookup key for obtaining a contract on both sides.

The arrow vacuity discharges (lines ~2342, ~3636, ~3641 in current `StepFRApp.lean`) are **specific to the current empty-registry theorem** and must be replaced in a future populated-registry theorem. The parrow vacuity arguments stay sound regardless (they rely on `Expr.toPExpr?` returning `none` for `externPfn`, a property of the language definition), so only the three arrow sites carry future replacement work under populated registries.

The follow-up registry-shape slice is also complete. `StepFRPost` is now a shared definition in `LeanProofs/StepFR.lean`, `StepFR` itself concludes that shared post, `LeanProofs/ExternBoundary.lean` defines the first shared boundary/registry scaffolding, and `StepFRApp.lean` now obtains its side-0 and side-1 providers through a local `TrustedRegistryAgreesWithProgramLocal` wrapper rather than constructing the two providers independently.

The next push added two populated-registry prerequisites but did not complete the populated-registry theorem. `LeanProofs/SemanticsProperties.lean` now exposes a full `terminatesTo_app_inv_full` / `TerminatesToAppSuccess` inversion with real `externFn` / `externPfn` dispatch branches. `LeanProofs/FaultRobustness.lean` now has `FaultRobustnessSpecWithRegistry` and `TypeSystemEnforcesFaultRobustness_spec_with_registry`; `LeanProofs/FaultRobustnessProofs.lean` proves the empty-registry compatibility theorem `TypeSystemEnforcesFaultRobustness_emptyRegistry`.

## Latest Provider Slice Scope

1. **Keep the current clean baseline.** No new `sorry`, no new `axiom`, no top-level theorem changes.
2. **Do not introduce `TrustedRegistry`** in this step.
3. **Add provider-shaped adapters for both sides,** `ExternCallBoundaryFRFnSide0Provider` and `ExternCallBoundaryFRFnSide1Provider`, parameterized by the arrow closure list `tcls`.
4. **Use static membership as the provider key:** `FnTClosure.extern id x retSpec eff tenv ∈ tcls → ExternCallBoundaryFRFnSide{0,1}Contract ...`.
5. **Keep the providers local and vacuous.** The `of_emptyExternRegistry` providers ignore the key and return the corresponding empty-registry contracts.
6. **At each branch, obtain the contract via `extProvider₀ htcl₀` / `extProvider₁ htcl₁`** before invoking the existing contract payload.
7. **Stop after both provider shapes build.**

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

### Two-run side-0/side-1 spike outcome

**Status:** ✅ Complete. `stepFR_app`'s side-0 `closure_extern` arm now invokes `ExternCallBoundaryFRFnSide0Contract`; side 1 now invokes `ExternCallBoundaryFRFnSide1Contract`. Each contract takes the ambient two-run `StepFR` inputs plus that side's extern dispatch payload and returns `StepFRPost` for the surrounding application. The branches supply `tcls`, per-side `tenv`, runtime `env`, `htcl`, and the per-side operational chain directly from local hypotheses. The default discharges ignore the static payload and close by the same `terminatesTo_preserves_registry` contradiction as the old inline proofs.

Two small engineering notes:

- The contract cannot use `StepFR ctxᵢ (Expr.app e1 e2) res predSat tm` as a function applied to the already-introduced premises; Lean treats that term as `Prop` without unfolding the definition at that application site. The spike first used a private local abbreviation for the already-applied post; that abbreviation has since been promoted to shared `StepFRPost`.
- Each branch uses `change StepFRPost ...` before `exact extCallSpec₀ ...` / `exact extCallSpec₁ ...` so the contract result lines up with the existing existential goal without changing the public theorem statement.

### Provider spike outcome

**Status:** ✅ Complete. `ExternCallBoundaryFRFnSide0Provider` and `ExternCallBoundaryFRFnSide1Provider` now model the future registry lookup shape locally: given a static member `FnTClosure.extern id x retSpec eff tenv ∈ tcls`, each returns the corresponding FR contract. The empty-registry providers ignore the key and return the vacuous contracts, but both branches now obtain their contracts through `extProvider₀ htcl₀` / `extProvider₁ htcl₁` instead of using the empty-registry contracts directly.

The key design result is small but important: `htcl₀` and `htcl₁` have exactly the shape needed to drive a future registry/boundary lookup. No additional typing-context facts had to be threaded to either branch.

### Local registry-agreement adapter outcome

**Status:** ✅ Complete. `StepFRApp.lean` now packages the two side providers behind `TrustedRegistryAgreesWithProgramLocal`. The empty-registry instance returns both vacuous providers, and `stepFR_app` projects `extProvider₀` / `extProvider₁` from that local agreement wrapper. This validates the next lookup-shaped layer without introducing a real `TrustedRegistry` into the theorem signatures.

### Shared post and boundary scaffolding outcome

**Status:** ✅ Complete for the additive scaffolding slice.

- `StepFRPost` was promoted from the app-local `StepFRAppliedPost` abbreviation into `LeanProofs/StepFR.lean`.
- `StepFR` now concludes `StepFRPost` directly; existing proofs continue to compile by definitional equality.
- The two FR extern-call contracts in `StepFRApp.lean` now return `StepFRPost` instead of the private app-local post.
- `LeanProofs/ExternBoundary.lean` now defines the shared names needed by the next registry slice: declaration/call boundary event shapes, `BodyEntryInputsAgree`, FR/single/WF boundary contracts, `ExternBoundarySpec`, `TrustedExternEntry`, `TrustedRegistry`, `TrustedRegistry.toRuntimeRegistry`, `ExternDeclarationInProgram`, and `TrustedRegistryAgreesWithProgram`.

One deliberate limitation remains: the current `StepFRPost` is still indexed by the source/post expression because it preserves the existing `IsCanonicalExtension`-based post exactly. The shared boundary contracts therefore take an explicit `postExpr`. Removing that expression dependency requires the deeper `BoundaryTagMeaningPost` refactor described in `doc/ffi-axioms.md`; it is not needed for the current payload-shape validation.

### Registry-aware semantic/spec prerequisite outcome

**Status:** ✅ Complete for prerequisites; ⛔ populated-registry theorem not complete.

- `TerminatesToAppSuccess` and `terminatesTo_app_inv_full` expose all four successful app paths: user fn, impure extern fn, user pfn, and pure extern pfn.
- `ExternDeclarationInReturn` makes nested extern return ids visible to `ExternDeclarationInProgram`, so trusted registry agreement can talk about returned callables.
- `TrustedRegistryAgreesWithFnTClosures` / `TrustedRegistryAgreesWithPFnTClosures` state the missing bridge from static closure-list membership to trusted entries.
- `FaultRobustnessSpecWithRegistry` is the runtime-registry-relative top-level property.
- `TypeSystemEnforcesFaultRobustness_emptyRegistry` proves the current theorem is an instance of the registry-relative spec at `emptyExternRegistry`.

The remaining populated-registry theorem cannot be obtained by only replacing the three old arrow vacuity discharges. The current `StepFR`, `StepFR_IH`, and `StepFRSingleRunFinalCleanPcTrue*_IH` families are still specialized to initial configs whose registry field is the `Config.mk` default. A genuine populated-registry proof must first strengthen that whole IH spine so every recursive premise starts from `{ ..., registry := runtimeRegistry }`. Until that is done, `StepFRApp` cannot use `terminatesTo_app_inv_full` in place of `terminatesTo_app_inv'` because the e2/e1 IH calls would still be about empty-registry runs.

Unattended completion attempt result: the additive prerequisites above are implemented and verified, but the populated-registry theorem is a real theorem-shape refactor, not a local Probe 2 cleanup. Pushing it further without a registry-parametric `StepFR` spine immediately runs into false premises in the extern declaration cases: `externVal`, `externFn`, and `externPfn` are currently discharged because the runtime registry is definitionally empty, but those branches can terminate under a populated registry and must consume declaration-level boundary evidence. Adding that evidence requires changing the public step theorem hypotheses and every recursive IH consumer together. No temporary `sorry` or axiom was introduced for this.

### What this tells us about the next step

**The single-run arrow consumption point is validated.** The contract type fits one proof site cleanly, including static closure-list membership; all parameters are supplied from local hypotheses already in scope.

**Several risks remain unvalidated and should be treated as future work, not as mechanical follow-on:**

- **Two-run payload fit.** Both sides of `stepFR_app`'s arrow case now fit FR-shaped contracts with static membership. A future non-vacuous registry contract may still need more cross-side evidence than this empty-registry slice exercises.
- **Registry agreement from static membership.** Both sides now use static membership as provider keys, and the shared scaffolding names `TrustedRegistryAgreesWithFnTClosures` / `TrustedRegistryAgreesWithPFnTClosures`; the proof still needs a typechecking lemma that turns app closure-list membership into one of those registry-closure agreement premises.
- **`TrustedRegistry` lookup mechanism.** Replacing `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` with a per-id registry lookup that delegates to `ExternBoundarySpec.callSingle` is unvalidated. The lookup needs to thread the extern id from the consumption site to the registry key; any mismatch in how `id` is exposed (through the closure-list, through the closure body, through `runtimeInstantiatesCtx`) will surface here.
- **Top-level theorem threading.** The runtime-registry-relative spec exists, but the proof theorem is still only established for `emptyExternRegistry`. A populated-registry theorem requires registry-parametric `StepFR` and single-run IHs across every per-operator proof module.

Generalization order (post-scaffolding, when ready):
1. Strengthen `StepFR`, `StepFR_IH`, `StepFRSingleRunFinalCleanPcTrue`, and masked single-run IHs with an explicit runtime registry parameter.
2. Mechanically update every per-operator `StepFR*` proof so recursive calls preserve the same registry. Non-extern operators should remain behavior-preserving; places using `config_eq_of_registry_default` need registry-parametric replacements.
3. Switch `StepFRApp` from `terminatesTo_app_inv'` to `terminatesTo_app_inv_full`.
4. Replace the top-level `externVal` / `externFn` / `externPfn` vacuity cases with declaration-boundary invocations from `ExternBoundarySpec.declFR`, `declSingle`, and `wf`.
5. Connect `TrustedRegistryAgreesWithProgram` plus closure-list agreement to the local provider wrapper by proving a bridge from `FnTClosure.extern … ∈ tcls` to a trusted entry and then to the side contract.
6. **Skip parrow user-closure vacuity only.** Runtime `externPfn` dispatch is exposed by the full app inversion, but `peClosure_extern` under the user-pfn branch still remains impossible by `Expr.toPExpr?`.
7. Replace `ExternCallBoundarySingleFnContract.of_emptyExternRegistry` and the two FR empty-registry provider projections with registry-keyed lookup that delegates to a per-id `ExternBoundarySpec`.
8. Prove the populated theorem for `TrustedRegistry.toRuntimeRegistry tr`; keep `TypeSystemEnforcesFaultRobustness_emptyRegistry` as the compatibility corollary.

The completed slices validated the single-run arrow site's operational/static payload, both two-run arrow-side payloads, static-membership-as-provider-key shape on both sides, the local agreement-wrapper shape, shared `StepFRPost` factoring, and the additive public boundary scaffolding. They do not yet validate non-vacuous cross-run boundary evidence or runtime registry plumbing.

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

1. ✅ Factor `StepFRPost` out of the existing `StepFR` conclusion shape.
2. ✅ Define the first shared `ExternCallEntry`, `ExternCallBoundaryRun`, `ExternCallBoundarySingle`, and `ExternCallBoundaryFR` scaffolding.
3. ✅ Define the first shared `TrustedRegistry`, `TrustedExternEntry`, `ExternBoundarySpec`, and `TrustedRegistryAgreesWithProgram` scaffolding.
4. ✅ Add the runtime-registry-relative top-level spec and empty-registry compatibility theorem.
5. Blocked on a broad theorem-shape refactor: add registry-parametric `StepFR` / single-run IHs and update every per-operator proof to preserve the runtime registry.
6. Replace extern declaration vacuity and the three arrow app vacuity discharges with real boundary-contract invocations once registry is non-empty.
