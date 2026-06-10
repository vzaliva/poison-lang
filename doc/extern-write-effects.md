# Extern Write-Effect Trust: Status and Remaining Work

## Status

`@22` (`set_err`), the impure write-effect extern
(`effects: { !errno :> (int :> clean {}) }`), is fully trusted:

- `ExternProofs.builtinSetErrSpec` is a complete five-field
  `ExternBoundarySpec` (`declFR`, `callFR`, `declSingle`, `callSingle`,
  `operational`) — the first trusted `.fn` (memory-writing) extern entry.
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `ExternRegimeInt.setErrWriteEffect_FR` is the program-level capstone:
  fault-robustness for the registry `[@22 set_err]` at the canonical empty
  context, stated for the bare `@22` declaration node.
  `ExternProofs.defaultRegistry_lookup_seterr` ties the interpreter's `@22`
  dispatch to the proven `setErrImpl`.
- The typechecker treats an extern write effect as an assignment to the
  resolved target reference: `applyExternEffect` performs the
  singleton-strong / non-singleton-weak heap update with the target
  reference's own poison folded into the stored type (the weak update
  degrades the joined predicate to `noPred` at untracked locset members);
  `.fn` extern returns invalidate guard-tag and regime dependencies on the
  written effect targets (`effectTargetLocs` / `invalidateTagDeps` /
  `invalidateRegimeDepsEffect`); and extern return guards are materialised
  value-correctly into the tagEnv at the call (`installReturnGuard`), gated
  on the final post-call regime, so an errno-reading return guard carries
  `deps ∋ errno` and a later `set_err` invalidates it. Regime-undetermined
  guards are not materialised.
- Behavioural coverage: `examples/extern_set_err_stale_guard.poison` (a
  stale errno-reading guard is invalidated; the later clean-argument gate
  rejects) and `examples/extern_set_err_unrelated_guard.poison` (an
  unrelated guard survives `set_err`). The Ott specification and
  `doc/poison-lang-description.tex` describe these semantics.

`@21` (`errno` as an extern `val` exposing `Value.loc errnoAddr`) is **not**
trusted and is in no `TrustedRegistry`. The representative combined scenario
remains:

```poison
let errno = extern val @21 : (ref int :> clean {}) in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

What already exists for `@21`: the reserved-address building blocks
`ReservedAddr`, `RegistryReservedBelow` (+ `_mono`,
`_emptyExternRegistry`), and the witness
`wfValue_loc_of_RegistryReservedBelow` are standalone definitions in
`Semantics.lean`; `defaultInitialState.nextAddr` starts above `errnoAddr`;
the `errno` cell is seeded in `defaultInitialState.memory`. `wfConfig` is
still registry-agnostic. The work below is what remains.

## Blocking finding: clean cell content makes `@21`'s declaration fields unprovable

The earlier assessment of `declFR` / `declSingle` ("plausibly doable —
novel work") was wrong. `extern val @21 : (ref int :> clean {})`
typechecks by allocating a fresh logical location `ℓ` and seeding the
cell-content memEnv entry **clean** (`surfaceSpecToQTyp`, ref case:
`ℓ ↦ ⟨ETyp.int, false, noPred⟩`). Against that typing the boundary
obligations fail for three independent reasons:

1. **Memory presence.** `valueHasETyp θ' (loc errnoAddr) (ref {ℓ})`
   forces `θ' ℓ = some errnoAddr`, and the first clause of
   `runtimeInstantiatesCtx` then demands `μ.contains errnoAddr`. The decl
   contracts quantify over an arbitrary `μ` constrained only by
   pre-context hypotheses that know nothing of `errnoAddr`; the
   `defaultInitialState` seeding never reaches the obligation
   (counterexample: empty memory).
2. **Relational agreement.** `StepFRPost.agreeOnClean` over `ctxAfter`
   covers the fresh clean entry at `ℓ`; with both runs realising
   `ℓ ↦ errnoAddr` it forces the two pre-memories to agree at
   `errnoAddr`. No premise supplies that — and none can: the errno cell
   is in no `InputSpec`, so two valid initial states may already disagree
   there. `!errno` typed clean before any trusted write is semantically
   **not** fault-robust; the statement is false, not merely hard.
3. **Flat contradiction in the single-run post.**
   `ExternBoundarySinglePost` requires both `valueHasETyp θ' …` (so
   `θ' ℓ = some errnoAddr`) and `FreshCleanLocsUnrealizedOneRun`, which
   for a fresh clean location demands `θ' ℓ = none`.

The fix has two parts, scheduled as steps 1 and 3 below:

- **Poison the seeded cell content** (dissolves 2 and 3): the memEnv
  entry for an extern-val ref becomes `⟨ETyp.int, true, noPred⟩`. The ref
  **value** keeps its declared qualifier (the location is stable and
  clean); the **content** is environment garbage until a trusted write
  effect re-establishes cleanness (e.g. `set_err`'s
  `!errno :> (int :> clean {})`, a singleton strong update). With the
  entry no longer `qtypCleanUnder`, the clean-location clauses of
  `agreeOnClean` and `FreshCleanLocsUnrealizedOneRun` are vacuous at `ℓ`.
- **Fold reserved-cell presence into `wfConfig`** (discharges 1): see
  step 3. Presence plus `wfConfig`'s memory bound also yields
  `RegistryReservedBelow`, so the planned `val` operational bridge rides
  on the same fold.

## Remaining work (ordered high-risk-first)

### 1. Typechecker: seed extern-val ref content poisoned

In `surfaceSpecToQTyp`'s ref case, change the fresh memEnv entry from
`⟨ETyp.int, false, Predicate.noPred⟩` to `⟨ETyp.int, true,
Predicate.noPred⟩`. Only extern-val declarations reach this function, so
nothing else moves; `beval` is untouched (the change is type-level only,
runtime values and outputs are unchanged). The proof-side dependents of
`surfaceSpecToQTyp` are shape lemmas (non-function ETyp, predicate
preservation, reachability) that do not read the poison bit.

Impact assessment:

- **Soundness**: restores it — the clean-content typing is FR-false
  (finding 2 above).
- **Precision**: reading a reserved cell before any trusted write is now
  poisoned; a later clean-effect write re-cleans it (singleton strong
  update). Programs feeding a pre-write `!errno` into a clean-gated
  position are rejected — which is the point.
- **Operational semantics**: none.
- **Sync**: Ott extern-val typing rule, `doc/poison-lang-description.tex`,
  and an audit of **every** ref-typed extern-val fixture — the converter
  is generic, not `@21`-specific. `grep -l 'extern val.*ref' examples/`
  currently lists 12 programs: among them `lp55xx-read.poison` (two
  extern refs; its `.fail` golden records both cells clean in the
  printed memEnv) and the `.fail` anchors `multiple-poison-sources`,
  `reference-poison2`, `assign-nonsingleton-weak`,
  `extern_effect_under_poisoned_{pc,function}`. Re-run `make test`;
  regenerate goldens where the diff is the intended verbose poison flip
  (`extern_errno.output`, `lp55xx-read.fail`, …) and flag any fixture
  whose accept/reject behaviour changes. `extern_set_err.*` goldens
  should be unchanged because the deref happens after the clean strong
  update.

### 2. Prototype `@21`'s decl fields standalone (de-risk before the fold)

`declFR` / `declSingle` remain the first-ever realisation of a bare
`Value.loc` — every existing trusted spec realises a closure. Before
paying the fold churn of step 3, prove the post bodies as standalone
lemmas with presence supplied as explicit hypotheses, stated **per
run**: for `declSingle`, `μ.contains errnoAddr` and `errnoAddr < a`;
for the two-run `declFR`, both `μ₀.contains errnoAddr` /
`μ₁.contains errnoAddr` and `errnoAddr < a₀` / `errnoAddr < a₁`:

- witness `θ' := θ.insert ℓ errnoAddr` (`ℓ` fresh, so `wfExtendsMap`
  holds);
- `valueHasETyp` via `valueHasETyp.loc`;
- `runtimeInstantiatesCtx` clause 1 from presence; clause 2 unchanged
  (varEnv and memory untouched by the externVal step);
- clean-location clauses vacuous at `ℓ` after step 1;
- result-value conjuncts close because both runs read the same registry
  value (`ExternDeclBoundaryFR` binds one `registry` for both runs).

If anything in `consistentWithRegime` / `valueConsistentWithRegime` for
ref-typed results resists, it surfaces here, before the expensive step.
The `ExternBoundarySpec` fields themselves can only be assembled after
step 3 (their `wfConfig` hypotheses must carry presence).

### 3. Fold presence into `wfConfig`; repair `val` bridge; assemble spec

Fold `∀ a, ReservedAddr cfg.registry a → cfg.memory.contains a` into
`wfConfig` as a new **last** conjunct (existing `.1` projections survive;
`.2` sites become `.2.1`). `RegistryReservedBelow cfg.registry
cfg.nextAddr` then **derives** from presence plus the memory bound — the
standalone defs and `wfValue_loc_of_RegistryReservedBelow` stay as the
bridge witness. Refresh the `Semantics.lean` comments that still describe
a below-only fold.

Preservation: the registry is immutable across evaluation and memory
containment is monotone (assign / newRef insert; nothing removes). Extern
`fn` dispatch is the one step where containment-monotonicity must come
from the contract: add a containment-preservation conjunct
(`∀ a, mem.contains a → mem'.contains a`) to the `fn` clauses of
`ExternOperationalSafe` / `RegistryOperationalSafe`, thread it through
`TrustedRegistry.operationalSafe` and `wfConfig_preserved`'s fn case, and
re-prove `builtinSetErrSpec.operational` (`setErrImpl` only inserts —
easy, but it is a signature change; the earlier "trivial,
`RegistryReservedBelow_mono` with `le_refl`" estimate was too small).

`val` clause repair: the per-entry clause becomes conditional on the
lookup —
`∀ v, impl = .val v → ∀ cfg id, wfConfig cfg → cfg.registry.get? id =
some (.val v) → wfValue cfg.nextAddr v` — discharged for `@21` by
presence + the memory bound. The registry-level bridge consumes
`cfg.registry = reg` (today discarded as `_hreg` in
`TrustedRegistry.operationalSafe`) to transport the lookup. Every site
that discharges `val` as impossible (the six `.pfn` operational lemmas
plus `pureUnaryCleanInt_operational`) is re-touched for the new
signature.

Initial state: `defaultRegistry` reserves exactly `errnoAddr`, which
`defaultInitialState.memory` seeds — prove the presence analogue of
`RegistryReservedBelow_emptyExternRegistry` for both registries.

Churn: the fold makes `wfConfig` read `cfg.registry`, breaking the FR
stack's defeq coercions across registry-differing configs — the
~100+-site estimate stands (mostly `StepFRApp`); add a transport helper
(`wfConfig` across registry-equal configs) so each site is a one-liner.
With steps 1–2 green this churn is exercised immediately by the
assembled `@21` spec.

Assemble `ExternProofs.builtinErrnoSpec`: decl fields from step 2 (with
presence now arriving via the strengthened `wfConfig` hypotheses),
`callFR` / `callSingle` vacuous by kind (`ExternCallBoundaryRun` has no
`val` constructor), `operational` via the repaired bridge.

### 4. Combined `@21`/`@22` scenario registry and documentation sweep

There is no single "default trusted registry": FR is proved per-scenario at
`TrustedRegistry.toRuntimeRegistry <subsetRegistry>`, and a
`TrustedRegistry` projecting to the *whole* `defaultRegistry` is impossible
(it would need a compiling entry for `@19` (sqrt), recorded infeasible
under the 0-sorry gate). So:

- Put `builtinErrnoSpec` and `builtinSetErrSpec` in a dedicated scenario
  `TrustedRegistry` with only `@21`/`@22`, and prove FR for a program
  reaching both via `TypeSystemEnforcesFaultRobustness_at` (its
  `TrustedRegistryAgreesWithReachable` premise requires only the externs
  the program *reaches*). End-to-end example tests already exist
  (`extern_set_err.poison`, `extern_errno.poison`).
- Add the per-id dispatch bridge `defaultRegistry_lookup_errno`
  (mirroring the existing `defaultRegistry_lookup_seterr` and friends).
- `doc/ffi-proposal.md` was brought current on 2026-06-10 (`@22` listed
  as trusted; the `@21` blocker rewritten to the decl-field findings).
  `doc/externs.md` is still stale for `@22` (its `@22` entry predates
  `builtinSetErrSpec`); fixing that wording is **not** gated on `@21`
  and should land with the next checkpoint. Both docs' `@21` entries get
  their final status update once all `@21` fields compile.

## Residual gaps (recorded, not scheduled)

- `installReturnGuard` materialises only the resolved **return** predicate
  of simple extern returns: a `guardOnly` return predicate, an effect-only
  guard tag, and nested-return effect guards are not materialised. The
  installer also skips a predicate whose `extractDepsFromPred` fails (such
  predicates already fail at any later `if` via `matchGuard`).
- `PredSatLaws.mem_monotone` as stated quantifies over an arbitrary `pred`,
  so instantiating it at `Predicate.noPred` yields unconditional
  memory-independence of `predSat`; the proof stack exploits exactly this
  (`predSat_mem_noPred_compat` /
  `qtypPredHolds_mem_compat_of_predSatLaws`, ~95 uses). Tightening the law
  to tie `pred` to the guard's canonical predicate — making
  memory-dependence real at the proof layer — is future work that the
  effect dependency-invalidation machinery now makes feasible.

## History

- 2026-06-10 — independent review: no technical blocker found in the
  reordered approach. Scope tightened: step 1's example audit broadened
  to all ref-typed extern-val fixtures (12, incl. `lp55xx-read` with two
  refs in its `.fail` golden); step 2's prototype hypotheses spelled
  per-run; stale-`@22` wording in `doc/ffi-proposal.md` fixed
  immediately rather than deferred to step 4 (`doc/externs.md` `@22`
  entry still pending, scheduled `@21`-independent).
- 2026-06-09 — plan review: established that `@21`'s decl fields are
  unprovable with clean seeded content (presence gap, relational
  agreement gap, `FreshCleanLocsUnrealizedOneRun` contradiction) and
  that the clean-content typing is semantically FR-false at top level
  (the errno cell is in no `InputSpec`, so initial states may disagree
  there). Plan reordered high-risk-first: content-poison flip →
  standalone decl-field prototype → presence-based `wfConfig` fold
  (supersedes the below-only fold) → combined registry. The `@22`
  re-touch grew accordingly: the `fn` operational clause needs a
  containment-preservation conjunct.
- Earlier — `@22` trusted end-to-end (see Status). The `wfConfig` fold
  was deliberately deferred until exercised by a trusted `.val` extern;
  threading the invariant as a separate hypothesis instead of folding
  was considered and rejected (it would touch the same ~119
  `wfConfig_preserved` call sites *plus* every per-operator signature).
