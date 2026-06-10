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

## Remaining work

### 1. `@21` operational trust: fold the reserved-address invariant into `wfConfig`

`@21`'s `operational` field (`ExternOperationalSafe.val`) requires
`wfValue cfg.nextAddr (Value.loc errnoAddr)`, i.e.
`errnoAddr < cfg.nextAddr`. The per-entry `val` clause demands this for
*every* `wfConfig`, which is false for small `nextAddr` — so `@21` cannot
be operationally trusted as the clause stands.

The fix: fold `RegistryReservedBelow cfg.registry cfg.nextAddr` into
`wfConfig` so the invariant is threaded by the existing `wfConfig`
machinery and reaches the `val` boundary. Re-establish preservation in
`wfConfig_preserved` / `wfConfig_mono` via registry immutability plus
`nextAddr` monotonicity (`RegistryReservedBelow_mono`).

**Why this is expensive.** The current `wfConfig` never reads
`cfg.registry`, so the FR proof stack coerces `wfConfig c` against
`wfConfig { c with registry := … }` by defeq throughout. Folding
`RegistryReservedBelow` makes `wfConfig` read `cfg.registry`, breaking
every such coercion — on the order of 100+ edit sites across `StepFRApp`,
`StepFRVlet`, and others, each needing a registry-equality bridge. The fold
is unexercised until a `.val` extern is actually trusted (the `val` clause
is vacuous for every current trusted registry), so it should land together
with the rest of `@21`'s fields, where it is immediately exercised and the
coercion churn is paid once.

Because this strengthens `wfConfig`, the assembled `@22` obligations must
also be re-touched to produce `RegistryReservedBelow` of their output
cursor (trivial — `@22` preserves the registry and `nextAddr`, so
`RegistryReservedBelow_mono` with `le_refl` applies); the churn estimate
includes those sites, not only the pre-existing ones.

### 2. Repair the `val` operational bridge and prove `builtinErrnoSpec`

Rewrite `TrustedRegistry.operationalSafe` so the registry-level `val`
clause consumes `cfg.registry = reg` (which it already receives but
discards) and the folded `RegistryReservedBelow` fact via
`wfValue_loc_of_RegistryReservedBelow`. Weakening the per-entry `val`
clause is not just the bridge: its *signature* changes, so every site that
currently discharges `val` as impossible (`impl = pfn ≠ val`) must be
updated to keep discharging the now-conditional clause trivially — the six
`.pfn` operational lemmas plus `pureUnaryCleanInt_operational`.

`@21`'s call fields are vacuous by extern kind (`ExternCallBoundaryRun` has
no `val` constructor), but its `declFR` / `declSingle` are a second,
independent open problem the operational fold does not touch: the
declaration boundary must realise a bare `Value.loc errnoAddr` as a
`ref int` (`valueHasETyp.loc` + `runtimeInstantiatesCtx` +
`valueConsistentWithRegime` for a reference value). No extern declaration
has ever realised a bare location — every existing trusted spec realises a
closure. It is plausibly doable (the `errno` cell is seeded in
`defaultInitialState.memory`), but it is novel work. Done means `@21`'s
operational and declaration fields close.

### 3. Combined `@21`/`@22` scenario registry and documentation sweep

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
- Update `doc/externs.md` / `doc/ffi-proposal.md` trust-status entries only
  after all `@21` fields compile.

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
