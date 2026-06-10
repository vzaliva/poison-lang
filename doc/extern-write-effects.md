# Extern Write-Effects Trust Plan

## Problem

The reserved-address proposal (formerly `doc/extern-addr-proposal.md`, now folded
into this document) was only **partially** implemented on `ffi`. What landed:

- `@22`'s `setErrImpl` resolves `"errno"` from the declaration-captured runtime
  environment and writes that referenced address;
  `ExternProofs.setErrImpl_operational` discharges the `operational` field from
  `wfVarEnv addr env` (axiom-clean).
- The reserved-address building blocks — `ReservedAddr`, `RegistryReservedBelow`
  (+ `_mono`, `_emptyExternRegistry`), and the witness
  `wfValue_loc_of_RegistryReservedBelow` — landed standalone in `Semantics.lean`;
  `wfConfig` was left registry-agnostic.
- `defaultInitialState.nextAddr` was raised to `errnoAddr + 1`.

Two pieces are **deferred** and are tracked here: (a) `@21`'s *operational* trust
still needs the `wfConfig` fold + `val`-bridge rewrite (see "Deferred: @21
operational trust" below); and (b) `@22`'s *relational* trust — the rest of this
document — including the captured-binding / no-retarget property that the
env-generic `setErrImpl_operational` does not establish. Neither `@21` nor `@22`
is in a `TrustedRegistry` yet.

To make either fully trusted, all five `ExternBoundarySpec` fields must compile:

```lean
declFR
callFR
declSingle
callSingle
operational
```

For `@22` only `operational` is done; the remaining four are relational: prove
that the runtime memory update performed by `setErrImpl` matches the type-level
post-state installed by `effects: { !errno :> (int :> clean {}) }`. For `@21`
(a `.val` extern) the `operational` field itself is still blocked on the deferred
fold/bridge below.

The representative source shape is:

```poison
let errno = extern val @21 : (ref int :> clean {}) in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

The target named by `!errno` is fixed when the `extern fn @22` declaration is
encountered. Later shadowing before a call must not retarget `@22`. Operationally
and proof-side, this is ordinary closure capture: the runtime closure stores the
declaration-time `VarEnv`, and the type closure stores the declaration-time
`VarTypeEnv`; application only extends those captured environments with the
argument binding.

This example binds `errno` through `@21`, but the `@22` proof should not depend
on that origin. The relevant fact is that the captured lexical environment
contains a well-typed reference named `errno` at declaration time. That reference
may come from a local allocation, from `@21`, or from any other trusted extern
value of the right reference type.

This work is not about building a broad library of externs. It is about adding
one realistic write-effect extern that demonstrates the trusted boundary proof
obligations for impure memory effects.

## Deferred: @21 operational trust (reserved-address fold + val bridge)

`@21` is `extern val @21 = Value.loc errnoAddr`. Its `operational` field
(`ExternOperationalSafe.val`) requires `wfValue cfg.nextAddr (Value.loc errnoAddr)`,
i.e. `errnoAddr < cfg.nextAddr`. The shipped per-entry `val` clause demands this
for *every* `wfConfig`, which is false for small `nextAddr` — so `@21` cannot be
operationally trusted as the clause stands.

The registry-derived fix; the mechanism already landed as standalone definitions:

- An address is *reserved* when the registry exposes it as a stored location
  value: `ReservedAddr reg a := ∃ id, reg.get? id = some (.val (Value.loc a))`.
- `RegistryReservedBelow reg n := ∀ a, ReservedAddr reg a → a < n`. The registry
  is fixed across evaluation and `nextAddr` only grows, so it is preserved by
  monotonicity (`RegistryReservedBelow_mono`).
- The witness `wfValue_loc_of_RegistryReservedBelow` already proves
  `RegistryReservedBelow reg n → reg.get? id = some (.val (Value.loc a)) →
  wfValue n (Value.loc a)`.

What remains (the deferred work):

1. **Fold `RegistryReservedBelow cfg.registry cfg.nextAddr` into `wfConfig`** so
   the invariant is threaded by the existing `wfConfig` machinery and reaches the
   `val` boundary. Re-establish preservation in `wfConfig_preserved` /
   `wfConfig_mono` via registry immutability + `nextAddr` monotonicity.
2. **Rewrite the `val` bridge** (`TrustedRegistry.operationalSafe`). The
   registry-level `RegistryOperationalSafe` `val` clause already receives
   `cfg.registry = reg`, but the bridge currently discards it and routes through
   the impossible unconditional per-entry `val` field. Make the bridge consume
   `cfg.registry = reg` plus the folded `RegistryReservedBelow` (via the witness),
   and weaken the per-entry `val` obligation so it is no longer the unprovable
   `∀ cfg, wfConfig cfg → wfValue cfg.nextAddr v`.

**Obstruction (why this is deferred, not done).** The old `wfConfig` never reads
`cfg.registry`, so the FR proof stack coerces `wfConfig c` against
`wfConfig { c with registry := … }` by defeq throughout. Folding
`RegistryReservedBelow` makes `wfConfig` read `cfg.registry`, breaking every such
coercion — on the order of 100+ edit sites across `StepFRApp`, `StepFRVlet`, and
others, each needing a registry-equality bridge. And the fold is **unexercised**
until a `.val` extern is actually trusted: the `val` clause is vacuous for every
current (all-`pfn`) trusted registry. So the fold's natural home is *here* —
landed together with `@21`'s relational fields when `@21` is first wired into a
`TrustedRegistry`, where it is immediately exercised and the coercion churn is
paid once, for a reason.

## Analysis

`ExternCallBoundaryRun` gives runtime facts for a successful impure extern
dispatch. For the proposed `setErrImpl`, those facts should reduce to:

```text
entry.argName = "n"
entry.unifiedEnv = VarEnv.update entry.capturedEnv "n" (Value.num n)
entry.capturedEnv.lookup "errno" = some (Value.loc a)
entry.unifiedEnv.lookup "errno" = some (Value.loc a)
entry.argValue = Value.num n
cf.memory = Memory.update entry.callConfig.memory a n
cf.nextAddr = entry.callConfig.nextAddr
o = Value.unit
```

`ExternBoundaryTyping.Call` gives the type-side facts. The `effects:` loop in
`applyFnTClosure` receives the type closure's captured environment extended with
the argument binding. For `@22`, the argument is named `n`, so resolving `!errno`
in that unified environment still means resolving the declaration-captured
`errno` target. The effect then updates the corresponding logical location set
in `res.memEnv'`.

The central proof obligation is the bridge between these two views:

```text
captured runtime env lookup "errno" = Value.loc a
captured type env lookup "errno" = ref ls
runtimeInstantiatesCtx says Value.loc a realizes some l in ls
the effect post-state updates l to int clean
the runtime post-state updates a to n
```

For the two-run `callFR` field, we additionally need the two writes to line up
relationally. The argument `n` is clean by the declared argument condition, so
the two runs' numeric arguments should agree. The target reference also needs a
stability story: the two runs must write corresponding logical cells.

This target-stability argument must be generic. It should not mention `@21`.
The proof should use the resolved captured type and runtime environment facts
for `errno`:

```text
captured type env lookup "errno" = ref ls
captured runtime env lookup "errno" = Value.loc a
valueHasETyp says a realizes some logical l in ls
```

Because the implementation receives the unified env, the shape lemmas should also
record the `@22` argument name `n` and the fact that updating the captured env
with `n` does not shadow `errno`.

The captured `errno` target needs no special restriction — the extern effect must
simply be typed the way an ordinary assignment through a reference is. Today
`applyExternEffect` strong-updates *every* location in the target locset `ls`
(`LocSet.fold ls … updateMemEnv … storedQt`, Typecheck.lean:1606), which is
unsound for `|ls| > 1`: the runtime writes one physical cell, so an unwritten
member of `ls` would be marked clean while stale. `typecheckAssign` already solves
exactly this (Typecheck.lean:1487-1497):

- singleton `ls = {l}` → strong update (`updateMemEnv`, `assign_singleton`);
- non-singleton `ls` → weak update (`updateLocsetWeak`, `assign_locset`), joining
  the stored type into each member's existing type;
- `storedPoison`/`storedPred` fold in the *target reference's own poison* `p1`
  (`joinPoison pc (joinPoison p1 p2)`; predicates erased when `p1 || pc`), so a
  dirty target poisons the written locations instead of claiming them clean.

The fix is to make `applyExternEffect` mirror `typecheckAssign`: the effect
becomes "an assignment of the declared effect type to the resolved target ref".
This removes any singleton/cleanness gate — a multi-location or dirty captured
`errno` is handled by the same weak-update + poison-join semantics assignment
already uses — and lets `@22`'s `callFR` reuse the assignment strong/weak
update-transport reasoning instead of a bespoke singleton proof. It also closes
a latent unsoundness: `applyExternEffect`'s current strong-update-all would
mis-type any multi-location effect target, invisible today only because no
effect-bearing extern is trusted.

The single-run fields have a different shape:

- `declSingle` and `declFR` are declaration-boundary closure facts. They should
  mostly reuse existing `extern fn` declaration proof patterns.
- `callSingle` runs under `ctx.pc = true`. In that mode, `applyExternEffect`
  stores poisoned effect cells, so inherited clean-location preservation should
  follow the existing "clean lookup was not written" helpers for effect loops.
- `callFR` is the main new proof: it must build `StepFRPost` for an impure
  runtime memory update whose type-level effect changes `res.memEnv'`.

## Proposed Approach

Keep `@22` as a declaration-captured lexical-target write. The implementation
is still called with the extern call's unified environment, but for this builtin
the lookup must denote the `errno` binding captured by the closure declaration,
not a later caller binding:

```lean
setErrImpl env (Value.num n) mem next :=
  match VarEnv.lookup env "errno" with
  | some (Value.loc a) => .ok (Value.unit, Memory.update mem a n, next)
  | _ => .error ...
```

Then prove the trusted spec in layers.

First, establish target stability for the captured `errno` reference. The proof
must be able to derive that the declaration-captured runtime `errno` values in
the two runs refer to corresponding logical cells, regardless of whether the
reference came from a local allocation or a trusted extern value. If the current
boundary cannot express or derive that condition for all well-typed reference
targets, add the smallest generic typing-side or trusted-agreement restriction
needed so `effects: { !errno ... }` is only trusted when the captured target
reference is stable enough for the runtime write and type-level postcondition to
agree.

Second, add reusable write-effect shape lemmas:

- `setErrImpl_ok_shape`: invert a successful runtime call.
- `setErrImpl_errno_target_wf`: the written address is below `nextAddr`, from
  `wfVarEnv`.
- `setErrImpl_errno_lookup_captured`: for the `@22` argument name `n`, lookup in
  the unified env agrees with lookup in the captured env for `"errno"`.
- `setErrImpl_bodyOutputConfig`: compute `entry.bodyOutputConfig cf`.
- `applyExternEffect_errno_shape`: specialize the type-level effect loop for
  the single `!errno` effect.

Third, prove the one-run post for `@22`. This should establish:

- return value is `unit`;
- no new logical locations are allocated for the simple `unit` return;
- `runtimeInstantiatesCtx (ctxAfter ctx res)` holds for the updated memory;
- `consistentWithRegime` holds after the effect update;
- inherited clean locations are preserved under `ctx.pc = true`.

Finally, prove the two-run `callFR`. The proof should split clean memory
agreement by logical location:

- if the location is the written `errno` target, both runs store the same clean
  argument value;
- if the location is not written, agreement comes from the pre-call
  `BodyEntryInputsAgree.agree`;
- if an effect target contains multiple logical locations, unwritten locations
  must be handled explicitly rather than assumed to have changed.

## Plan

1. Align the **heap update** of `applyExternEffect` with `typecheckAssign` (the
   dependency-invalidation half is split out as step 1b below), then prove the `@22`
   effect-update / target-resolution lemma. The scoping / no-retarget half is
   structural and cheap: the runtime call entry uses the closure-captured `VarEnv`
   (`ExternCallFnFacts.unifiedEnv_eq`), the typing closure uses the
   declaration-captured `VarTypeEnv` (`ofCaptured tenv`), and extending either
   with argument `n` does not shadow `errno` (`n ≠ errno`). The substance is the
   effect update: change `applyExternEffect` to mirror assignment (singleton
   strong / non-singleton `updateLocsetWeak`, folding the target ref's poison `p1`
   into `storedPoison`/`storedPred`), then show the resulting memEnv update
   transports across the two runs exactly as the assignment weak/strong update
   already does. No singleton or cleanness restriction is needed — multi-location
   and dirty targets are covered by the weak-update + poison-join. This is a
   typechecking change: re-check the existing effect examples (errno is a clean
   singleton, so their singleton branch is unchanged). Extract the reusable
   weak-update / store-transport lemmas to a shared layer (`StepFR.lean`,
   `TypeSafety.lean`, or a small dedicated helper module) — the `@22` proof must
   NOT import `StepFRAssign`; the per-operator FR files stay mutually independent.

   **Status — heap update DONE (uncommitted).** `applyExternEffect` now
   mirrors `typecheckAssign`'s *memory update*: singleton strong /
   non-singleton `updateLocsetWeak`, with the target ref's own poison
   `p1 = qt.poison` folded into `storedPoison`/`storedPred`. Reusable transport
   lemmas live in `TypeSafety.lean` / `StepFR.lean` (`assign_memEnv_formula_*`
   plus `updateLocsetWeak_lookup_mem_props`), reachable without importing
   `StepFRAssign`. This closes the latent strong-update-all unsoundness; build
   green, 0-sorry, axiom-clean, 115 example tests byte-identical
   (clean-singleton errno unchanged). NOT done: the `@22`-specific two-run
   transport (step 4) and the dependency-invalidation parity (step 1b).

   **Step 1b — effect dependency invalidation.** The heap update above mirrors
   `typecheckAssign` but its dependency invalidation did not: `typecheckAssign`
   runs `invalidateTagDeps` / `invalidateRegimeDeps` on the written locset,
   dropping any guard tag whose `deps` include a written location; the effect
   path left `tagEnv'` / `regime'` untouched. A guard *can* depend on an effect
   target — `if deref errno > 0 then …` yields a tag whose `deps` contain
   errno's location.

   **Status — invalidation DONE + integrated (uncommitted, green).** The `.fn`
   extern returns now invalidate guard/regime deps on the written effect targets:
   `tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv)`
   and `regime' := applyExternRegimePolicy (invalidateRegimeDepsEffect
   result2.regime' result2.tagEnv' (effectTargetLocs …)) …`
   (`effectTargetLocs` + `invalidateRegimeDepsEffect` are new in
   `LeanPoison/Typecheck.lean`; `invalidateRegimeDepsEffect` differs from
   assignment's `invalidateRegimeDeps` by **keeping** regime tags absent from the
   tagEnv — the lp55xx-read fix). The full FR proof stack was re-proved against
   this change: foundational equality lemmas (`applyFnTClosure_extern_{tagEnv_eq,
   regime_eq_or_policy, regime_preserve_some, regime_mono}`) became sub-map /
   `monotoneStep` forms, all ~11 consumers fixed. **`lake build LeanProofs` =
   8517 jobs green, 115/115 tests.** Shared lemmas added to `TypeSafety.lean`
   (`invalidate{TagDeps,RegimeDepsEffect}_*` sub-map / survive / monotone).

   **Step 1b.2 — value-correct return-guard materialisation (REQUIRED; the real
   fix for the residual gap; in progress).** Step-1b invalidation only catches
   guards that are *materialised in the tagEnv*. But an extern's **return** guard
   is NOT in the tagEnv at the call — `collectAndAllocExternTags` returns
   `(tagMapping, nextTag)` only, and the sole materialiser (`matchGuard`) runs at
   an `if`, not at a store. So a value guarded by `deref errno > 0` (tag `k ∉
   tagEnv`, driver-asserted true) can be stored into a cell and reach a later
   `set_err` call with `k ∉ tagEnv`; the effect invalidation **keeps** it
   (`none ⇒ true`), the cell's `consistentWithRegime.locsRegime.withPred_ok`
   obligation (gated on `R.lookup? k ≠ none`) still fires, and `predSat` cannot
   transport across the errno write (`mem_monotone` uses `extractDepsFromPred`).
   The unmasked boundary `consistentWithRegime` is genuinely false for this
   reachable config. **Fix (decided): materialise extern return guards into the
   tagEnv at the call**, value-correctly, so an errno-reading return guard carries
   `deps ∋ errno` and a later `set_err` invalidation drops it (vacuous
   obligation), while non-errno guards (lp55xx) stay and remain clean.

   **A proof-only masked boundary was REJECTED:** it would leave the executable
   stale-regime fact in place (`qtypCleanUnderRegime` can still read `R(k)=true`
   later) — hiding the inconsistency, not fixing it.

   The naive version (insert `⟨false, deps⟩` for every guardClosure return)
   **FAILED behaviourally — 10/115 tests regress, lp55xx-read `poison false→true`**
   — because the tagEnv entry's `value` field *drives the depoison*, so a dummy
   `false` poisons cells the driver keeps clean. Required design (value-correct,
   post-invalidation):

   1. First invalidate old/materialised deps from the pre-call tagEnv and regime
      (the Step-1b `invalidate*` above).
   2. Then install *this* call's fresh guard tags.
   3. For each fresh tag `k`, compute `deps` from the matching `guardClosure`
      (`extractDepsFromPred`).
   4. If `ctx.externRegime id k = some b`, insert **both**
      `tagEnv[k] := ⟨value := b, deps⟩` **and** `regime[k] := b` (the regime half
      is already `applyExternRegimePolicy`'s insert-if-absent; add the tagEnv half).
   5. If the policy is `none`, do **not** insert a fake tagEnv entry (an
      undetermined guard stays out of the tagEnv — that was the `value=false` bug).

   This preserves lp55xx-read (driver `1=true`, empty deps ⇒ materialised `true`,
   stays clean) and, for an errno-reading guard, gives `deps ∋ errno` so a later
   `set_err` invalidates the tag and drops the stale regime fact. Applies to all
   four extern simple-returns (fn + pfn, AtCursor + non; `LeanPoison/Typecheck.lean`
   ~1727/1828/1926/2014). Expect a SECOND round of proof churn (the foundational
   `applyFnTClosure_extern_tagEnv_eq` etc. conclusions gain the install term;
   reduces to the current form for `noPred` returns like `set_err`).

   **Regression test (add BEFORE proof churn):** an extern returns/effects a value
   whose guard predicate reads `errno`; `set_err` then changes `errno`; a later
   clean use must NOT de-poison through the old guard. Run all 115 + this new test
   green after the typechecker change, before touching proofs.

   **Status — step 1b.2 DONE (uncommitted; typechecker + tests + full proof churn
   green).** Implemented as `installReturnGuard` (`LeanPoison/Typecheck.lean`,
   just before the typechecking `mutual` block) applied at the four extern
   simple-return sites, with one deliberate refinement of point 4: the install is
   gated on the **final post-call regime's value at the fresh tag** rather
   than on
   `ctx.externRegime` directly. Rationale: driver assertions also arrive through
   the *initial* `--regime` map (the lp55xx pattern asserts a future tag that the
   policy function knows nothing about), so policy-gating would materialise
   nothing for them and leave the doc's own regression scenario unfixed;
   regime-gating covers both driver mechanisms, reduces to policy-gating when the
   policy is the only source, and makes `tagEnvConsistentWithRegime` hold by
   construction (the installed value IS the regime's value). Point 5 is preserved:
   a regime-undetermined guard is not materialised. Two further bounded choices:
   the installer is pure and skips a predicate whose `extractDepsFromPred` fails
   (such predicates already fail at any later `if` via `matchGuard`), and only the
   resolved **return** predicate of simple returns is installed — a `guardOnly`
   return predicate, an effect-only guard tag, and nested-return effect guards
   are NOT materialised (documented residual; the lp55xx shared-index pattern is
   covered because its return predicate is the guard closure).

   **Companion soundness fix (step 1b.2 fallout): weak-update untracked-member
   degradation.** `updateLocsetWeak` inserts the joined entry at *every*
   member of
   the locset, including members absent from the memory environment (possible
   after conservative if/while typing). With regime-live stored guards such an
   inserted cell would carry a symbolic guard claim about an untracked (and,
   in a
   well-formed run, unrealized) cell — unjustifiable at the FR layer. The weak
   update now degrades the joined predicate to `noPred` whenever a member is
   untracked (the poison join is unchanged); behaviourally invisible on the whole
   test suite.

   **Regression tests added:** `examples/extern_set_err_stale_guard.poison`
   (errno-reading driver-asserted return guard; `set_err 0` invalidates it; the
   later clean-argument gate REJECTS — A/B-verified to be wrongly accepted with
   the installer disabled) and `examples/extern_set_err_unrelated_guard.poison`
   (positive control: a guard reading only its bound argument survives `set_err`
   and the program still typechecks and runs). Three `--extern-regime` goldens
   (`extern_arg_precond_sqrt`, `extern_captures_guarded`,
   `extern_captures_join_guarded`) legitimately gained the materialised
   `tagEnv: { 1 := { value := true, deps := [] } }` entry in their verbose dumps;
   types and results are unchanged. 117/117 tests green.

   **Proof churn (DONE, green, 0-sorry, no warnings).** `TypeSafety.lean`:
   `installReturnGuard_get?_{eq_of_not_guard, cases, ne_none_of_ne_none}`,
   `resolveSyntaxPred_guardClosure_tag_from_mapping` (moved public from `StepFR`),
   and the per-flavor `apply{Fn,PFn}TClosure_extern_tagEnv_{lookup_eq_of_lt,
   get_cases}` replacing the old tagEnv equality/sub-map lemmas (an output binding
   is an invalidated input binding OR the freshly installed guard, whose value the
   output regime interprets); `applyFnTClosure_extern_regime_preserve_some`'s
   survival precondition is now stated against the invalidated input tagEnv.
   `StepFR.lean`: the `*_tag_absent_*` lemmas weakened to
   `*_tag_absent_or_installed_*`; masked-absence and masked/unmasked
   regime-consistency extern cases repaired via the `get_cases` disjunction
   (installed tags are regime-interpreted, and `≥` the cursor base hence never
   masked). `ExternBoundaryProofs.lean`: `fnExternFinishAtCursor` mirrors the
   install (new `fuel` parameter). `StepFRAssign.lean`: the pre-1b.2
   `*_guardClosure_pred_implies_tag_absent` lemma cluster (a stored guard is
   never in the tagEnv) is now FALSE and was deleted; the five consumer sites
   case on the tag entry — absent keeps the old vacuity route, present (the new,
   genuinely reachable case) proves the obligation via the shared
   `assign_stored_guard_locsRegime` (singleton: RHS `valueConsistentWithRegime`
   evidence at the written member; weak: `fold_joinPred_guardClosure_members`
   join-inversion + pre-assign cell consistency, written-address split) and, for
   `agreeOnClean`, the guard-clean route (`withPred_true_eq`, RHS
   `resultAgreesIfClean` under guard-cleanness, shared written-member witness).

   **Proof-layer finding (recorded, not fixed here):** `PredSatLaws.mem_monotone`
   as stated quantifies over an arbitrary `pred`, so instantiating it at
   `Predicate.noPred` yields unconditional memory-independence of `predSat` —
   and the existing stack already exploits exactly this
   (`predSat_mem_noPred_compat` / `qtypPredHolds_mem_compat_of_predSatLaws`,
   ~95 uses incl. all of `StepFRAssign`). The `@22` proofs use the same
   established transport discipline. Tightening the law to tie `pred` to the
   guard's canonical predicate (making memory-dependence real at the proof layer)
   is future work that the step-1b/1b.2 dependency machinery now makes feasible.

2. Add the `@22` runtime and typing shape lemmas.
   Keep these local to `LeanProofs/ExternProofs.lean` unless another extern
   needs them. Done means successful `setErrImpl` runs, captured-`errno` lookup,
   non-shadowing by argument `n`, `bodyOutputConfig`, and the corresponding
   one-effect type result can be inverted without reopening large definitions.

3. Prove `@22` `callSingle`.
   Use the `ctx.pc = true` path and existing effect-loop preservation helpers.
   Done means the single-run post is proven for the runtime memory update.

   **Status — DONE (uncommitted, 0 sorries, axiom-clean).**
   `builtinSetErr_callSingle` (`LeanProofs/ExternProofs.lean`) is complete — the
   first fully proven `.fn` (memory-writing) `callSingle`. It is assembled from
   the typing inversion `builtinSetErr_call_clean_shape` (whose
   `tagEnv'`/`regime'` conjuncts state the Step-1b invalidated forms; set_err's
   `noPred` return makes the step-1b.2 install reduce to the identity) and the
   runtime inversion `builtinSetErr_callRun_output`. The three formerly open
   conjuncts:
   - **wfTagMeaningCtx**: written cells are `⟨int, true, noPred⟩` (no guard
     descriptor, by `QTypInQTyp_eq_of_nonFunctionTarget` on the int cell);
     unwritten cells and the varEnv route to the input `wfTagMeaningCtx`.
   - **consistentWithRegime**: written cells carry no guard tag (vacuous); for
     unwritten cells the output-regime gate transports to the input regime
     (`invalidateRegimeDepsEffect_lookup_some_imp` — the invalidation is a
     value-preserving sub-map), the realized address differs from the written
     errno address by `θ`-injectivity, and the predicate facts move across the
     write by the `PredSatLaws` mem-compatibility (see the proof-layer finding
     under step 1b.2); the dropped (materialised errno-reading) guards are
     vacuous by the gate. Captured-closure evidence transports by
     `closureCapturedVarsRegime_monotone` + `_transport_μ`.
   - **PreservesInheritedFinalCleanLocsOneRun**: a clean (or guard-clean) output
     cell is unwritten (written cells are poisoned `noPred`), so by
     `θ`-injectivity its realized address is untouched by the write
     (`preserve_value`; unrealized cells are `both_unrealized`).
   `#print axioms ExternProofs.builtinSetErr_callSingle` = `propext,
   Classical.choice, Quot.sound` only.

4. Prove `@22` `callFR`.
   This is the main relational write-effect proof, and `@22` is the first-ever
   complete trusted `.fn` spec (every existing complete spec is `.pfn`), so the
   `.fn` call path — `ExternCallFnFacts` with its memory-modifying `output_config`
   — is unexercised end-to-end; budget that novelty as an independent risk axis
   from "write-effect". This step must also settle the effect
   dependency-invalidation question (step 1b): `@22` writes a *clean* errno
   cell, so the orphaning argument that covers poisoned effects does not apply
   directly. Done means paired successful `@22` calls produce
   `StepFRPost` for `entry.bodyOutputConfig cf₀` and `entry.bodyOutputConfig cf₁`.
   Split clean-memory agreement by logical location, reusing the shared
   update-transport lemmas (extracted per step 1, not imported from
   `StepFRAssign`): a written singleton target carries the clean-argument
   agreement; a multi-location target uses the weak update (members joined, dirty
   targets poisoned) so unwritten members are not force-marked clean; unwritten
   clean locations come from the pre-call `BodyEntryInputsAgree.agree`.

   **Status — DONE (0 sorries, axiom-clean: propext/Classical.choice/Quot.sound).**
   `builtinSetErr_callFR` (`LeanProofs/ExternProofs.lean`) proves the full
   19-conjunct two-run `StepFRPost`. The per-run conjuncts reuse the
   `callSingle` machinery without its `pc = true` hypothesis (the effect
   predicate is `noPred` on both gate branches, so written cells always store
   `noPred` but may be *clean*). The relational core is `agreeOnClean`, split
   by membership in the effect target locset:
   - *written cell, clean*: cleanness of the stored join forces the pc and the
     captured errno reference clean; the input agreement on the clean `errno`
     binding yields one shared written logical location for both runs
     (`agreeValueUnder_ref_common_loc`), at which both runs hold the agreeing
     clean argument (`builtinSetErr_callRun_argEq`, the gate against the clean
     declared precondition, mirroring `abs`); any other locset member is
     unwritten in both runs (`θ`-injectivity against the shared location) and
     transports from the input agreement (a present member was clean before the
     call by the weak-join poison inversion; an absent member is unrealized in
     both runs);
   - *written cell, dirty*: poisoned `noPred` cells carry no agreement
     obligation (vacuous);
   - *unwritten cells and variables*: the input agreement transports across the
     two single-address writes (`θ`-injectivity per run) and the regime shrink,
     via the public `agreeValueUnder` memory/monotone transports.
   Supporting additions: the typing inversion gained `res.nextLoc' = ctx.nextLoc`
   and the clean-gated argument binding (`builtinSetErr_call_clean_shape`);
   `builtinSetErr_callRun_bodyVar` exposes the runtime `"n"` binding. The
   `StepFRPost`-only conjuncts absent from `callSingle` (`wfTypeContext`,
   `TagBoundedCtx`, `wfConfig` of the written configs via
   `setErrImpl_errno_target_wf`, `regimeConsistentWithCtx` via the coordinated
   invalidation filters) are discharged from `BodyEntryInputsAgree` plus the
   effect-update formulas.

5. Author `builtinSetErrDecl` / `builtinSetErrSpec` and prove `@22`
   `declSingle` / `declFR`.
   **Partially pulled forward into step 3:** `builtinSetErrDecl` (plus
   `builtinSetErrRetSpec` / `builtinSetErrEffect` / `builtinSetErrImpl`) was
   authored during step 3, because the `callSingle` goal is *stated against* the
   concrete declaration (as `builtinAbsDecl` precedes `builtinAbs_callSingle`).
   What remains here is `builtinSetErrSpec` assembly and the `declSingle` /
   `declFR` fields.
   Reuse existing impure extern declaration proof patterns for the closure value.
   Two pieces the operational milestone left open: there is no
   `builtinSetErrDecl : ExternDeclaration` yet (it must be authored), and
   `setErrImpl_operational`'s standalone signature must be *wrapped* into the
   `ExternOperationalSafe` structure for `.fn setErrImpl` (its `val`/`pfn` clauses
   vacuous) — not a free "combine". Done means the declaration closure is
   consistent/agrees under the captured-environment assumptions and all five
   fields combine into `builtinSetErrSpec`.

   **Status — DONE (0 sorries, axiom-clean). `builtinSetErrSpec :
   ExternBoundarySpec builtinSetErrDecl builtinSetErrImpl` is complete — the
   first fully proven `.fn` (write-effect) trusted entry.**
   `builtinSetErr_declSingle` / `builtinSetErr_declFR` realize the first `.fn`
   declaration: an `arrow` closure carrying the declared effects, mirroring the
   `abs` (`.pfn`) declaration fields with the `fn`-flavored constructors
   (`valueHasETyp.closure_extern`, `deepValueQTypProperty.closure_extern`,
   `QTypRespectsTagMeaning_fn_extern`,
   `agreeValueUnder.clean_internal_arrow_extern`); no tags or locations are
   allocated, so `ctxAfter ctx res = ctx` and both posts collapse onto the input
   hypotheses. `builtinSetErrImpl_operationalSafe` wraps
   `setErrImpl_operational` into the `fn` clause of `ExternOperationalSafe`
   (the `pfn`/`val` clauses are impossible by constructor mismatch).
   `#print axioms ExternProofs.builtinSetErrSpec` = `propext, Classical.choice,
   Quot.sound`.

6. Thread the `@21` reserved-address invariant through `wfConfig`.
   Fold `RegistryReservedBelow cfg.registry cfg.nextAddr` into `wfConfig`, then
   re-establish `wfConfig_preserved` and monotonicity using registry immutability
   plus `nextAddr` monotonicity. Done means the FR stack compiles with explicit
   registry-equality bridges at the former registry-agnostic config coercions.
   Because this strengthens `wfConfig`, the `@22` `callFR` assembled in steps 1-5
   must also be re-touched to produce `RegistryReservedBelow` of its output cursor
   (trivial — `@22` preserves the registry and `nextAddr`, so
   `RegistryReservedBelow_mono` with `le_refl` applies); the churn estimate should
   include the just-assembled `@22` obligations, not only the pre-existing sites.

7. Repair the `@21` val operational bridge and prove `builtinErrnoSpec`.
   Rewrite `TrustedRegistry.operationalSafe` so the registry-level `val` clause
   consumes `cfg.registry = reg` and the folded `RegistryReservedBelow` fact via
   `wfValue_loc_of_RegistryReservedBelow`. Weakening the per-entry `val` clause
   is not just the bridge: its *signature* changes, so every site that currently
   discharges `val` as impossible (`impl = pfn ≠ val`) must be updated to keep
   discharging the now-conditional clause trivially — the six `.pfn` operational
   lemmas plus `pureUnaryCleanInt_operational`.

   `@21`'s call fields are vacuous by extern kind (`ExternCallBoundaryRun` has no
   `val` constructor), but its `declFR` / `declSingle` are a SECOND, independent
   open problem the operational fold does not touch: the declaration boundary must
   realise a bare `Value.loc errnoAddr` as a `ref int` (`valueHasETyp.loc` +
   `runtimeInstantiatesCtx` + `valueConsistentWithRegime` for a reference value).
   No extern declaration has ever realised a bare location — every existing
   trusted spec is `.pfn` realising a closure. It is plausibly doable (the `errno`
   cell is seeded in `defaultInitialState.memory`), but it is novel work, not the
   "reuse existing patterns" the rest of this track implies. Done means `@21`'s
   operational AND declaration fields close.

8. Assemble a scenario trusted registry for `@21`/`@22` and bridge to the
   interpreter.
   There is no single "default trusted registry": FR is proved per-scenario at
   `TrustedRegistry.toRuntimeRegistry <subsetRegistry>`, and a `TrustedRegistry`
   projecting to the *whole* `defaultRegistry` is impossible — it would need a
   compiling entry for `@19` (sqrt), which has no spec and is recorded infeasible
   under the 0-sorry gate. So put `builtinErrnoSpec` and `builtinSetErrSpec`
   in a dedicated scenario `TrustedRegistry` with only `@21`/`@22`, and prove
   FR for a program reaching them via `TypeSystemEnforcesFaultRobustness_at`
   (whose `TrustedRegistryAgreesWithReachable` premise requires only the
   externs the program *reaches*, not all of `defaultRegistry`). Separately,
   add per-id bridge lemmas `defaultRegistry_lookup_errno` /
   `defaultRegistry_lookup_seterr` (`defaultRegistry.get? id = some
   builtin…Impl`), mirroring the existing
   `defaultRegistry_lookup_max10/11/abs/memderef`; `@19` never enters. State
   explicitly whether this step delivers full top-level FR integration or
   stops at the per-scenario runtime-projection agreement (the existing
   precedent does the
   latter). End-to-end example tests already exist (`extern_set_err.poison`,
   `extern_errno.poison`); update `doc/externs.md` / `doc/ffi-proposal.md` status
   only after all fields compile.

   **Status — `@22`-only slice DONE; the `@21`/`@22` combined registry stays
   blocked on steps 6-7.** `LeanProofs/SetErrWriteEffectFR.lean` delivers the
   program-level capstone for the bare `@22` declaration node (mirroring
   `memReadCaptures_FR`'s bare-declaration form): `setErrRegistry :=
   [⟨builtinSetErrDecl, builtinSetErrImpl, builtinSetErrSpec⟩]`, the
   registry-agreement witness, and `setErrWriteEffect_FR` — the first
   program-level FR result whose trusted registry contains a memory-writing
   extern (axioms: the standard three plus the top-level theorem's pre-existing
   `native_decide` baseline; `builtinSetErrSpec` itself is propext/choice/quot
   only). `defaultRegistry_lookup_seterr` bridges the interpreter dispatch for
   `@22` to the proven `setErrImpl` (mirroring `defaultRegistry_lookup_abs`).
   Still open here: the `@21`-inclusive scenario registry (after steps 6-7) and
   the `externs.md` / `ffi-proposal.md` status sweeps.

## History

`doc/extern-addr-proposal.md` (now deleted) proposed the reserved-address
invariant and the `setErrImpl` lexical-target change. Its operational half — CP1
(`defaultInitialState.nextAddr`) and CP4 (`setErrImpl` plus
`setErrImpl_operational`) — and the reserved-address building blocks landed on
`ffi`; its `wfConfig` fold and
`val`-bridge repair were deferred (see "Deferred: @21 operational trust"). This
document is now the single home for the remaining `@21` operational and `@22`
relational write-effect trust work.
