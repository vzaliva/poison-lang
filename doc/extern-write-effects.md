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

1. Align `applyExternEffect` with `typecheckAssign`, then prove the `@22`
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

2. Add the `@22` runtime and typing shape lemmas.
   Keep these local to `LeanProofs/ExternProofs.lean` unless another extern
   needs them. Done means successful `setErrImpl` runs, captured-`errno` lookup,
   non-shadowing by argument `n`, `bodyOutputConfig`, and the corresponding
   one-effect type result can be inverted without reopening large definitions.

3. Prove `@22` `callSingle`.
   Use the `ctx.pc = true` path and existing effect-loop preservation helpers.
   Done means the single-run post is proven for the runtime memory update.

4. Prove `@22` `callFR`.
   This is the main relational write-effect proof, and `@22` is the first-ever
   complete trusted `.fn` spec (every existing complete spec is `.pfn`), so the
   `.fn` call path — `ExternCallFnFacts` with its memory-modifying `output_config`
   — is unexercised end-to-end; budget that novelty as an independent risk axis
   from "write-effect". Done means paired successful `@22` calls produce
   `StepFRPost` for `entry.bodyOutputConfig cf₀` and `entry.bodyOutputConfig cf₁`.
   Split clean-memory agreement by logical location, reusing the shared
   update-transport lemmas (extracted per step 1, not imported from
   `StepFRAssign`): a written singleton target carries the clean-argument
   agreement; a multi-location target uses the weak update (members joined, dirty
   targets poisoned) so unwritten members are not force-marked clean; unwritten
   clean locations come from the pre-call `BodyEntryInputsAgree.agree`.

5. Author `builtinSetErrDecl` / `builtinSetErrSpec` and prove `@22`
   `declSingle` / `declFR`.
   Reuse existing impure extern declaration proof patterns for the closure value.
   Two pieces the operational milestone left open: there is no
   `builtinSetErrDecl : ExternDeclaration` yet (it must be authored), and
   `setErrImpl_operational`'s standalone signature must be *wrapped* into the
   `ExternOperationalSafe` structure for `.fn setErrImpl` (its `val`/`pfn` clauses
   vacuous) — not a free "combine". Done means the declaration closure is
   consistent/agrees under the captured-environment assumptions and all five
   fields combine into `builtinSetErrSpec`.

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

## History

`doc/extern-addr-proposal.md` (now deleted) proposed the reserved-address
invariant and the `setErrImpl` lexical-target change. Its operational half — CP1
(`defaultInitialState.nextAddr`) and CP4 (`setErrImpl` plus
`setErrImpl_operational`) — and the reserved-address building blocks landed on
`ffi`; its `wfConfig` fold and
`val`-bridge repair were deferred (see "Deferred: @21 operational trust"). This
document is now the single home for the remaining `@21` operational and `@22`
relational write-effect trust work.
