# Poison FFI: Runtime Baseline and Proof Interface

Status: working document. The runtime side is implemented and is treated here
as a baseline. The fault-robustness proof has a populated-registry theorem that
consumes trusted extern boundary evidence. Concrete trusted specs exist for
`abs`, the curried-`max` pair, the explicit-argument memory-read extern
`@23`, the `errno` reference extern `@21`, and the errno-style impure
write-effect extern `@22` (`set_err` — the trusted `.fn` entry, with the
program-level capstone `ExternRegimeInt.setErrWriteEffect_FR`; see
`doc/externs.md`, `@22`). Read-dependency/captures support is implemented.

Goal: give `extern val`, `extern ref`, `extern fn`, and `extern pfn` intended
semantics while keeping implementations outside Poison and making the
fault-robustness (FR) boundary explicit.

Related documents:

- `doc/ffi-axioms.md` is the proof-boundary reference for
  `ExternBoundarySpec`, `TrustedRegistry`, and FR-facing extern evidence.
- `doc/extern-poison.md` is the source-language contract reference for argument
  preconditions, return/effect poison meaning, regimes, and trust triage.
- `doc/poison-interpreter.md` documents executable CLI behavior and the default
  runtime extern registry.

## Planning

The FFI mechanism and external-boundary proof interface are done. What remains is
the shipped extern cleanup and default-registry assembly:

1. **Finish trusted specs for shipped gaps.** Prove default trusted entries
   for the shipped builtins that still lack concrete specs: only the
   sqrt-style guarded input (`@19`) remains. (`@22`, the errno-style impure
   update, is done — `ExternProofs.builtinSetErrSpec` is the first trusted
   `.fn` write-effect entry — and `@21`, the reference-valued extern declared
   with the `extern ref ... points_to: ...` form, is done:
   `ExternProofs.builtinErrnoSpec`, carried by the reserved-cell
   invariants `RegistryReservedBelow` / `RegistryReservedWF` /
   `ReservedDiscipline`; see the `@21` entry in `doc/externs.md`. The
   clean-`points_to:` extension is tracked in issue #140.)

   - `@19` is blocked on **predicate semantics for value-attached guards**. A
     faithful guarded-input contract must derive a value fact from an *inactive*
     guard (`¬predSat ⟹ n < 0`), which the abstract `predSat` / `match_iff`
     machinery does not expose for guards carried on values (it is forward and
     needs an evaluated `if` condition). Pinning only the argument poison flag
     would silently reduce `@19` to a clean-input extern that ignores its
     predicate. Closing it requires expanding the predicate/guard trust surface.

   See `doc/externs.md` (`@19`, `@21`).
2. **Assemble the default trusted registry.** Define `defaultTrustedRegistry`
   for the shipped extern set, then prove
   `TrustedRegistry.toRuntimeRegistry defaultTrustedRegistry` agrees with
   `defaultRegistry` from `LeanPoison/ExternBuiltins.lean` by extensional
   equality or lookup agreement. Because trusted lookup is id-based, this
   registry must choose one canonical declaration per extern id; alternate
   same-id proof variants such as guarded/capture-specialized `@11` specs remain
   specialized examples unless their declaration is the chosen shipped contract.

Deliberately deferred:

- **Helper extraction after repetition.** Direct `ExternBoundarySpec` proofs are
  large, but public constructors should be introduced only after repeated
  concrete proofs show a stable shape. Likely future helpers include
  `pureUnaryCleanInt`, `nestedPfn`, `refValInitialized`, and
  `impureCellUpdate`.

## Scope

- Research design for reasoning about externs in FR, not a production
  cross-language FFI.
- "FFI" is used loosely: the goal is a model of an extern boundary rich
  enough to study what FR requires.
- Executable extern behaviour is supplied by surrounding Lean code (the
  built-in set in `LeanPoison/ExternBuiltins.lean`, wired in by `Main.lean`)
  and passed into the semantics as a registry.
- The same interface is also intended to support reasoning about
  separately verified Poison components treated abstractly as externs;
  building the actual separate-compilation pipeline is out of scope.

## Glossary

- `extern`: a Poison declaration whose executable behaviour is supplied
  externally rather than by a Poison body.
- `extern id`: the explicit `@id` attached to an extern declaration. This is
  the language-level identity used by runtime dispatch, nested returned
  callables, and proof-facing evidence indexing.
- `registry`: the Lean-supplied mapping from extern identities to runtime
  values or callables.
- `basic shape`: the coarse runtime kind checked dynamically — integer,
  boolean, unit, string, location, or callable — as distinct from full
  summary conformance.
- `trusted extern`: an extern id with a `TrustedExternEntry` in a
  `TrustedRegistry`; ids absent from that registry have no proof-facing
  boundary evidence.
- `evidence`: an explicit proof object or theorem bundle supplying FR-facing
  guarantees for trusted externs.

## Non-goals

- Designing a production-grade interface to C, Rust, OCaml, or other
  external languages.
- Implementing a full separate-compilation, module, or linker pipeline.
- Tooling details such as hot reloading, debugging, or deployment
  workflows.
- Duplicating the detailed runtime rules that live in the Lean
  implementation.

## Part I: Runtime Baseline (Implemented)

The runtime side is in place. The source of truth is the code:

- `LeanPoison/Runtime.lean` — `ExternImpl`, `ExternRegistry`,
  `ExternError`, `register`, `valueMatchesTyp`, and the `registry` field
  of `Config`.
- `LeanPoison/BigStep.lean` — extern dispatch prologue, application
  branches, nested-return shape validation, and fuel accounting.
- `LeanProofs/ExternTypingAssumptions.lean` — the typing-side contract floor:
  `ExternTypingAssumptions.externPredSatDelta` (predicate-law preservation
  across structural extern allocation batches), packaged as a field of the
  `ExternTypingAssumptions` structure that callers must supply to
  instantiate the FR theorem.

### Runtime Summary

- Extern identity is explicit through mandatory `@id` syntax, including
  on nested callable return descriptors.
- Source programs should not reuse the same id across multiple extern
  declarations; the typechecker enforces this only for `extern ref` (each id
  may be declared at most once per program), and `register` rejects
  duplicate id registrations at driver-setup time.
- Runtime dispatch uses a flat registry keyed by extern id, stored in
  `Config`, and fixed for the duration of evaluation.
- `extern val` dispatch returns a registered value after shallow shape
  checking (`valueMatchesTyp`).
- `extern fn` and `extern pfn` behave as ordinary Poison closures whose
  body is the corresponding extern AST node.
- Nested callable returns are supplied directly by the implementation and
  validated against the declared nested return descriptor; mismatches
  surface as `ExternError.nestedReturnMismatch`.
- Runtime checking is deliberately shallow: it checks declared
  identity/kind/basic shape and nested-return wrapper shape, not poison or
  FR-level conformance.
- Executable extern input types are restricted to the first-order surface
  types `{ int, bool, unit, string, ref int }`; function-typed inputs and
  reference-typed returns are rejected. Higher-order callbacks are
  therefore out of scope.
- Each extern invocation consumes one evaluator step in the fuel story.
- `beval` remains a total pure Lean function; executable extern behaviour
  is computable Lean-level data, not I/O.
- Within a fixed registry, operational behaviour is deterministic by
  construction.

### Extern Callable Value Shape

The proof layer treats "this runtime value is an extern callable" as a
structural predicate on `Value`:

- An impure extern callable is exactly a value of the form
  `Value.closure argName (Expr.externFn id ... effects captures) env`.
- A pure extern callable is exactly a value of the form
  `Value.peClosure argName (Expr.externPfn id ... ret captures) env`.
- `extern fn` and `extern pfn` capture the surrounding runtime environment
  at the point where the extern expression is evaluated: their summaries
  may mention Poison variables in scope, so later calls must retain the
  producing environment. They behave like ordinary closures in this respect
  and never mutate `env`.
- `extern val` captures nothing; it is looked up directly in the registry.
- Registry identity and dispatch depend only on the wrapped extern AST
  node (and its `id`), never on the captured environment. Proofs that
  compare or transport extern callables can therefore ignore `env` when
  only identity is at stake.

Nested returned callables use the same shape with the nested descriptor's
`id`. Any other value returned where a nested callable is expected is
rejected at dispatch.

### Driver Registry Contracts

These are the semantic assumptions the FR / `wfConfig` proof layer is
allowed to consume about registered implementations. They are driver
obligations, not runtime-checked invariants.

Flat contracts (apply to every registered `ExternImpl`):

- `D-REG-1`: One identifier maps to one registered implementation; the
  registry rejects a second registration under the same id.
- `D-REG-2`: The extern kind of the registered implementation agrees with
  the extern AST kind of the declaration sharing its id
  (`ExternImpl.val` / `.pfn` / `.fn` vs `externVal` / `externPfn` /
  `externFn`). Disagreement is a driver bug.

Pure-callable contracts (`ExternImpl.pfn`):

- `D-PFN-1`: The implementation receives `VarEnv`, argument `Value`, and
  `Memory` as read-only inputs. It does not return an updated environment
  or memory; pure externs do not allocate or mutate runtime state.

Impure-callable contracts (`ExternImpl.fn`):

- `D-FN-1`: The returned `(mem', addr')` pair is well-formed: `mem'` is
  well-formed with respect to `addr'`.
- `D-FN-2`: Address monotonicity: `addr ≤ addr'`, where `addr` is the
  `Config.nextAddr` observed by the call. This keeps any pre-existing
  `varEnv` well-formed with respect to the post-call `nextAddr`.

Reference-valued `extern ref` contracts (`ExternImpl.val (Value.loc a)` for
an `extern ref` declaration; a ref-typed `extern val` is rejected by the
typechecker):

- `D-REF-1`: The registered `Value.loc a` satisfies `a < Config.nextAddr`
  in the initial configuration. `Config.nextAddr` must be initialised
  above every driver-supplied address present in the initial memory.
- `D-REF-2`: `Config.memory` is populated at `a` with an integer before
  any evaluation that could dereference it.
- `D-REF-3`: The address `a` is stable across all evaluations of that
  declaration in a given run.
- `D-REF-4`: Distinct extern ids registered as reference-valued externs
  resolve to distinct addresses, so the registry never introduces
  aliasing. Sharing of an extern reference across multiple Poison names
  must be expressed through ordinary `let` binding, not by repeating the
  extern declaration — the typechecker enforces this (each extern id
  may be declared by `extern ref` at most once per program).

These contracts are the evidence interface the proof layer consumes.
`wfConfig` preservation for `ExternImpl.fn` consumes `D-FN-1` / `D-FN-2`
(the `fn` clauses of `ExternOperationalSafe`); well-formedness of
reference-valued externs consumes `D-REF-1` / `D-REF-2`
(`RegistryReservedBelow` / `RegistryReservedWF`). See the proof interface
section for where they feed in.

### Typing Baseline

The typing-side contract floor is `LeanProofs/ExternTypingAssumptions.lean`,
which exposes the `ExternTypingAssumptions` structure with a single field:

- `externPredSatDelta` — predicate-law preservation across one structural
  extern allocation batch.

Guard-origin provenance is derived structurally via
`applyFnTClosure_extern_ok_memEnv_guard_origin` in `ExternTagMeaning.lean`;
extern effect writes under poisoned `pc` erase predicates in the same style as
assignment.

The fault-robustness theorem is relative to a witness of
`ExternTypingAssumptions`: callers must supply (or postulate) one to
instantiate it.

Any new semantics-side evidence should compose with this baseline rather than
replace it wholesale.

### What Lives In Code, Not Here

The following are recorded directly in the implementation and are not
re-specified in this document:

- runtime representation of extern implementations
  (`LeanPoison/Runtime.lean`);
- registry API and duplicate-registration behaviour (`register`);
- `beval` dispatch structure (`LeanPoison/BigStep.lean`);
- shape-checking rules for arguments, simple returns, and nested returns
  (`valueMatchesTyp` and the application branches in `BigStep.lean`);
- error constructors and messages (`ExternError`);
- fuel accounting for extern dispatch;
- curried examples such as the built-in `max` externs (shared driver setup in
  `LeanPoison/ExternBuiltins.lean`, interpreter wiring in `Main.lean`, and the
  extern tests under `examples/`).

## Extern Read Dependencies (`captures:`)

Extern callable implementations receive a runtime environment and memory as well
as the explicit argument. The extern argument precondition describes only the
explicit argument, so a trusted clean result also needs a way to name environment
or memory entries that the implementation reads.

The motivating shape is curried `max`: the outer extern `@10` receives `a` and
returns an inner extern closure `@11`; the inner implementation computes
`max captured_a b`. The `@11` argument precondition can make `b` clean, but the
trusted call-boundary proof also needs a contract for the captured `a`:

```poison
extern pfn @10 a : (int :> clean {}) -> (
  extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})),
    captures: { a :> (int :> clean {}) })
```

The `captures:` clause is a list of read-dependency requirements. A bare target
such as `a` names a callable-environment entry. A bang target such as `!r` names
the current memory entry reached through a reference in the callable environment.
The callable environment is the closure's captured environment plus the explicit
argument binding, so a bang target may refer either to a captured reference or to
the explicit argument when the argument is reference-typed.

The clause is sibling syntax to `effects:` on extern callables. It is allowed on
top-level and nested `extern fn` / `extern pfn` declarations, and the list may be
empty. Empty `captures:` means the trusted result may depend on the explicit
argument and on registry-local implementation state that agrees across FR runs,
but not on ambient environment or memory entries.

Capture requirements use the same contract/ascription syntax as `effects:`:

```poison
captures: {
  a :> (int :> clean { 7, v => v >= 0 }),
  !r :> (int :> clean {})
}
```

The typechecker checks each declared dependency at the extern call boundary using
the same structural satisfaction relation as extern argument conditions:

```text
Qactual <:R Qdecl
```

The base type must match after erasure. A declared poisoned requirement accepts
clean or poisoned actuals; a declared clean requirement needs the actual to be
clean under the current regime. A declared `noPred` imposes no predicate
obligation; a declared predicate requires the actual to carry the same structural
predicate shape. There is no general logical implication.

The check is intentionally call-time. Extern arguments are checked when the
argument expression is evaluated, captured environment dependencies are checked
when the implementation reads the callable environment, and memory dependencies
are checked when the implementation is about to read memory. This gives guarded
values the right regime interpretation: if guard `7` is active at the call site,
`a` can be accepted as clean-under-regime; if it is inactive, the gate rejects
the trusted result even if the guard was active when the closure was created.

The trusted boundary still owns completeness of the dependency list. Runtime
closure environments and memory may contain entries not listed in `captures:`.
The proof obligation is that a clean result depends only on the explicit
argument, the listed read dependencies under their declared qualified types, and
declared memory effects. If an implementation reads an unlisted entry in a way
that can affect a clean result, that entry must be listed as a dependency or the
result must be typed poisoned/guarded accordingly.

Branch joins treat capture requirements as preconditions. They combine by
conjunction, not by return-side join, and they must not collapse distinct capture
predicate shapes to `noPred`. The implementation achieves this structurally:
closure members with different `captures:` contracts stay distinct, and applying
a merged closure gates every surviving member.

Current coverage:

- pfn-side environment captures are implemented and proved through the curried
  `max` artifacts (`builtinMax11CapturesSpec`,
  `MaxCurriedFR.appliedMaxCurried_FR`);
- guarded pfn captures are checked at the call boundary and proved at the
  trusted call boundary (`builtinMax11GuardedSpec`,
  `GuardedCapturesFR.guardedCaptures_FR`);
- representative memory-read `!r` captures are implemented/proved through `@23`
  (`builtinMemDerefSpec`, `MemReadCapturesFR.appliedMemReadCaptures_FR`);
- branch-join capture conjunction preservation is proved in
  `LeanProofs/CaptureJoinConjunction.lean`; and
- fn-side captures are operationally/typecheck-supported, with accepted/rejected
  examples. `@22`'s `effects:` post-state is proved
  (`builtinSetErrSpec` / `setErrWriteEffect_FR`); a trusted
  captures-bearing `fn` example should be revisited only if a shipped
  implementation actually reads captures.

## Proof Interface

The main FR proof obligation is discharged through a registry-aware theorem:
`TypeSystemEnforcesFaultRobustness` proves the trusted-registry-facing
`FaultRobustnessSpec tr ...`, requiring registry agreement
(`InitialContextTrusted` / `TrustedRegistryAgreesWithReachable`) per initial
context admitted by the input spec. `TypeSystemEnforcesFaultRobustness_allCtx`
is a compatibility corollary for callers that can supply universal agreement.
Declaration and call boundary evidence are the active extern-consumption path.

The operational-safety portion of the stack is already discharged through
`ExternBoundarySpec.operational`: `TrustedRegistry.operationalSafe` derives
`RegistryOperationalSafe`, which `SemanticsProperties.lean` consumes for
extern-aware preservation and monotonicity.

### Chosen Guarantee Interface

The proof consumes a `StepFR`-level evidence bundle:
`ExternBoundarySpec` stores declaration and call FR posts, single-run posts,
and an `operational : ExternOperationalSafe d impl` projection. This keeps the
core theorem generic over extern implementations while giving app/declaration
proof sites exactly the facts they need.

Concrete drivers should not expose this large interface directly in the long
term. For builtin validation, prove small behavior lemmas near the concrete
entries and assemble `ExternBoundarySpec` directly. Extract constructor lemmas
only once additional entries beyond `abs` and `max` demonstrate a repeated
shape.

### High-Level Direction

- Prefer evidence-passing over hard-wired global trust markers.
- Keep the executable runtime model and the proof interface distinct but
  compatible: semantics stays executable; proofs abstract over the
  properties executable externs must satisfy.
- Reuse explicit extern ids as the common indexing story for runtime
  dispatch, nested returned callables, and proof-facing evidence.
- Use reachable-domain trust over the initial typed configuration, not
  root-AST-only trust and not a global "all ids are trusted" assumption.
- Extern ids absent from `TrustedRegistry` are outside the proof-facing FR
  boundary in the current plan.
- The consumed proof-core interface is `StepFR`-shaped; driver-facing APIs
  should be finer-grained constructors over that core.

### Success Criteria

- `S-1`: The proof layer discharges concrete builtin boundary obligations using
  an id-indexed evidence interface that composes with
  `ExternTypingAssumptions.lean`; operational preservation and monotonicity flow
  through `ExternBoundarySpec.operational` and `RegistryOperationalSafe`.
- `S-2`: FR handles callable values returned by externs — including
  nested returned callables — without special-casing them outside the
  id-indexed story.
- `S-3`: The chosen interface can stand in for a separately verified
  Poison component, even though the separate-compilation pipeline itself
  is out of scope.
- `S-4`: The relationship between new semantics-side assumptions and the
  existing typing-side `ExternTypingAssumptions` fields is explicit: what is
  preserved, extended, or repackaged.
- `S-5`: The design is stress-tested against multiple examples, even if
  they are not all written out here.
- `S-6`: The example suite includes a shipped-registry instantiation:
  `defaultTrustedRegistry` projects to `defaultRegistry` from
  `LeanPoison/ExternBuiltins.lean`, so representative FR artifacts can be stated
  against the same registry that executable examples use.

### Affected Artefacts

Primarily on the proof side:

- `LeanProofs/ExternRuntime.lean` — extern boundary runs and the operational
  safety contracts.
- `LeanProofs/ExternBoundary.lean` — trusted registry, FR boundary contracts,
  reachable-domain trust, and the future constructor API.
- `LeanProofs/ExternProofs.lean` — concrete builtin trusted specs.
- `LeanProofs/AbsFR.lean`, `LeanProofs/MaxCurriedFR.lean`,
  `LeanProofs/MemReadCapturesFR.lean`, `LeanProofs/GuardedCapturesFR.lean`,
  and `LeanProofs/ExternRegimeInt.lean` — program-level validation artifacts.
- `LeanProofs/ExternTypingAssumptions.lean` — possible future localization of
  `externPredSatDelta` into per-extern evidence.
- `LeanProofs/SemanticsProperties.lean` — consumes `RegistryOperationalSafe`
  derived from trusted entries for extern-aware preservation and monotonicity.
- `LeanProofs/FaultRobustnessProofs.lean` and `LeanProofs/StepFRApp.lean` —
  existing consumers of populated-registry boundary evidence.
- `LeanProofs/StepFR.lean` — `StepFRPost` / `BoundaryTagMeaningPost`
  definitions consumed by boundary constructors.

Runtime-side artefacts (`LeanPoison/Syntax.lean`, `Runtime.lean`,
`BigStep.lean`, `Typecheck.lean`, `ExternBuiltins.lean`) are expected to remain
stable, though the proof work may surface small inconsistencies or annotations
worth tightening.

Specification artefacts (`poison-lang-spec/poison-lang.ott`,
`doc/poison-lang-description.tex`) already reflect the runtime baseline and the
current captures syntax. Further changes are expected only if later
trusted-builtin coverage changes the language surface.

## Open Questions

Current open questions:

- Are current extern annotations (`ExternReturn`, `Effect`, `Capture`,
  `SyntaxPredicate`) sufficient for FR, or is extra proof-only metadata
  unavoidable? (The branch-join capture conjunction case needed none — it is
  handled by the existing closure-member set-merge.)
- Beyond within-run determinism, what additional stability properties
  are needed for trusted externs?
- Should the current binary `TrustedRegistry` model remain the only proof
  boundary, or should future work introduce multiple trust levels?
- Is the proposed extern/evidence interface strong enough to model
  separate compilation, with FR proved once for a component and reused
  by a client program?
- What soundness theorem should connect executable semantics, typing,
  and FR? Is basic-shape execution enough for a minimal baseline? Do
  safe guarantees support a stronger theorem? Does FR itself imply the
  desired soundness property?
- Should the broad `ExternTypingAssumptions.externPredSatDelta` field remain
  global, or should constructor lemmas localize it into per-extern trusted
  entry evidence?
- How much of the concrete runtime should be reflected in proof-facing
  lemmas directly, and how much should stay hidden behind abstract
  evidence?
- What is the status of polymorphic or generic extern summaries, if any?

## Design Decisions / Constraints

- Research design for reasoning about externs in FR, not a production
  FFI design.
- Externs do not perform I/O.
- `beval` is a total pure Lean function; executable externs must
  therefore be computable Lean-level data supplied to evaluation.
- Extern identity is explicit and user-visible through mandatory `@id`
  syntax, including for nested returned callables.
- The registry is fixed for the duration of evaluation and supplied
  outside the object-language semantics.
- The executable design restricts extern inputs to first-order types;
  higher-order callback stories are deferred.
- `ExternTypingAssumptions.lean` is the known typing-side contract floor. Any
  semantics-side extension should connect to that baseline rather than
  replace it wholesale.
- Extern ids absent from `TrustedRegistry` are outside the proof-facing FR
  boundary in the current plan.
- The interface should be suitable for modelling separately verified
  Poison components, even though building the actual
  separate-compilation pipeline is out of scope.
- The Lean implementation (`LeanPoison/Runtime.lean`,
  `LeanPoison/BigStep.lean`) is authoritative for runtime mechanics;
  this document defers to it for operational detail.
