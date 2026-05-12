# Poison FFI: Runtime Baseline and Proof Roadmap

Status: working document. The runtime side is implemented and is treated here
as a baseline. The fault-robustness proof now has a populated-registry theorem
that consumes trusted extern boundary evidence; remaining open work is proof
constructor/API work for concrete extern drivers and the operational
well-formedness projections.

Goal: give `extern val`, `extern fn`, and `extern pfn` intended semantics
while keeping implementations outside Poison and making the fault-robustness
(FR) boundary explicit.

This document has two parts:

1. **Part I — Runtime baseline (implemented).** A short, factual summary of
   what the runtime already does, with the source of truth being the code in
   `LeanPoison/Runtime.lean`, `LeanPoison/BigStep.lean`, and (on the typing
   side) `LeanProofs/ExternTypingAssumptions.lean`. Detailed operational rules are not
   duplicated here.
2. **Part II — Proofs / reasoning.** The live design work: what evidence the
   proof layer needs about trusted externs, how it is indexed, and how it
   connects to the existing typing-side axioms. This is where the remaining
   `sorry`s in `LeanProofs/` will be discharged.

## Scope

- Research design for reasoning about externs in FR, not a production
  cross-language FFI.
- "FFI" is used loosely: the goal is a model of an extern boundary rich
  enough to study what FR requires.
- Executable extern behaviour is supplied by surrounding Lean code (for
  example from `Main.lean`) and passed into the semantics as a registry.
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
- `trust tier`: the proof-level status of an extern, such as `safe` or
  `unsafe`.
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
  declarations; this is not enforced by the compiler, but `register`
  rejects duplicate id registrations at driver-setup time.
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
  therefore out of scope in the current phase.
- Each extern invocation consumes one evaluator step in the fuel story.
- `beval` remains a total pure Lean function; executable extern behaviour
  is computable Lean-level data, not I/O.
- Within a fixed registry, operational behaviour is deterministic by
  construction.

### Extern Callable Value Shape

The proof layer treats "this runtime value is an extern callable" as a
structural predicate on `Value`:

- An impure extern callable is exactly a value of the form
  `Value.closure argName (Expr.externFn id argTyp ret effects) env`.
- A pure extern callable is exactly a value of the form
  `Value.peClosure argName (Expr.externPfn id argTyp ret) env`.
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

Reference-typed `extern val` contracts (`ExternImpl.val (Value.loc a)` for
a declaration at type `ref int`):

- `D-REF-1`: The registered `Value.loc a` satisfies `a < Config.nextAddr`
  in the initial configuration. `Config.nextAddr` must be initialised
  above every driver-supplied address present in the initial memory.
- `D-REF-2`: `Config.memory` is populated at `a` with an integer before
  any evaluation that could dereference it.
- `D-REF-3`: The address `a` is stable across all evaluations of that
  declaration in a given run.
- `D-REF-4`: Distinct extern ids registered as ref-typed `extern val`
  resolve to distinct addresses, so the registry never introduces
  aliasing. Sharing of an extern reference across multiple Poison names
  must be expressed through ordinary `let` binding, not by repeating the
  extern declaration.

These contracts are the evidence interface the proof layer consumes. The
`wfConfig` preservation gap for `ExternImpl.fn` consumes `D-FN-1` /
`D-FN-2`; the `externVal` well-formedness gap for `ref int` consumes
`D-REF-1`. See Part II for where they feed in.

### Typing Baseline

The typing-side contract floor is `LeanProofs/ExternTypingAssumptions.lean`,
which exposes the `ExternTypingAssumptions` structure with a single field:

- `externPredSatDelta` — predicate-law preservation across one structural
  extern allocation batch.

A previous `guardProvenance` field was removed once the typechecker was
tightened to erase predicates on extern effect writes under poisoned `pc`
(mirroring assignment); the guard-origin trace is now structurally provable
via `applyFnTClosure_extern_ok_memEnv_guard_origin` in `StepFR.lean`.

The fault-robustness theorem is relative to a witness of
`ExternTypingAssumptions`: callers must supply (or postulate) one to
instantiate it.

Any new semantics-side evidence introduced by Part II must compose with
this baseline rather than replace it wholesale.

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
- curried examples such as the built-in `max` externs (driver setup in
  `Main.lean` and the extern tests under `examples/`).

## Part II: Proofs / Reasoning

This is where the live work sits. The runtime baseline above is the input;
the output is a proof interface that lets FR see through trusted externs
without inspecting Lean implementation code.

### Topics To Settle

- Whether current extern summaries (`ExternReturn`, `Effect`,
  `SyntaxPredicate`) are sufficient for FR, or whether extra
  proof-only metadata is needed.
- Which reusable constructor lemmas should be the driver-facing API for common
  extern shapes, and what small behavior facts each constructor should require.
- How trust tiers such as `safe` and `unsafe` are represented at the proof
  layer.
- How any new semantics-side assumptions relate to the existing
  typing-side `ExternTypingAssumptions` fields in
  `ExternTypingAssumptions.lean`.
- How much convenience API is needed to build finite trusted registries and
  discharge reachable-domain trust for programs using them.
- Whether the same interface can stand in for a separately verified Poison
  component linked through an extern boundary.
- What soundness relation should hold between executable extern
  semantics, typing, and FR.

### Proof Status And Remaining Obligations

The main FR proof obligation is discharged through a registry-aware theorem:
`TypeSystemEnforcesFaultRobustness` now proves
`FaultRobustnessSpec (TrustedRegistry.toRuntimeRegistry tr) ...`, assuming
`TrustedRegistryAgreesWithReachable` for every initial context admitted by the
input spec. The old
`terminatesTo_extern_absurd` path has been replaced by declaration and call
boundary consumption.

The remaining concrete proof obligations are:

- **Constructor API for trusted entries.** Directly proving
  `ExternBoundarySpec` for every extern would require assembling large
  `StepFRPost` and single-run conjunctions by hand. The next proof layer should
  provide constructors such as `ExternBoundarySpec.pureUnaryCleanInt`,
  `constCleanInt`, `nestedPfn`, `refValInitialized`, and `impureCellUpdate`.
- **`LeanProofs/SemanticsProperties.lean` — `app` case of the `wfConfig`
  preservation lemma.** For `ExternImpl.fn`, preservation should consume the
  `ExternBoundarySpec.wf` projection on `ExternCallBoundaryRun.fn`.
- **`LeanProofs/SemanticsProperties.lean` — `externVal` case of the
  `wfConfig` preservation lemma.** For `ref int`, preservation should consume
  the `ExternBoundarySpec.wf` projection on `ExternDeclBoundaryRun.val`.
- **End-to-end driver examples.** Once constructors exist, prove trusted
  entries for `abs`, then the curried `max` pair, then low-risk extern values
  and errno-style impure updates.

### Chosen Guarantee Interface

The proof consumes a `StepFR`-level evidence bundle:
`ExternBoundarySpec` stores declaration and call FR posts, single-run posts,
and an operational `wf` projection. This keeps the core theorem generic over
extern implementations while giving app/declaration proof sites exactly the
facts they need.

Concrete drivers should not expose this large interface directly. They should
prove small behavior lemmas that feed constructor lemmas, and those
constructors should assemble the `ExternBoundarySpec` fields. That constructor
layer is the main remaining API work.

### High-Level Direction

- Prefer evidence-passing over hard-wired global trust markers.
- Keep the executable runtime model and the proof interface distinct but
  compatible: semantics stays executable; proofs abstract over the
  properties executable externs must satisfy.
- Reuse explicit extern ids as the common indexing story for runtime
  dispatch, nested returned callables, and proof-facing evidence.
- Use reachable-domain trust over the initial typed configuration, not
  root-AST-only trust and not a global "all ids are trusted" assumption.
- Unsafe externs are outside FR in the current plan.
- The consumed proof-core interface is `StepFR`-shaped; driver-facing APIs
  should be finer-grained constructors over that core.

### Success Criteria (Part II)

- `S-1`: The proof layer discharges the remaining constructor and
  `wfConfig_preserved` obligations using an id-indexed evidence interface that
  composes with `ExternTypingAssumptions.lean`.
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

### Affected Artefacts

Primarily on the proof side:

- `LeanProofs/ExternBoundary.lean` — trusted registry, extern boundary runs,
  reachable-domain trust, and the future constructor API.
- `LeanProofs/ExternTypingAssumptions.lean` — possible future localization of
  `externPredSatDelta` into per-extern evidence.
- `LeanProofs/SemanticsProperties.lean` — `wfConfig` preservation for
  `app` (fn sub-case) and `externVal` (ref int sub-case).
- `LeanProofs/FaultRobustnessProofs.lean` and `LeanProofs/StepFRApp.lean` —
  existing consumers of populated-registry boundary evidence.
- `LeanProofs/StepFR.lean` — `StepFRPost` / `BoundaryTagMeaningPost`
  definitions consumed by boundary constructors.

Runtime-side artefacts (`LeanPoison/Syntax.lean`, `Runtime.lean`,
`BigStep.lean`, `Typecheck.lean`) are expected to remain stable, though
the proof work may surface small inconsistencies or annotations worth
tightening.

Specification artefacts (`poison-lang-spec/poison-lang.ott`,
`doc/poison-lang-description.tex`) already reflect the runtime baseline;
no further changes are anticipated solely for Part II unless new
proof-only annotations need a surface spec.

## Open Questions

All open questions are now on the proof side:

- Are current extern annotations (`ExternReturn`, `Effect`,
  `SyntaxPredicate`) sufficient for FR, or is extra proof-only metadata
  unavoidable?
- Beyond within-run determinism, what additional stability properties
  are needed for trusted externs?
- Are the current typing-side `ExternTypingAssumptions` fields already too
  strong for unsafe externs, or should unsafe externs sit entirely outside
  that baseline?
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
- Unsafe externs are outside FR in the current plan.
- The interface should be suitable for modelling separately verified
  Poison components, even though building the actual
  separate-compilation pipeline is out of scope.
- The Lean implementation (`LeanPoison/Runtime.lean`,
  `LeanPoison/BigStep.lean`) is authoritative for runtime mechanics;
  this document defers to it for operational detail.
