# Poison FFI: Runtime Baseline and Proof Roadmap

Status: working document. The runtime side is implemented and is treated here
as a baseline. The fault-robustness proof has a populated-registry theorem that
consumes trusted extern boundary evidence. Concrete trusted specs now exist for
`abs`, the curried-`max` pair, the explicit-argument memory-read extern `@23`,
and the first impure (`extern fn`) entry `@13` (`builtinImpureIdSpec`).
Read-dependency/captures support is implemented on `ffi`.

Goal: give `extern val`, `extern fn`, and `extern pfn` intended semantics
while keeping implementations outside Poison and making the fault-robustness
(FR) boundary explicit.

This document has two parts:

1. **Part I — Runtime baseline (implemented).** A short, factual summary of
   what the runtime already does, with the source of truth being the code in
   `LeanPoison/Runtime.lean`, `LeanPoison/BigStep.lean`, and (on the typing
   side) `LeanProofs/ExternTypingAssumptions.lean`. Detailed operational rules
   are not duplicated here.
2. **Part II — Proofs / reasoning.** The live design work: what evidence the
   proof layer needs about trusted externs, how it is indexed, and how it
   connects to the existing typing-side assumptions. This is also where the
   remaining concrete trusted-builtin coverage and any helper/API extraction are
   tracked.

Related documents:

- `doc/ffi-proposal.md` is the status hub and roadmap for the FFI branch stack.
- `doc/ffi-axioms.md` is the proof-boundary reference for
  `ExternBoundarySpec`, `TrustedRegistry`, and FR-facing extern evidence.
- `doc/extern-poison.md` is the source-language contract reference for argument
  preconditions, return/effect poison meaning, regimes, and trust triage.
- `doc/extern-env-deps.md` is the selected `captures:` design for extern read
  dependencies.
- `doc/poison-interpreter.md` documents executable CLI behavior and the default
  runtime extern registry.

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
- curried examples such as the built-in `max` externs (shared driver setup in
  `LeanPoison/ExternBuiltins.lean`, interpreter wiring in `Main.lean`, and the
  extern tests under `examples/`).

## Part II: Proofs / Reasoning

This is where the live work sits. The runtime baseline above is the input; the
output is a proof interface that lets FR see through trusted externs without
inspecting Lean implementation code.

Integration status:

- `ffi` carries the FFI effort, including the completed `captures:` design in
  `doc/extern-env-deps.md`.
- The trusted guarded-value producer plus applied program-FR routing is broader
  FFI/regime validation work, not part of the completed captures mechanism.

### Topics To Settle

- Whether current extern summaries (`ExternReturn`, `Effect`, `Capture`,
  `SyntaxPredicate`) are sufficient for FR, or whether extra proof-only metadata
  is needed.
- Which reusable constructor lemmas should be the driver-facing API for common
  extern shapes, and what small behavior facts each constructor should require.
- Whether the current binary `TrustedRegistry` model is the intended long-term
  proof boundary, or future work needs multiple trust levels.
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
`TypeSystemEnforcesFaultRobustness` proves the trusted-registry-facing
`FaultRobustnessSpec tr ...`, requiring registry agreement
(`InitialContextTrusted` / `TrustedRegistryAgreesWithReachable`) *per* initial
context admitted by the input spec rather than over all of them at once; the old
all-context form survives as `TypeSystemEnforcesFaultRobustness_allCtx`. The old
`terminatesTo_extern_absurd` path has been replaced by declaration and call
boundary consumption.

Completed concrete validation:

- `abs` (`@12`) has a complete `ExternBoundarySpec`.
- The curried-`max` pair has complete trusted specs for the relevant `@10` and
  capture-bearing `@11` declarations, plus program-level FR for both the bare
  declaration path and the applied `(m 7) 2` path.
- Guarded pfn captures are implemented at the typecheck gate, covered by active
  and inactive regime examples, and proved at the trusted call boundary via
  `builtinMax11Guarded_callFR` / `builtinMax11GuardedSpec`. The accompanying
  program-FR artifact is the bare-declaration registry-agreement shape; applied
  guarded-value routing remains later FFI/regime work because it needs a trusted
  producer extern that returns the guarded/de-poisoned value consumed by the
  capture.
- Memory-read `!r` dependencies are implemented/proved end-to-end for the
  representative explicit-reference-argument path: `@23` has a complete
  `ExternBoundarySpec`, accepted/rejected examples exercise the call gate, and
  `MemReadCapturesFR.appliedMemReadCaptures_FR` routes the applied `@23 (ref 3)`
  program through the trusted `callFR`.
- Branch-join capture conjunction merging is proved in
  `LeanProofs/CaptureJoinConjunction.lean`: branch capture contracts survive the
  closure-member merge, and applying a merged capture-bearing `parrow` requires
  every surviving capture gate.
- The first impure (`extern fn`) trusted spec is complete: `@13`
  (`ExternProofs.builtinImpureIdSpec`) proves all five `ExternBoundarySpec`
  fields, and `LeanProofs/FnExternFR.lean` routes `(extern fn @13 ...) 7`
  through the impure `callFR`.

The remaining work is:

- **Add a captures-bearing trusted `kind = .fn` spec.** `@13` closes the impure
  fn call-boundary milestone, but it has `captures = []` and `effects = []`. The
  fn side still needs proof coverage that exercises `captures:` read-dependency
  evidence under a trusted fn spec, mirroring the pfn
  `builtinMax11CapturesSpec` path.
- **Build a trusted guarded-value producer.** Applied guarded-value routing
  requires a trusted producer extern that returns the guarded/de-poisoned value
  consumed by the capturing extern.
- **Cover the rest of the default registry.** Prove trusted entries for the
  remaining builtins as needed: sqrt-style guarded input (`@19`), constant
  extern values (`@20`), initialized ref-valued extern values (`@21`), and
  errno-style impure updates (`@22`).
- **Helper extraction after repetition.** Directly proving
  `ExternBoundarySpec` assembles large `StepFRPost` and single-run
  conjunctions, but public constructors should be introduced only after repeated
  concrete proofs show a stable shape. Likely future helpers include shapes such
  as `pureUnaryCleanInt`, `constCleanInt`, `nestedPfn`, `refValInitialized`, and
  `impureCellUpdate`.

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

### Success Criteria (Part II)

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

### Affected Artefacts

Primarily on the proof side:

- `LeanProofs/ExternBoundary.lean` — trusted registry, extern boundary runs,
  reachable-domain trust, and the future constructor API.
- `LeanProofs/ExternProofs.lean` and `LeanProofs/MaxCurriedFR.lean` — concrete
  builtin trusted specs and program-level validation artifacts.
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

Open questions are now narrower:

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
