# Poison FFI Proposal

Status: working draft.

Goal: give `extern val`, `extern fn`, and `extern pfn` intended runtime
semantics while keeping implementations outside Poison and making the
fault-robustness (FR) boundary explicit.

This is the top-level design document. It gives the high-level overview of
how FFI is handled in:

1. runtime / semantics;
2. proofs / reasoning.

The runtime part now has a more detailed sub-proposal in
`doc/ffi-runtime-design.md`. That document is authoritative for the concrete
runtime design and operational details. This top-level proposal should stay at
the level of capabilities, constraints, proof interfaces, and major design
choices.

## Scope

- This is a high-level design document for a research project.
- The term `FFI` is used loosely: the goal is not a production cross-language
  interface, but a model of an extern boundary rich enough to study what FR
  requires.
- In the intended experimental setting, executable extern behaviour may simply
  be supplied by surrounding Lean code, for example from `Main.lean` or a
  similar driver, and then passed into the semantics.
- The same interface may also help reason about separate-compilation-style
  reuse, where a separately verified Poison component is treated abstractly as
  an extern boundary; building the actual pipeline is out of scope.
- This document records required capabilities, proof interfaces, and open
  questions, without duplicating the operational detail now recorded in
  `doc/ffi-runtime-design.md`.

## Glossary

- `extern`: a Poison declaration whose executable behaviour is supplied
  externally rather than by a Poison body.
- `extern id`: the explicit `@id` attached to an extern declaration. This is
  now the language-level identity used by runtime dispatch, nested returned
  callables, and any future proof-facing evidence indexing.
- `registry`: the Lean-supplied mapping from extern identities to runtime
  values or callables.
- `basic shape`: the coarse runtime kind checked dynamically, for example
  integer, boolean, unit, string, location, or callable, as distinct from full
  summary conformance.
- `trust tier`: the proof-level status of an extern, such as `safe` or
  `unsafe`.
- `evidence`: an explicit proof object or theorem bundle supplying FR-facing
  guarantees for trusted externs.

## Non-goals

- Designing a production-grade interface to C, Rust, OCaml, or other external
  languages.
- Implementing a full separate-compilation, module, or linker pipeline for
  Poison components.
- Designing tooling details such as hot reloading, debugging, or deployment
  workflows.
- Repeating the detailed runtime rules that now live in
  `doc/ffi-runtime-design.md`.

## Current Baseline

- Surface syntax already has `extern val`, `extern fn`, and `extern pfn`.
- The runtime design now requires an explicit `@id` on every extern
  declaration, including nested callable return descriptors.
- The typechecker already interprets extern summaries through `ExternReturn`,
  `Effect`, and `SyntaxPredicate`, allocating fresh tags per use site.
- Application typing already computes the summary-level effect of applying an
  extern closure.
- The evaluator can now execute externs through a Lean-supplied registry rather
  than failing immediately on every extern occurrence.
- `beval` remains a total pure Lean function. Executable extern behaviour is
  still supplied as computable Lean-level data/functions, not as I/O or an
  abstract proof-only relation.
- Within a fixed supplied extern environment, operational behaviour is intended
  to be deterministic by construction.
- The current proof boundary lives in `LeanProofs/ExternAxioms.lean`. This is
  the typing-side baseline. At present it contains:
  - `externTagSoundness`, for fresh-tag soundness of summary-generated tags.
  - `externGuardProvenance`, for provenance of impure extern summaries in the
    FR development.
- The main currently relevant typing/runtime restrictions are now:
  - executable extern input types are restricted to the first-order surface
    types `{ int, bool, unit, string, ref int }`;
  - function-typed extern inputs are rejected;
  - extern functions do not currently return references;
  - the current heap model constrains the shape of effect summaries and the
    supported reference story.
- Typing restrictions should stay paired with any matching semantic obligations
  or proof evidence.

## Requirements

### Semantic Boundary

- `R-SEM-1`: Extern implementations remain outside Poison expressions; in the
  intended setting they are supplied by surrounding Lean code.
- `R-SEM-2`: Supplying extern implementations happens outside Poison
  evaluation; calling an extern during evaluation does not itself perform I/O.
- `R-SEM-3`: The current executable design does not support higher-order
  callbacks from externs back into arbitrary Poison callables. The current
  phase restricts executable extern inputs to first-order types, so any richer
  callback story is deferred.
- `R-SEM-4`: The proposal must state the first-class status of extern-provided
  callables and values, including capture, return, and storage.
- `R-SEM-5`: Runtime/proof identity is now explicit and user-visible through
  `@id`, including for nested returned callables.

### Typing Summaries and Contracts

- `R-CON-1`: Extern summaries describe poisoned inputs, outputs, and effects at
  the typing/FR level; poison itself is not a runtime notion.
- `R-CON-2`: Runtime checking is intentionally shallow: it checks declared
  identity/kind/basic shape and nested-return wrapper shape, not full
  conformance with summaries or FR obligations.
- `R-CON-3`: The proposal must decide whether the current annotation language
  is sufficient for FR or whether extra annotations or proof-only metadata are
  needed.
- `R-CON-4`: The proposal must say at what granularity guarantees are exposed:
  top-level theorem, `StepFR`-level interface, or finer-grained assumptions.
- `R-CON-5`: The proposal must decide how safe-extern guarantees are supplied:
  built-in axioms, explicit proof objects/evidence per extern, or another
  mechanism.
- `R-CON-6`: The proposal must clarify the relation between the current
  typing-side axioms and the safe/unsafe split.

### Runtime and Execution

- `R-RUN-1`: Registered externs are executable in the intended semantics;
  absent registrations produce documented runtime failure.
- `R-RUN-2`: The registry is a flat mapping from explicit extern ids to
  implementations, supplied by the surrounding Lean driver and fixed for the
  duration of evaluation.
- `R-RUN-3`: The runtime side must support the current memory-access needs of
  impure externs, while staying within the existing heap model.
- `R-RUN-4`: Extern calls participate in the evaluator's existing fuel story.
  The current runtime design treats each extern invocation as consuming one
  evaluator step; richer callback-related recursion is out of scope in the
  current phase.
- `R-RUN-5`: The runtime side must provide a documented error taxonomy covering
  at least missing implementation, kind mismatch, basic-shape mismatch,
  nested-return mismatch, and extern-implementation failure.
- `R-RUN-6`: Detailed runtime rules, driver obligations, and operational
  examples should live in `doc/ffi-runtime-design.md`, not be duplicated here.

### Typing Baseline and Specification Alignment

- `R-TYP-1`: The current typing-side extern floor is already known: it is based
  on `ExternReturn`, `Effect`, `SyntaxPredicate`, and the existing axioms in
  `ExternAxioms.lean`.
- `R-TYP-2`: If executable semantics introduces extra obligations, they should
  be documented together with the matching typing restrictions/evidence.
- `R-TYP-3`: A program may typecheck even if matching runtime registrations are
  absent.
- `R-TYP-4`: Any syntax, typing, or semantic change must be reflected in
  `poison-lang-spec/poison-lang.ott` and `doc/poison-lang-description.tex`.

### Proofs and FR

- `R-PRF-1`: Proofs must reason about externs through abstract contracts, not
  by inspecting Lean implementation code.
- `R-PRF-2`: The proposal must clarify how FR builds on the existing
  typing-side extern floor and what, if any, extra semantics-side assumptions
  are still needed.
- `R-PRF-3`: FR-facing evidence should be indexed by the same explicit extern
  identities used by runtime dispatch, including for nested returned callables.
- `R-PRF-4`: The proposal must relate any new extern evidence interface to the
  existing `LeanProofs/ExternAxioms.lean` baseline, including how executable
  behaviour is related to declared summaries.
- `R-PRF-5`: Externs are deterministic within a fixed supplied environment; the
  proposal must state whether any further stability assumptions are needed by
  FR.
- `R-PRF-6`: Unsafe externs are outside FR in the current plan.
- `R-PRF-7`: The proposal must assess whether the same extern/evidence
  interface is sufficient to model separately verified Poison components linked
  through an extern boundary.
- `R-PRF-8`: The proposal must state how FR should treat callable values
  returned by externs.
- `R-PRF-9`: The proposal must examine what soundness property should connect
  executable extern semantics and typing, and whether safe guarantees support a
  stronger theorem than basic-shape execution alone.

## Success Criteria

- `S-1`: The proposal explicitly addresses identity, registry lifecycle,
  memory-access needs, first-class extern callables, and error taxonomy.
- `S-2`: The proposal makes clear what is handled by typing, what is handled by
  executable semantics, and what remains axiomatic or evidence-backed.
- `S-3`: The proposal explains how `ExternAxioms.lean` is preserved, extended,
  or repackaged.
- `S-4`: The runtime overview here stays consistent with
  `doc/ffi-runtime-design.md` rather than re-specifying it independently.
- `S-5`: The proposal is stress-tested against multiple examples, even if they
  are not fully written out here.

## Affected Artefacts (Likely)

- `LeanPoison/`: `Syntax.lean`, `Runtime.lean`, `BigStep.lean`.
- Driver code such as `Main.lean`, which may supply executable extern
  behaviour.
- `LeanPoison/Typecheck.lean`, if the extern contract vocabulary changes.
- `LeanProofs/`: `ExternAxioms.lean`, `StepFR.lean`,
  `FaultRobustnessProofs.lean`, and downstream proof modules.
- `doc/ffi-runtime-design.md`, which carries the detailed runtime
  sub-proposal.
- `poison-lang-spec/poison-lang.ott` and `doc/poison-lang-description.tex`.
- Examples/tests for executable extern design.

## Part I: Runtime / Semantics

### Runtime Status

The runtime side is no longer just an open sketch. Its high-level shape is now
decided, and the concrete operational design is recorded in
`doc/ffi-runtime-design.md`.

This top-level proposal only needs the following runtime summary:

- extern identity is explicit through mandatory `@id` syntax;
- nested callable return descriptors carry their own ids as well;
- ids are globally unique across the whole program;
- runtime dispatch uses a flat registry keyed by extern id;
- the registry is supplied by the surrounding Lean driver and stored in
  `Config`;
- `extern val` dispatch returns a registered value after shallow shape
  checking;
- `extern fn` and `extern pfn` behave as ordinary Poison closures whose body is
  the corresponding extern AST node;
- nested callable returns are supplied directly by the implementation and
  validated against the declared nested return descriptor;
- runtime checking is deliberately shallow and does not re-check poison or FR
  obligations;
- executable extern input types are restricted to first-order surface types,
  which keeps callbacks out of scope in the current phase;
- the current reference story supports `extern val` at type `ref int`, with the
  detailed driver obligations spelled out in the runtime sub-proposal.

### What This Runtime Part No Longer Needs To Settle Here

The following are now delegated to `doc/ffi-runtime-design.md`:

- exact runtime representation of extern implementations;
- exact registry API and duplicate-registration behaviour;
- exact `beval` dispatch structure;
- shape-checking rules for arguments, simple returns, and nested returns;
- exact error constructors/messages;
- driver obligations for reference-typed extern values;
- detailed curried examples such as the built-in `max` externs;
- the precise fuel accounting for extern dispatch.

### High-Level Direction

- Keep the runtime interface abstract and Lean-level, not an inter-language
  ABI.
- Preserve executability of the definitional interpreter.
- Keep loading/registration outside object-language semantics; in the research
  setting this means supplying an extern registry to evaluation.
- Keep the runtime model shallow: execution checks kind/basic shape, while
  typing and proofs continue to carry poison-level meaning.
- Use the runtime sub-proposal for concrete operational choices, and keep this
  top-level document at the capability/interface level.

## Part II: Proofs / Reasoning

### Topics This Part Must Settle

- Which extern properties are needed only for execution, including what follows
  from basic-shape execution alone, and which are needed to prove FR.
- Whether current extern summaries are sufficient for FR or need extension or
  supplementation.
- What assumptions or evidence state that executable behaviour matches declared
  effect summaries. In the safe case this is trusted evidence, not something
  the runtime is expected to enforce.
- How trust tiers such as `safe` and `unsafe` are represented at the proof
  layer.
- How FR evidence is indexed by extern identity.
- How new semantics-side assumptions relate to the current typing-side
  assumptions in `ExternAxioms.lean`.
- How callable values returned by externs are handled by FR.
- Whether the same interface can stand in for a separately verified Poison
  component.
- What soundness relation should hold between executable extern semantics,
  typing, and FR.

### Guarantee Interface Options

The current `LeanProofs/ExternAxioms.lean` is the baseline for extern-related
assumptions in the proof development. Any new guarantee interface should be
compared against that baseline rather than designed in isolation.

1. Top-level theorem interface.
   The user supplies one theorem per trusted extern, close to the final FR
   statement.
   Pros: simple user story.
   Cons: coarse, hard to reuse locally, awkward for nested externs.

2. `StepFR`-level interface.
   The user supplies a lemma or evidence bundle matching the local proof
   obligations at extern call sites.
   Pros: matches the current proof decomposition.
   Cons: exposes some proof internals.

3. Fine-grained assumptions.
   The user supplies smaller obligations, such as tag soundness, effect
   provenance, or value/memory agreement, from which the required `StepFR`
   facts are derived.
   Pros: modular and close to the true semantic obligations.
   Cons: heavier user-facing API.

Options 1 and 2 may repackage or subsume parts of the current baseline. Option
3 most naturally extends `ExternAxioms.lean` with explicit semantics-side
assumptions.

### Pending Proof Obligations (Category B)

The following proof obligations in `LeanProofs/` currently stand as `sorry`
and genuinely need the extern evidence interface described above. They are
listed here so the proof work that introduces that interface can discharge
them together. All other extern-related `sorry`s in the proof development
concern top-level extern *declarations* (which leave `Config` unchanged) and
are mechanical to close without any extern guarantees.

- `LeanProofs/SemanticsProperties.lean` — the `app` case of the `wfConfig`
  preservation lemma. For the `ExternImpl.fn` dispatch path, the
  driver-supplied implementation returns an arbitrary `(mem', addr')` pair.
  Preserving `wfConfig` requires a registry contract stating at minimum:
  - `mem'` is well-formed with respect to `addr'`,
  - `addr₀ ≤ addr'` (address monotonicity so the pre-existing `varEnv`
    remains well-formed).
  The `ExternImpl.pfn` sub-case of the same `app` proof and the user-closure
  sub-case are provable without extern guarantees; only the `fn` sub-case is
  guarantee-dependent.
- `LeanProofs/SemanticsProperties.lean` — the `externVal` case of the
  `wfConfig` preservation lemma. `wfConfig cfg₁` is trivial (cfg unchanged),
  but `wfValue cfg₁.nextAddr v` for the `ref int` sub-case needs a registry
  contract that any registered `Value.loc a` satisfies `a < cfg.nextAddr`.
  `valueMatchesTyp` only enforces basic shape and accepts any `loc a`;
  numeric/boolean/unit/string sub-cases are provable without extern
  guarantees.
- `LeanProofs/FaultRobustnessProofs.lean` — `terminatesTo_extern_absurd`.
  Under the previous placeholder runtime every extern evaluation errored,
  which made this lemma vacuously true; with a live registry the lemma is
  statically false. Its six call sites — all inside the masked-single-run
  FR theorem — currently discharge the extern cases by `exfalso`. Each must be replaced with a real
  FR-at-extern-dispatch proof consuming extern-invocation evidence,
  specifically: when a registered extern with declared return qtype `qt`
  produces value `v`, `v` satisfies
  `valueConsistentWithRegime qt μ θ v` at the post-dispatch memory/map. This
  is the central FR obligation for trusted externs and is the natural fit
  for an id-indexed evidence bundle in either the Option-2 or Option-3
  interface above.

### High-Level Direction

- Prefer an evidence-passing design over hard-wired global trust markers.
- Keep the executable runtime model and the proof interface distinct but
  compatible: semantics stays executable, proofs abstract over the properties
  executable externs must satisfy.
- Reuse explicit extern ids as the common indexing story for runtime dispatch,
  nested returned callables, and proof-facing evidence.
- It remains open whether the primary consumed interface should be
  `StepFR`-shaped or finer-grained.

## Open Questions

- Are current extern annotations (`ExternReturn`, `Effect`,
  `SyntaxPredicate`) sufficient for FR, or is extra proof-only metadata
  unavoidable?
- Beyond within-run determinism, what additional stability properties are
  needed for trusted externs?
- Are the current typing-side axioms already too strong for unsafe externs, or
  should unsafe externs sit entirely outside that baseline?
- Is the proposed extern/evidence interface strong enough to model separate
  compilation with FR proved once for a component and reused by a client
  program?
- What soundness theorem should connect executable semantics, typing, and FR?
  Is basic-shape execution enough for a minimal baseline? Do safe guarantees
  support a stronger theorem? Does FR itself imply the desired soundness
  property?
- If new semantics assumptions are needed, should they live beside the current
  ones in `LeanProofs/ExternAxioms.lean` or in a separate module?
- How much of the runtime sub-proposal should be reflected in proof-facing
  lemmas directly, and how much should stay hidden behind abstract evidence?
- What is the status of polymorphic or generic extern summaries, if any?

## Design Decisions / Constraints

- This is a research design for reasoning about externs in FR, not a production
  FFI design.
- Externs do not perform I/O.
- `beval` is a total pure Lean function; executable externs must therefore be
  computable Lean-level data/functions supplied to evaluation.
- Extern identity is explicit and user-visible through mandatory `@id` syntax,
  including for nested returned callables.
- The registry is fixed for the duration of evaluation and supplied outside the
  object-language semantics.
- The current executable design restricts extern inputs to first-order types;
  richer callback stories are deferred.
- The current `ExternAxioms.lean` axioms are the known typing-side contract
  floor. Any semantics-side extension should connect to that baseline rather
  than replace it wholesale.
- Unsafe externs are outside FR in the current plan.
- The interface should be suitable for modelling separately verified Poison
  components, even though building the actual separate-compilation pipeline is
  out of scope.
- `doc/ffi-runtime-design.md` is the detailed runtime companion to this
  top-level proposal and should be treated as authoritative for runtime
  mechanics.
