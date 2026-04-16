# Poison FFI Proposal

Status: working draft.

Goal: give `extern val`, `extern fn`, and `extern pfn` intended runtime
semantics while keeping implementations outside Poison and making the
fault-robustness (FR) boundary explicit.

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
  questions, without choosing a concrete low-level representation.

## Glossary

- `extern`: a Poison declaration whose executable behaviour is supplied
  externally rather than by a Poison body.
- `registry`: the abstract mapping from extern identities to Lean-supplied
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

## Current Baseline

- Surface syntax already has `extern val`, `extern fn`, and `extern pfn`.
- The typechecker already interprets extern summaries through `ExternReturn`,
  `Effect`, and `SyntaxPredicate`, allocating fresh tags per use site.
- Application typing already computes the summary-level effect of applying an
  extern closure.
- The current evaluator does not execute externs; evaluating an extern
  expression currently fails with a runtime error.
- `beval` is a total pure Lean function. Any executable extern interface must
  therefore be supplied as computable Lean-level data/functions to evaluation,
  not only as an abstract proof-side relation. From the proof side, such
  implementations should still be used through explicit guarantees rather than
  by inspecting their code.
- Within a fixed supplied extern environment, operational behaviour is
  deterministic by construction.
- The current proof boundary lives in `LeanProofs/ExternAxioms.lean`. This is
  the typing-side baseline. At present it contains:
  - `externTagSoundness`, for fresh-tag soundness of summary-generated tags.
  - `externGuardProvenance`, for provenance of impure extern summaries in the
    FR development.
- Known current typing restrictions already relevant to the design include:
  - extern functions do not currently return references;
  - the current heap model constrains the shape of effect summaries.
- Typing restrictions should stay paired with any matching semantic obligations
  or proof evidence.

## Requirements

### Semantic Boundary

- `R-SEM-1`: Extern implementations remain outside Poison expressions; in the
  intended setting they are supplied by surrounding Lean code.
- `R-SEM-2`: Supplying extern implementations happens outside Poison
  evaluation; calling an extern during evaluation does not itself perform I/O.
- `R-SEM-3`: If callbacks are supported, they occur only through function
  values explicitly passed or obtained during execution, not by name lookup
  into the enclosing program. Any resulting recursion must be reflected in the
  fuel story.
- `R-SEM-4`: The proposal must state the first-class status of extern-provided
  callables and values, including capture, return, and storage.
- `R-SEM-5`: The proposal must decide how runtime/proof identity is assigned to
  externs, preferably without forcing user-visible names, and must account for
  unnamed and nested externs.

### Typing Summaries and Contracts

- `R-CON-1`: Extern summaries describe poisoned inputs, outputs, and effects at
  the typing/FR level; poison itself is not a runtime notion.
- `R-CON-2`: Runtime checking is intentionally shallow: it may check only basic
  shape, not full conformance with summaries or FR obligations.
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

- `R-RUN-1`: Registered externs must be executable in the intended semantics;
  absent registrations must produce documented runtime failure.
- `R-RUN-2`: The proposal must define an abstract registry role and lifecycle,
  including duplicate bindings, resolution time, and how the surrounding Lean
  driver supplies implementations.
- `R-RUN-3`: The proposal must define an abstract memory-access interface
  sufficient to talk about reads, writes, and effect summaries.
- `R-RUN-4`: The proposal must explain how extern calls interact with fuel and
  termination. Current working assumption: no divergence, and extern calls
  consume fixed nominal fuel unless callbacks force a more detailed account.
- `R-RUN-5`: The proposal must define a high-level error taxonomy covering at
  least missing implementation, basic-shape mismatch, and
  extern-implementation failure.

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
- `R-PRF-3`: The proposal must define how FR-facing evidence is supplied and
  indexed by extern identity, ideally through the same contract story used by
  typing.
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
  returned by externs, if such returns remain in scope.
- `R-PRF-9`: The proposal must examine what soundness property should connect
  executable extern semantics and typing, and whether safe guarantees support a
  stronger theorem than basic-shape execution alone.

## Success Criteria

- `S-1`: The proposal explicitly addresses callbacks, fuel, memory access,
  first-class status, naming/identity, and error taxonomy.
- `S-2`: The proposal makes clear what is handled by typing, what is handled by
  executable semantics, and what remains axiomatic or evidence-backed.
- `S-3`: The proposal explains how `ExternAxioms.lean` is preserved, extended,
  or repackaged.
- `S-4`: The proposal is stress-tested against multiple examples, even if they
  are not fully written out here.

## Affected Artefacts (Likely)

- `LeanPoison/`: `Syntax.lean`, `Runtime.lean`, `BigStep.lean`.
- Driver code such as `Main.lean`, which may supply executable extern
  behaviour.
- `LeanPoison/Typecheck.lean`, if the extern contract vocabulary changes.
- `LeanProofs/`: `ExternAxioms.lean`, `StepFR.lean`,
  `FaultRobustnessProofs.lean`, and downstream proof modules.
- `poison-lang-spec/poison-lang.ott` and `doc/poison-lang-description.tex`.
- Examples/tests for any eventual executable design.

## Part I: Runtime / Semantics

### Topics This Part Must Settle

- What it means for externs to have runtime semantics rather than immediate
  failure.
- The abstract memory interface for impure externs.
- Lookup and identity, especially for unnamed and nested externs.
- Registry lifecycle: when implementations exist and how missing/duplicate
  entries behave.
- Fuel and termination under the no-divergence working assumption, including
  callback-related recursion scenarios.
- Error classification.
- Whether extern callables behave like ordinary higher-order values in the
  current language.
- Callback/re-entrancy limits: only via function values already passed or
  obtained during execution.

### High-Level Direction

- Keep the runtime interface abstract and Lean-level, not an inter-language
  ABI.
- Preserve executability of the definitional interpreter.
- To reduce special cases, `extern val` may be treated internally as a pure
  immutable constant-function case.
- Keep loading/registration outside object-language semantics; in the research
  setting this can simply mean supplying an extern environment to evaluation.
- Treat memory access, fuel, and error taxonomy as part of the extern contract,
  not incidental implementation details.

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
- How callable values returned by externs, if permitted, are handled by FR.
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

### High-Level Direction

- Prefer an evidence-passing design over hard-wired global trust markers.
- Keep the executable runtime model and the proof interface distinct but
  compatible: semantics stays executable, proofs abstract over the properties
  executable externs must satisfy.
- It remains open whether the primary consumed interface should be
  `StepFR`-shaped or finer-grained.

## Open Questions

- Are current extern annotations (`ExternReturn`, `Effect`,
  `SyntaxPredicate`) sufficient for FR, or is extra proof-only metadata
  unavoidable?
- Is the extern registry fixed for the duration of evaluation, or may it vary?
- Beyond within-run determinism, what stability properties are needed for
  trusted externs?
- Are the current typing-side axioms already too strong for unsafe externs, or
  should unsafe externs sit entirely outside that baseline?
- Is the proposed extern/evidence interface strong enough to model separate
  compilation with FR proved once for a component and reused by a client
  program?
- How should duplicate registrations and extern-related diagnostics be handled?
- What is the status of polymorphic or generic extern summaries, if any?
- What soundness theorem should connect executable semantics, typing, and FR?
  Is basic-shape execution enough for a minimal baseline? Do safe guarantees
  support a stronger theorem? Does FR itself imply the desired soundness
  property?
- If new semantics assumptions are needed, should they live beside the current
  ones in `LeanProofs/ExternAxioms.lean` or in a separate module?
- Least-effort sequencing question: should the project first make externs
  executable and then prove against that runtime, or first design the proof
  boundary as if externs may execute later while the current interpreter still
  throws an exception?

## Design Decisions / Constraints

- This is a research design for reasoning about externs in FR, not a production
  FFI design.
- Externs do not perform I/O.
- `beval` is a total pure Lean function; executable externs, if added, must be
  computable Lean-level data/functions supplied to evaluation.
- The preferred surface story is to keep current externs lambda-like. If
  runtime/proof identity is needed, it should be generated internally rather
  than forced into user-visible syntax, including for unnamed and nested
  externs.
- If callbacks are supported, they are only through function values explicitly
  passed or obtained during execution; there is no by-name access back into the
  enclosing program.
- `extern val` may be treated internally as a pure immutable constant-function
  case; the main design focus is therefore on extern functions.
- The current `ExternAxioms.lean` axioms are the known typing-side contract
  floor. Any semantics-side extension should connect to that baseline rather
  than replace it wholesale.
- Unsafe externs are outside FR in the current plan.
- The interface should be suitable for modelling separately verified Poison
  components, even though building the actual separate-compilation pipeline is
  out of scope.

## Notes from the call on 2026-04-16

### Function descriptors

The earlier text already points towards a single extern identity being used for
both runtime lookup in the `registry` and proof-side lookup of FR `evidence`.
The main open question is how that identity is assigned for unnamed and nested
externs, not whether the source language must expose it directly. In line with
the earlier design constraints, prefer internally generated identity over a
user-visible `id` annotation on `extern`.

The executable side should receive only what evaluation needs: a Lean-supplied
value or callable, plus at most the basic-shape information used by shallow
runtime checks. FR-facing properties should stay on the proof side. The
declared summary (`ExternReturn`, `Effect`, `SyntaxPredicate`) remains the
typing/FR contract, while any extra trusted guarantees for `safe` externs are
supplied separately as evidence indexed by the same extern identity.

### Safe/unsafe distinction

Both `safe` and `unsafe` externs are intended to be executable. The split is
about what FR may assume, not about whether evaluation can call the extern at
all. In particular, only actually reached calls should matter to an FR theorem:
the mere presence of an unsafe declaration, or of an unsafe call in a known-dead
branch, should not by itself count against the program.

This leaves an open question about how the trust tier split interacts with the
current typing-side baseline:

1. Soundness/preservation: currently we effectively have one level of
   typechecking, namely `QTyp`; `EType` typing can be derived from it by
   erasing the extra information. If we move to two actual typecheckers,
   `EType` typechecking could always succeed, including for unsafe functions,
   while `QTyp` typechecking could fail with a typechecking error on unsafe
   calls.

2. Another approach is to keep a single level of typechecking, but, when
   typechecking an unsafe function, poison `pc`. Typechecking still passes, but
   the results are poisoned and FR does not hold, as intended. (favoured
   direction)

### FN/PFN extern distinction

One idea discussed on the call was that the `extern fn`/`extern pfn` split
might be derivable from annotations, and that the surface syntax could perhaps
be simplified accordingly. For user-defined functions, `pfn` does two jobs: it
restricts the body to `PExpr` and gives the resulting value `parrow` type.
Externs have no body, so only the second role remains. In the current surface
story, `extern pfn` is therefore the direct way to introduce an extern callable
that pure contexts, including predicates, may apply.

Simple argument against: with the current annotation language, this looks
infeasible, or at least premature. `Effect` summaries alone do not seem rich
enough to recover the full higher-order purity story, and the present typing
interface does not derive `parrow` from summaries by itself. In particular,
higher-order cases still need an explicit account of how function-valued
arguments and returned callables are classified. So the simplification is worth
recording as a possible future direction, but it should not be treated as a
consequence of the current annotations.


