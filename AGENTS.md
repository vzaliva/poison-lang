# AGENTS.md

This file provides guidance to AI agents when working with code in this repository.

## Project Overview

The Poison Language is a research implementation of a simple imperative programming language with built-in fault tracking via a type system that models data corruption as "poison" propagation. This Lean 4 project combines:

1. **Core implementation** (`LeanPoison/`) - operational semantics, type system, parser integration
2. **Formal proofs** (`LeanProofs/`) - fault-robustness of the type system (which subsumes preservation) and its supporting properties; the progress property is stated but not proved
3. **Parser** (`parser/`) - tree-sitter grammar for `.poison` files
4. **Formal specification** (`poison-lang-spec/`) - Ott specification with LaTeX documentation

## General Coding Standards

- **Indentation**: Use spaces only, never tabs
- **Compilation**: Always leave code in compilable state at checkpoints (no build errors)
- **Warnings**: Avoid compilation warnings (except `sorry`-related warnings in proofs)
- **Unused binders**: Prefix unused variables and parameters with `_` so the tree stays warning-clean (warnings can fail CI or tests)
- **Build verification**: Run `lake build` to check compilation before committing
- **No parallel builds**: Do not run concurrent builds (including via parallel sub-agents) for files that share dependencies; `lake` builds all transitive dependencies, so concurrent builds of interdependent files will conflict and produce spurious errors
- **CLI tools**: fd (fdfind), ripgrep, jq, rename, shellcheck, sd, delta, gh, difftastic (`difft` on some installs), scc, yq, hyperfine, comby, tree-sitter, ast-grep, dtrx; fzf, bat (navigation/preview), just (task runner), entr, watchexec (rebuild on change), parallel (gnu parallel; independent per-file checks).

## Build Commands

```bash
# Initial setup and build
make                                   # Build everything: spec, docs, parser, Lean code
make lean-build                        # Build Lean libraries and executables
make lean-build-file FILE=LeanProofs/FaultRobustness.lean  # Build one module (path or dotted name, e.g. LeanProofs.FaultRobustness)
make axioms                            # Print the axioms the main theorems depend on (expect propext, Classical.choice, Quot.sound)

# Running interpreter
make run POISON=FILE.poison              # Run a .poison file
make run-verbose POISON=FILE.poison      # Run with verbose output

# Testing (applies to LeanPoison implementation only, not proofs)
make test                              # Build and run all tests
./scripts/run_tests.sh                 # Compare outputs against .output/.fail files
./scripts/update-tests.sh              # Regenerate .output/.fail from current interpreter

# Documentation and parser
make poison-lang-spec                  # Generate PDF from Ott specification
make doc                               # Build documentation pdf from tex files
make parser                            # Build tree-sitter parser

# Cleaning (WARNING: invalidates mathlib cache - avoid; ask user permission if it is absolutely necessary)
make clean                             # Clean build artifacts
# After cleaning, run: lake exe cache get

# Lean cache (mathlib); `lean-build` already depends on `cache`
make cache                             # Download precompiled caches if needed
make cache-refresh                     # Force fresh cache (use after toolchain/mathlib bumps)
```

## Architecture

### LeanPoison/ - Core Implementation

The executable language implementation. **Tests apply to this package.**

- `Syntax.lean` - AST definitions, types (Typ, QTyp), expressions (Expr), operators, values, runtime state (Config, Memory, VarEnv)
- `BigStep.lean` - Big-step operational semantics (`beval` with fuel-based evaluation)
- `Typecheck.lean` - Type checking with typing contexts (MemoryTypeEnv, TagEnv, TypeContext)
- `Parser.lean` - Tree-sitter parser integration, XML-to-AST conversion
- `Pretty.lean` - `Repr`/`Format` pretty-printing for values, configs, and related structures
- `Runtime.lean` - Runtime support functions
- `Misc.lean` - Utilities

**Key patterns:**
- Fuel-based evaluation (default 1000) ensures termination
- `EvalResult` has three cases: `success`, `outOfFuel`, `runtimeError`
- Type checker maintains `MemoryTypeEnv` (Γ), `TagEnv` (ℒ), and `TypeContext`

### LeanProofs/ - Formal Proofs

Formal correctness proofs establishing type safety and semantic properties. **No tests for this package.**

**Core definitions:**
- `Semantics.lean` - Low-level semantic definitions: `terminatesTo`, `stuck`, `wfValue`, `wfVarEnv`, `wfConfig`, `nextAddr_not_in_memory`. Foundational module imported by `ExternRuntime.lean` and `SemanticsProperties.lean`.
- `TypeSafety.lean` - Typing contexts, realisation maps, value typing, runtime context instantiation
- `SemanticsProperties.lean` - Structural inversion lemmas, `bevalApp_structure` / `BevalAppSuccess`, `nextAddr` monotonicity (`beval_nextAddr_mono`, `terminatesTo_nextAddr_mono`), and `wfConfig_preserved`. These three lemmas take `(hOp : RegistryOperationalSafe cfg₀.registry)` as a hypothesis discharged at the orchestration layer via `TrustedRegistry.operationalSafe`.

**Extern boundary stack (FFI trust):**
- `ExternRuntime.lean` - Runtime extern event predicates living below the FR proof stack: `ExternDeclaration`, `ExternDeclBoundaryRun`, `ExternCallEntry`, `ExternCallBoundaryRun`, `ExternBoundaryWFRun`, and the operational safety contracts `ExternOperationalSafe` (per trusted entry, per-kind shape) and `RegistryOperationalSafe` (per runtime registry, consumed by `SemanticsProperties.lean`).
- `ExternBoundary.lean` - Theorem-facing FR boundary contract layer (small, readable API): `BodyEntryInputsAgree`, `ExternBoundarySpec` (with `declFR`, `callFR`, `declSingle`, `callSingle`, `operational` fields), `TrustedExternEntry`, `TrustedRegistry` (with `toRuntimeRegistry`, `runtime_lookup_exists`, and the `operationalSafe` bridge proving `RegistryOperationalSafe` from `entry.spec.operational`), `TrustedRegistryAgreesWithReachable`, and reachability-domain inductives + navigation theorems.
- `ExternBoundaryProofs.lean` - Proof-heavy adapters and reachability integration theorems split off from `ExternBoundary.lean` (kept above it in the import graph). Resolution variants of `TrustedRegistryAgreesWithReachable`, captured-environment/QTyp reachability namespaces, and call-boundary integration. Consumers needing these proof bodies (e.g. `FaultRobustnessProofs.lean`, `StepFRApp.lean`) import this file in addition to `ExternBoundary.lean`.
- `ExternProofs.lean` - Concrete trusted entries for the shipped externs: the complete `ExternBoundarySpec`s (`builtinMax10Spec`, `builtinMax11CapturesSpec`, `builtinAbsSpec`, `builtinSetErrSpec`, `builtinErrnoSpec`, `builtinMemDerefSpec`, …), the generic `pfn` and `extern ref` declaration-boundary machinery, and the `set_err` program/registry agreement witness (`setErrProg`, `setErrRegistry`, `setErr_agreesWithProgram`). Everything lives in the `ExternProofs` namespace; implementations are shared definitionally with the interpreter via `LeanPoison/ExternBuiltins.lean`.
- `ExternRegimeInt.lean` - Extern-regime typechecking lemmas plus the program-level FR capstones that instantiate the top-level theorem at concrete trusted registries (`setErrWriteEffect_FR`, `errnoExternRef_FR`, `errnoScenario_FR`, all in the `ExternRegimeInt` namespace). Imports `FaultRobustnessProofs` and `ExternProofs`, so it sits above the whole general proof stack; only the per-builtin capstone modules below import it.
- `AbsFR.lean`, `MaxCurriedFR.lean`, `MemReadCapturesFR.lean`, `GuardedCapturesFR.lean` - Program-level FR capstones for the shipped builtins (`abs_FR`, `maxCurried_FR` / `appliedMaxCurried_FR`, `memReadCaptures_FR` / `appliedMemReadCaptures_FR`, `guardedCaptures_FR`): each places the builtin's `ExternBoundarySpec` in a concrete `TrustedRegistry` and instantiates the top-level theorem. Leaves of the import graph.
- `CaptureJoinConjunction.lean` - Branch-join behaviour of extern `captures:` contracts (`mergedParrow_apply_captures_conjunction`): merged closure members keep their captures verbatim, and applying the merged type requires every member's contract. Imports only `TypeSafety`; illustrative, not on the FR proof path.
- `ExternTypingAssumptions.lean` - Semantic contracts for extern typechecking (the typing-side contract floor) used in fault-robustness.

**Main properties:**
- `RegimeConsistency.lean` - Regime-consistency definitions (tag meaning, guard descriptors) plus the masked-regime / `tagEnvConsistentWithRegime*` machinery (definitions, insert/invalidate/join lemmas) shared by `StepFR` and downstream FR proofs
- `FaultRobustness.lean` - Top-level fault-robustness definitions (`FaultRobustnessSpecForCtx`, `FaultRobustnessSpecForRegistry`, `agreeOnClean`, `agreeValueUnder`, etc.)
- `StepFR.lean` - Shared step-based machinery (`StepFR`, `StepFR_IH`, `resultAgreesIfClean`, `consistentRegimeSpec_implies_consistentWithRegime` bridge lemma, and helper lemmas for value/captured/closure consistency) used by every per-operator FR proof. Its heavy IH-free clusters were factored out into the hub-split support modules below (`ExternTagMeaning`, `TypecheckInduction`); `StepFR` re-imports them.
- `ExternTagMeaning.lean` - extern-tagMeaning cluster factored out of `StepFR` (hub split): `resolveSyntaxPred`, `surfaceSpec`, `typecheckExternVal`, `applyFnTClosure_extern`, `applyExternEffect`, `forIn_effects`, and the captured-extern `QTypRespectsTagMeaning` origin lemmas. Sits below `StepFR`; imported by `StepFR` (re-export) and `TypecheckInduction.lean`.
- `TypecheckInduction.lean` - the heavy `typecheckExpr`-preservation structural inductions factored out of `StepFR` (hub split): `typecheckExpr_preserves_regimeConsistentWithCtx` (+ masked / `MaskedTagsAbsent` variants), `typecheck_preserves_predSatLaws`, the `*_byIH` closure-application bridges, and the clean lookup-origin cluster. Sits below `StepFR`; imports `ExternTagMeaning.lean`.
- `StepFRClosureApply.lean` - App-only closure-application machinery factored out of `StepFR` (hub split): the `applyFnTClosure` / `applyPFnTClosure` / `applyClosuresThreaded` structural family and their feeders. Imports `StepFR`; imported only by `StepFRApp.lean` and `ExternCallBoundarySides.lean`.
- `ExternCallBoundarySides.lean` - parametrized extern-call boundary-contract / Side family relocated out of `StepFRApp` (hub split): the `ExternCallBoundary{Fn,Pfn}StaticSource` provenance inductives + navigation theorems, the `ExternCallBoundarySingle{Fn,Pfn}Contract` single-run contracts (+ `of_emptyExternRegistry` / `of_trustedRegistry` / `of_trustedProgram` / `of_trustedReachable`), the `ExternCallBoundaryFR{Fn,Pfn}{Run,Side0,Side1}` contracts/providers, the `ExternCall{No,Impossible,Trusted}EntryKey` discriminators, and `TrustedRegistryAgreesWithProgramLocal`. These take the per-run results as hypotheses rather than referencing the application case proof (so the family is downward-closed). Sits below `StepFRApp` (which imports it; the `Single{Fn,Pfn}Contract`s are also consumed transitively by `FaultRobustnessProofs`).
- `JoinMemberTransport.lean` - Shared join-member transport machinery: lemmas about how `joinTypeResults` transports per-member properties (`valueConsistentWithRegime`, `agreeOnClean`, etyp signatures, member-of-arrow/parrow, ref membership, internal-poison) to the joined result. Imported by `StepFRApp` and `StepFRIte` so per-operator FR proof modules stay mutually independent
- **Per-expression case proofs** (each file contains the corresponding `stepFR_*` / masked single-run lemmas; shared imports from `StepFR`; `StepFRApp` and `StepFRIte` additionally import `JoinMemberTransport`; each per-operator lemma threads `(hOp : RegistryOperationalSafe registry)` to discharge `wfConfig_preserved` / `terminatesTo_nextAddr_mono` calls):
  - `StepFRApp.lean` - function application
  - `StepFRAssign.lean` - assignment
  - `StepFRLiteral.lean`, `StepFRVar.lean`, `StepFROp.lean` - literals, variables, primitive operators
  - `StepFRFnPfn.lean` - `fn` / `pfn` forms
  - `StepFRIte.lean` - conditional
  - `StepFRDeref.lean`, `StepFRNewRef.lean` - memory operations
  - `StepFRSeq.lean` - sequencing
  - `StepFRVlet.lean` - `vlet`
- `FaultRobustnessProofs.lean` - Orchestration: imports all `StepFR*` case modules and proves the step theorem (the private `TypeSystemEnforcesFaultRobustness_step_*` family), the bridge from the step theorem to the specification (`faultRobustnessSpec_of_step`), the per-context theorem `TypeSystemEnforcesFaultRobustness_at` with its all-context corollary `TypeSystemEnforcesFaultRobustness_allCtx`, and the top-level statement (`FaultRobustnessSpec`, `TypeSystemEnforcesFaultRobustness`). The public top-level theorem derives `RegistryOperationalSafe` internally via `TrustedRegistry.operationalSafe tr` — no separate public operational-safety hypothesis.
- `Progress.lean` - Statement of the progress property (well-typed expressions evaluate or diverge, never get stuck). Definition only; the repository contains no proof of it.
- `PredSatLawsWitness.lean` - Satisfiability witness for `PredSatLaws`: a tag meaning with a matchable guard (`v => v`), a satisfaction relation that meets both laws (`predSatLaws_idSat`), and a context in which `matchGuard` selects that guard. Imports `StepFRIte` for `matchGuard_ok_matched_owner`; a leaf of the import graph, not on the FR proof path.

**Helper modules:** `Auxiliary.lean`, `Equality.lean`, `VarEnvPreservation.lean`

**Dependency graph (extern boundary stack):**

```
Semantics → ExternRuntime → SemanticsProperties → StepFR → ExternBoundary → ExternBoundaryProofs
                                                                │                     ↓
                                                                │     FaultRobustnessProofs (orchestration)
                                                                ↓                     ↓
                                                          ExternProofs  →  ExternRegimeInt (program capstones)
                                                                                      ↓
                                              AbsFR, MaxCurriedFR, MemReadCapturesFR, GuardedCapturesFR
```

The split puts runtime extern event predicates and `RegistryOperationalSafe` *below* `StepFR` so `SemanticsProperties.lean` can consume them without an import cycle. FR-shaped contracts (`StepFRPost`-producing) live above `StepFR` in `ExternBoundary.lean`.

**Hub-split modules.** To decouple builds, `StepFR`'s heavy IH-free clusters and `StepFRApp`'s boundary-contract family were factored into dedicated modules without statement changes. Below `StepFR` (re-imported by it): `SemanticsProperties → ExternTagMeaning → TypecheckInduction → StepFR` (the extern-tagMeaning and `typecheckExpr`-preservation/lookup-origin clusters). Between `StepFR` and `StepFRApp`: `StepFR → StepFRClosureApply → ExternCallBoundarySides → StepFRApp` (closure-application machinery, then the parametrized Side / boundary-contract family). Editing any of these no longer rebuilds the other per-operator files.

**Module visibility / `private` discipline:** declarations used only within their declaring file are marked `private`. The `private` keyword scopes the binding to the file, which keeps the public surface of each module small and gives reviewers a quick read of "what is this module's API." When adding a new helper, default to `private` until another file actually needs it.

**Per-operator independence rule:** the `StepFR{App,Assign,Ite,Deref,NewRef,Seq,Vlet,Literal,Var,Op,FnPfn}.lean` files MUST NOT import each other. Any helper that two of them need belongs in a shared module (`StepFR.lean` for general step machinery, or `JoinMemberTransport.lean` for join-member transport). Because these files are mutually independent, edits to different per-operator files may be delegated to sub-agents in parallel — but run `lake build` sequentially afterwards (lake cannot build shared-dependency files concurrently).

### Other Components

- `Main.lean` - Interpreter entry point with CLI
- `parser/` - Tree-sitter grammar for `.poison` files
- `poison-lang-spec/` - Ott specification (`poison-lang.ott`)
- `examples/` - Test suite (`.poison` files with `.output` or `.fail` golden files)

## Specification and documentation

**Ott** (`poison-lang-spec/poison-lang.ott`): When syntax or typing rules change, keep **`doc/poison-lang-description.tex`** and **`examples/`** consistent (update tests and prose as needed).

**Narrative docs** (`doc/`): Describe the **current** language. Avoid changelog-style phrasing (for example, "we now support …").

**Markdown** (usually working notes under `doc/`): After editing, validate with `npx markdownlint-cli` (pass the file path or `doc/` as needed).

**Builds:** Use the targets in **Build Commands** above (`make poison-lang-spec`, `make doc`, `make parser`, etc.).

## Working with Implementation (LeanPoison/)

### Adding Language Features

When adding new expression types or operations:
1. Update `Syntax.lean` - add to `Expr` or `Op` inductive types
2. Update `BigStep.lean` - add evaluation case to `beval`
3. Update `Typecheck.lean` - add type checking rule
4. Update `poison-lang-spec/poison-lang.ott` - formal semantics
5. **Add test cases** in `examples/` with expected `.output` or `.fail` files
6. Run `make test` to verify correctness
7. Update proofs in `LeanProofs/` if needed

### Testing Implementation Changes

**Tests apply only to LeanPoison/, not LeanProofs/.**

The test suite (`scripts/run_tests.sh`) compares interpreter output against golden files:
- `.poison` + `.output` = expect successful execution with matching output
- `.poison` + `.fail` = expect non-zero exit code with matching error

To add a test:
1. Create `examples/testname.poison`
2. Run: `make run POISON=examples/testname.poison > examples/testname.output`
3. Review output, commit if correct

## Working with Proofs (LeanProofs/)

### Proof Development Guidelines

- **No testing**: Proofs are verified by compilation, not runtime tests
- **Extern semantics**: Fault-robustness for extern-backed typing relies on the `ExternTypingAssumptions` structure in `ExternTypingAssumptions.lean`; keep that boundary minimal and consistent with `RegimeConsistency` / typechecking
- **Conservative `sorry` use**: When you are proving deliberately, use `sorry` sparingly. The goal is to **decrease** the number of `sorry` statements (shrinking proof surface), not increase them. Adding more `sorry` goes in the wrong direction
- **Specification style**: Prefer **declarative / logical** specifications over functional encodings when both are reasonable (for example, membership predicates instead of `filter`-style definitions)
- **Inductive predicates**: For proof-relevant properties, prefer **inductive predicates** over `Bool` helpers so inversion is straightforward

Example (style preference):

```lean
-- Prefer: inductive predicate
inductive IsMember (x : α) : List α → Prop where
  | head : IsMember x (x :: _)
  | tail : IsMember x xs → IsMember x (_ :: xs)

-- Less convenient for proofs: functional encoding
def isMember (x : α) (xs : List α) : Bool :=
  xs.any (· = x)
```

- **Proof techniques**: Many proofs use structural induction on fuel or expression structure
- **Lean LSP tooling**: Use `lean-lsp` MCP tool to examine proof goals, errors, and search for lemmas
- **Bounded falsification check**: When a lemma looks suspicious, try 2–3 quick
  counterexample attempts before committing to a long proof. If you find a
  concrete counterexample, or a precise obstruction showing the statement cannot
  hold as written, stop and report it instead of forcing the proof.

## Lean 4 Workflows

`lean4` skills (`prove`, `autoprove`, `review`, `golf`, etc.) if available could be used.

### When Implementation Changes

When modifying type rules or evaluation in `LeanPoison/`:
1. Check that proofs in `LeanProofs/` still compile
2. Fix broken proofs if possible
3. Use `sorry` only if proof is complex and fixing it is not immediately feasible
4. Document any new `sorry` statements and plan to eliminate them

## Git and GitHub

- **Repository**: Project hosted on GitHub as `vzaliva/poison-lang`
- **Read-only git operations**: You may use `git` commands to review commit history, compare branches, and inspect changes
- **No repository modifications**: Never execute commands that modify the repository (e.g., `git commit`, `git push`, `git merge`)
- **GitHub CLI**: You may use `gh` commands to view or create issues or sub-issues (e.g. `gh sub-issue add <parent-issue-url> <sub-issue-url-or-number>`) but be wary of shell backtick handling (you may want to use `--body-file` to avoid issues with them)
- **Approval required**: Always request user approval before creating or modifying GitHub issues
