# AGENTS.md

This file provides guidance to AI agents when working with code in this repository.

## Project Overview

The Poison Language is a research implementation of a simple imperative programming language with built-in fault tracking via a type system that models data corruption as "poison" propagation. This Lean 4 project combines:

1. **Core implementation** (`LeanPoison/`) - operational semantics, type system, parser integration
2. **Formal proofs** (`LeanProofs/`) - type safety properties (preservation subsumed into fault-robustness, progress, fault-robustness, memory monotonicity)
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
- `TypeSafety.lean` - Typing contexts, realisation maps, value typing, runtime context instantiation
- `SemanticsProperties.lean` - Evaluation relations (terminatesTo, diverges, stuck), runtime configuration well-formedness

**Main properties:**
- `RegimeConsistency.lean` - Regime-consistency definitions (tag meaning, guard descriptors) plus the masked-regime / `tagEnvConsistentWithRegime*` machinery (definitions, insert/invalidate/join lemmas) shared by `StepFR` and downstream FR proofs
- `FaultRobustness.lean` - Top-level fault-robustness definitions (`FaultRobustnessSpec`, `agreeOnClean`, `agreeValueUnder`, etc.)
- `StepFR.lean` - Shared step-based machinery (`StepFR`, `StepFR_IH`, `resultAgreesIfClean`, `consistentRegimeSpec_implies_consistentWithRegime` bridge lemma, and helper lemmas for value/captured/closure consistency) used by every per-operator FR proof
- `JoinMemberTransport.lean` - Shared join-member transport machinery: lemmas about how `joinTypeResults` transports per-member properties (`valueConsistentWithRegime`, `agreeOnClean`, etyp signatures, member-of-arrow/parrow, ref membership, internal-poison) to the joined result. Imported by `StepFRApp` and `StepFRIte` so per-operator FR proof modules stay mutually independent
- **Per-expression case proofs** (each file contains the corresponding `stepFR_*` / masked single-run lemmas; shared imports from `StepFR`; `StepFRApp` and `StepFRIte` additionally import `JoinMemberTransport`):
  - `StepFRApp.lean` - function application
  - `StepFRAssign.lean` - assignment
  - `StepFRLiteral.lean`, `StepFRVar.lean`, `StepFROp.lean` - literals, variables, primitive operators
  - `StepFRFnPfn.lean` - `fn` / `pfn` forms
  - `StepFRIte.lean` - conditional
  - `StepFRDeref.lean`, `StepFRNewRef.lean` - memory operations
  - `StepFRSeq.lean` - sequencing
  - `StepFRVlet.lean` - `vlet`
- `FaultRobustnessProofs.lean` - Orchestration: imports all `StepFR*` case modules and proves the step theorem (`TypeSystemEnforcesFaultRobustness_step`), the implementation bridge (`TypeSystemEnforcesFaultRobustness_impl`), and the top-level statement (`TypeSystemEnforcesFaultRobustness`)
- `Progress.lean` - Progress (well-typed expressions evaluate or diverge, never get stuck)
- `MemoryMonotonicity.lean` - Memory monotonicity (evaluation only adds locations, never removes)

**Helper modules:** `Aux.lean`, `Equality.lean`, `VarEnvPreservation.lean`, `ExternAxioms.lean` (semantic contracts for extern typechecking used in fault-robustness)

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
- **Extern semantics**: Fault-robustness for extern-backed typing relies on the axioms in `ExternAxioms.lean`; keep that boundary minimal and consistent with `RegimeConsistency` / typechecking
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

- **Repository**: Project hosted on GitHub in private repository `vzaliva/poison-lang`
- **Read-only git operations**: You may use `git` commands to review commit history, compare branches, and inspect changes
- **No repository modifications**: Never execute commands that modify the repository (e.g., `git commit`, `git push`, `git merge`)
- **GitHub CLI**: You may use `gh` commands to view or create issues or sub-issues (e.g. `gh sub-issue add <parent-issue-url> <sub-issue-url-or-number>`) but be wary of shell backtick handling (you may want to use `--body-file` to avoid issues with them)
- **Approval required**: Always request user approval before creating or modifying GitHub issues
