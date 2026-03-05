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
- **Build verification**: Run `lake build` to check compilation before committing
- **CLI tools**: You can use: fd (fdfind), ripgrep, jq, rename, shellcheck, sd, delta, gh, difft (difftastic), scc, yq, hyperfine, watchexec, comby, tree-sitter, ast-grep, dtrx; fzf, bat, just, entr, rga (ripgrep-all), parallel (gnu parallel). For Lean workflows: fzf+bat (file/symbol nav + preview), just (task runner), entr or watchexec (rebuild on change), rga (search PDFs/docs/specs), parallel (safe parallel checks across files).

## Build Commands

```bash
# Initial setup and build
make                                   # Build everything: spec, docs, parser, Lean code
make lean-build                        # Build Lean libraries and executables
make lean-build-file FILE=LeanProofs/FaultRobustness.lean  # Build a single Lean file

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

# Cleaning (WARNING: invalidates mathlib cache - avoid. ask user permssions if it is absolutely necessary)
make clean                             # Clean build artifacts
# After cleaning, run: lake exe cache get
```

## Architecture

### LeanPoison/ - Core Implementation

The executable language implementation. **Tests apply to this package.**

- `Syntax.lean` - AST definitions, types (Typ, QTyp), expressions (Expr), operators, values, runtime state (Config, Memory, VarEnv)
- `BigStep.lean` - Big-step operational semantics (`beval` with fuel-based evaluation)
- `Typecheck.lean` - Type checking with typing contexts (MemoryTypeEnv, TagEnv, TypeContext)
- `Parser.lean` - Tree-sitter parser integration, XML-to-AST conversion
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
- `RegimeConsistency.lean` - Regime-consistency definitions (tag meaning, guard descriptors) shared by fault-robustness
- `FaultRobustness*.lean` - Fault-robustness (poison tracking ensures conservative fault propagation)
- `Progress*.lean` - Progress (well-typed expressions evaluate or diverge, never get stuck)
- `MemoryMonotonicity.lean` - Memory monotonicity (evaluation only adds locations, never removes)

**Helper modules:** `Aux.lean`, `Equality.lean`, `VarEnvPreservation.lean`, `IOHelpers.lean`

### Other Components

- `Main.lean` - Interpreter entry point with CLI
- `parser/` - Tree-sitter grammar for `.poison` files
- `poison-lang-spec/` - Ott specification (`poison-lang.ott`)
- `examples/` - Test suite (`.poison` files with `.output` or `.fail` golden files)

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
- **Conservative `sorry` use**: Use `sorry` sparingly. The goal is to **decrease** the number of `sorry` statements (shrinking proof surface), not increase them. Adding more `sorry` goes in the wrong direction.
- **IO monad reasoning**: See `doc/IO_equality_approach.md` for guidelines on functions defined in IO monad (e.g., `beval`)
- **Proof techniques**: Many proofs use structural induction on fuel or expression structure
- **Lean LSP tooling**: Use `lean-lsp` MCP tool to examine proof goals, errors, and search for lemmas

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
