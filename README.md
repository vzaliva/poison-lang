# Poison Language

A simple imperative programming language with built-in fault tracking via a
type system that models data corruption as "poison" propagation.

## Overview

The Poison Language tracks faults, modelled as "poison", throughout program
execution. Its key feature is **de-poisoning** via predicates, which allows
selective recovery from faults based on runtime conditions. The language
provides a fail-safe integrity guarantee: any fault propagates conservatively
through both data and control paths.

This repository contains:

- an interpreter and type checker for the language, written in Lean 4;
- a machine-checked Lean 4 proof that the type system enforces *fault
  robustness*, a refinement of non-interference;
- an Ott specification of the syntax, the typing rules and the big-step
  semantics;
- a tree-sitter grammar for `.poison` source files.

For the language features and syntax, see the language description in
[`doc/poison-lang-description.pdf`](doc/poison-lang-description.pdf) and the
Ott specification in
[`poison-lang-spec/poison-lang.pdf`](poison-lang-spec/poison-lang.pdf).

## Building and Running

### Prerequisites

- [Lean 4](https://lean-lang.org/install/), installed through `elan`. The
  toolchain version is pinned in `lean-toolchain` and is downloaded
  automatically.
- The [tree-sitter CLI](https://tree-sitter.github.io/tree-sitter/creating-parsers/1-getting-started.html),
  version 0.27 or later (tested with 0.27.2), and a C compiler (used by
  `tree-sitter build`).
- [Ott](https://github.com/ott-lang/ott), LaTeX and `latexmk`. These are
  needed only to regenerate the PDFs (`make poison-lang-spec`, `make doc`).
- GNU Make and Bash.

### Build

```bash
make             # everything: Ott spec, Lean code and proofs, parser, docs
make lean-build  # Lean only: interpreter, type checker and proofs
make parser      # tree-sitter parser only
```

The first build downloads a precompiled Mathlib cache. Building `LeanProofs`
checks every proof and takes a while.

### Run Examples

The interpreter needs the parser (`make parser`) and must be started from the
repository root: it finds the grammar through the `config.json` that `make`
generates there.

```bash
# Run a specific file
lake exe poison-interpreter examples/arithmetic.poison

# Run with verbose output
lake exe poison-interpreter --verbose examples/basic-poison-flow1.poison

# Run the REPL
lake exe poison-interpreter --repl

# Run the tests (typechecks and evaluates every examples/*.poison and
# compares with the expected output next to it)
make test
```

[`doc/poison-interpreter.md`](doc/poison-interpreter.md) documents all
options and exit codes.

### Regimes

Guarded extern values and functions are typechecked under a *regime*: an
assumption, per guard tag, that the tag's check holds (`true`) or fails
(`false`). The typechecker runs once per regime; two flags select one:

```bash
# Preferred: select an extern by its id (@238 in the source). Every output tag
# the typechecker allocates for that extern's applications is set to the value.
lake exe poison-interpreter --extern-regime "238=true" examples/extern_captures_guarded.poison

# Low-level: name a concrete guard tag. Tags are numbered from 1 in the
# typechecker's traversal order, so this depends on allocation order; use it
# for debugging, and for guards --extern-regime cannot reach, such as those of
# `extern val` declarations (tags fixed at the declaration).
lake exe poison-interpreter --regime "1=true" examples/vlet-shadow-guarded.poison
```

A test file can pin its flags in a first-line directive, which `make test`
passes to the interpreter:

```text
--! poison-interpreter --extern-regime "238=true"
```

## Proofs

The main result is the theorem `TypeSystemEnforcesFaultRobustness` in
`LeanProofs/FaultRobustnessProofs.lean`: a well-typed program satisfies the
fault-robustness specification defined in `LeanProofs/FaultRobustness.lean`,
relative to a registry of trusted extern functions. The specification takes
the extern typing assumptions packaged as `ExternTypingAssumptions`
(`LeanProofs/ExternTypingAssumptions.lean`) as a hypothesis. `lake build`
checks the whole development. It contains no `sorry`, and the main theorem
depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); `make axioms` prints them.

`LeanProofs/` also contains fault-robustness theorems for concrete programs
that use the shipped externs (`AbsFR.lean`, `MaxCurriedFR.lean`,
`MemReadCapturesFR.lean`, `GuardedCapturesFR.lean`, `ExternRegimeInt.lean`).

## Project Structure

- `LeanPoison/` - Language implementation: syntax, big-step semantics, type
  checker, parser front end
- `LeanProofs/` - Proofs of fault robustness and supporting properties
- `Main.lean` - Interpreter entry point
- `parser/` - tree-sitter grammar and parser packaging
- `examples/` - Sample programs with their expected output; they double as
  the test suite
- `poison-lang-spec/` - Ott specification of the syntax, the typing rules and
  the big-step semantics
- `doc/` - Language description (`poison-lang-description.tex`), the
  interpreter manual, and design notes on the extern (FFI) boundary
- `scripts/` - Test runner and maintenance scripts

## Research Context

This language implements an approach to fault tracking that combines:

1. Region-parameterised reference types
2. Flow-sensitive typestate tracking
3. Predicate-based de-poisoning
4. Higher-order function support with captured typing context

The system provides a uniform type system for tracking faults through both
data and control paths, even in the presence of aliasing and higher-order
code.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE)
file for details.

The XML parser in `LeanPoison/Xml/` is vendored from the Lean 4 core library
and remains under the Apache 2.0 license; see
[`LeanPoison/Xml/LICENSE`](LeanPoison/Xml/LICENSE).
