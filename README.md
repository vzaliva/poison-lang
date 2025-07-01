# Poison Language

A simple imperative programming language with built-in fault tracking via a type
system that models data corruption as "poison" propagation.

## Overview

The Poison Language is designed to track faults modelled as "poison" throughout
program execution. The key feature is **de-poisoning** via predicates, allowing
selective recovery from faults based on runtime conditions. The language
provides a fail-safe-integrity guarantee: any fault propagates conservatively
through both data and control paths.

For detailed language features and syntax, see the formal documentation in `doc/poison-lang-description.tex` and the Ott specification in `poison-lang-spec/poison-lang.ott`.

## Building and Running

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html)
- LaTeX and latexmk (for building documentation)

### Build
```bash
lake build
```### Run Examples
```bash
# Run a specific file
lake exe poison-interpreter examples/arithmetic.poison

# Run with verbose output
lake exe poison-interpreter --verbose examples/basic-poison-flow1.poison

# Run tests
lake exe poison-tests

# Run tests with different modes
lake exe poison-tests --typecheck    # Type checking only
lake exe poison-tests --eval         # Evaluation only  
lake exe poison-tests --eval -v      # Evaluation only with verbose output
lake exe poison-tests # both evaluation and typchecking
```

## Project Structure

- `LeanPoison/` - Core language implementation
  - `Syntax.lean` - Abstract syntax definitions
  - `Eval.lean` - Executable semantics
  - `Parser.lean` - Syntax parser
  - `Runtime.lean` - Runtime environment
- `examples/` - Sample programs demonstrating language features
- `doc/` - Documentation
- `poison-lang-spec/` - Ott specification files
- `Main.lean` - Main interpreter entry point
- `Tests.lean` - Test suite

## Formal Specification

The language is formally specified using Ott in `poison-lang-spec/poison-lang.ott`. The complete formal definitions and documentation are available in `doc/poison-lang-description.tex`.

## Research Context

This language implements a novel approach to fault tracking that combines:
1. Region-parameterised reference types
2. Flow-sensitive typestate tracking
3. Predicate-based de-poisoning
4. Higher-order function support with captured typing context

The system provides a uniform type system for tracking faults through both data and control paths, even in the presence of aliasing and higher-order code.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.


