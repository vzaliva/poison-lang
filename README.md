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
-- tree-sitter 0.25.6

-- Tree sitter setup :
    - Detailed Instructions : https://tree-sitter.github.io/tree-sitter/creating-parsers/1-getting-started.html 
    - Usual Setup :  npm install -g tree-sitter-cli

    -- Run 'make' which should generate the parser that the language uses
    
    -- If there are some issues , navigate to parser/tree-sitter-poison and run npm-install 
       , also try 'tree-sitter init-config'  from parser/tree-sitter-poison 
       and then modify  '~/.config/tree-sitter/config.json' and add 
                  {
                    "parser-directories": ["Path to base poison directory/parser"]
                  }


### Build
```bash
lake build
```### Run Examples
```bash
# Run a specific file
lake exe poison-interpreter examples/arithmetic.poison

# Run with verbose output
lake exe poison-interpreter --verbose examples/basic-poison-flow1.poison

# Run repl
lake exe poison-interpreter --repl

# Run tests
make test ( Runs run_tests.sh)


## Project Structure

- `LeanPoison/` - Core language implementation
  - `Syntax.lean` - Abstract syntax definitions
  - `Eval.lean` - Executable semantics
  - `Parser.lean` - Syntax parser
  - `Runtime.lean` - Runtime environment
-  `parser/     - Contains grammar and packages to generate parser
- `examples/` - Sample programs demonstrating language features
- `doc/` - Documentation
- `poison-lang-spec/` - Ott specification files
- `Main.lean` - Main interpreter entry point
- `run_tests.sh - Currently runs programs in examples/

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


