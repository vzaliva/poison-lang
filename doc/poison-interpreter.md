# poison-interpreter

## NAME

poison-interpreter - typecheck and evaluate Poison programs

## SYNOPSIS

```text
poison-interpreter --repl
poison-interpreter [--verbose] [--regime "100=true,101=false"]
  [--extern-regime "238=true"] <file>
poison-interpreter --help
```

## DESCRIPTION

`poison-interpreter` parses a `.poison` file, typechecks it, and (if typechecking
passes) evaluates it with a pure interpreter. In verbose mode it prints the full
typing result. The interpreter starts with the built-in extern registry from
`LeanPoison/ExternBuiltins.lean`, so the documented builtins such as curried
`max`, `abs`, `impure_id`, `sqrt`, `ZERO`, `errno`, `set_err`, and `memDeref`
can execute. User-declared extern ids that are absent from the runtime registry
still fail at dispatch.

## OPTIONS

`--verbose`
Typecheck and evaluate with verbose output.

`--regime "k=true,..."`  
Seed the regime used for FR-aware typing. Each assignment maps a guard tag to a
truth value. Duplicate tags use last-one-wins.

`--extern-regime "id=true,..."`
Seed the executable extern-regime policy by extern id. Every return/effect tag
generated for a selected extern id receives the selected truth value.

`--repl`
Start a REPL.

`--help`
Print usage.

## EXIT CODES

`0` Success (including successful detection of type errors)  
`1` Usage error  
`2` Parse error  
`3` AST construction error  
`4` Type checker out of fuel  
`5` File I/O error  
`6` Runtime error  
`7` Evaluation out of fuel

## EXAMPLES

Typecheck and run:
`poison-interpreter examples/arithmetic.poison`

Verbose mode:
`poison-interpreter --verbose examples/basic-poison-flow1.poison`

Typecheck with a regime:
`poison-interpreter --verbose --regime "100=true" examples/lp55xx-read.poison`

Typecheck with an extern-regime policy:
`poison-interpreter --verbose --extern-regime "238=true" examples/extern-regime-open.poison`

## RELATED DOCUMENTS

- `doc/ffi-proposal.md` gives the FFI branch roadmap and status.
- `doc/extern-poison.md` explains extern argument conditions, regimes, and
  trusted/untrusted extern contracts.
- `doc/extern-env-deps.md` explains `captures:` read dependencies for externs.
- `doc/ffi-axioms.md` explains the proof-facing trusted extern boundary.
