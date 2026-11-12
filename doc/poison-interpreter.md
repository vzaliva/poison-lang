# poison-interpreter

## NAME

poison-interpreter - typecheck and evaluate Poison programs

## SYNOPSIS

```text
poison-interpreter --repl
poison-interpreter [--verbose] [--regime "1=true"]
  [--extern-regime "238=true"] <file>
poison-interpreter --help
```

## DESCRIPTION

`poison-interpreter` parses a `.poison` file, typechecks it, and (if typechecking
passes) evaluates it with a pure interpreter. In verbose mode it prints the full
typing result. The interpreter starts with the built-in extern registry from
`LeanPoison/ExternBuiltins.lean`, so the documented builtins such as curried
`max`, `abs`, `sqrt`, `errno`, `set_err`, and `memDeref` can execute.
User-declared extern ids that are absent from the runtime registry still fail at
dispatch.

## OPTIONS

`--verbose`  
Typecheck and evaluate with verbose output.

`--regime "k=true,..."`  
Low-level, concrete-tag control. Each assignment maps a numeric guard tag `k`
directly to a truth value, and the map seeds the regime *before* typechecking
begins, so it reaches any guard tag. The typechecker allocates guard tags in
its own traversal order starting from `1` — not strictly textual source order
(an application, for instance, visits its argument before the function) — so
naming a tag here is **allocation-order dependent**: inserting an earlier guard
shifts every subsequent number and silently changes which guard `k` refers to.
Use this mainly for debugging; prefer `--extern-regime` for extern-produced
guards. Duplicate tags use last-one-wins.

`--extern-regime "id=true,..."`  
Id-keyed control, **preferred for extern-produced guards**. Selects externs by
their declared id; every return/effect output tag the typechecker freshly
allocates at a call of a selected `extern fn`/`pfn`, and the guard tag of a
selected `extern val` declaration, receives the chosen truth value. The flag
fixes, for one run, the assignment of values to extern tags that the typing
context carries. Because selection is by id rather than by tag number, it is
robust against allocation order and covers *all* of a callable's output tags
(one per call site). A tag that `--regime` already sets keeps that value. Tags
the policy leaves unset keep the conservative (uninterpreted) behavior.

`--repl`  
Start a REPL. It cannot be combined with `--verbose`, `--regime`,
`--extern-regime` or a file name.

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

Assert an extern-produced return guard by id (preferred):
`poison-interpreter --verbose --extern-regime "238=true" examples/extern-regime-open.poison`

Concrete-tag control (here tag `1` is the guard of an `extern val` declaration;
activating it rejects a later shadow):
`poison-interpreter --verbose --regime "1=true" examples/vlet-shadow-guarded.poison`

The same program two ways — id-keyed vs concrete tag. Both typecheck and run;
`--extern-regime` interprets *both* call sites' output tags (1 and 2), while
`--regime "1=true"` names only tag 1:
`poison-interpreter --verbose --extern-regime "12=true" examples/regime-vs-extern-regime.poison`
`poison-interpreter --verbose --regime "1=true" examples/regime-vs-extern-regime.poison`

## RELATED DOCUMENTS

- `doc/externs.md` lists the shipped built-in externs, their canonical
  declarations, and their trusted-boundary status.
