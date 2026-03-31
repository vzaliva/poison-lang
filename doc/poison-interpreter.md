## NAME
poison-interpreter - typecheck and evaluate Poison programs

## SYNOPSIS
`poison-interpreter --repl`

`poison-interpreter [--verbose] [--regime "100=true,101=false"] <file>`

`poison-interpreter --help`

## DESCRIPTION
`poison-interpreter` parses a `.poison` file, typechecks it, and (if typechecking
passes) evaluates it with a pure interpreter. In verbose mode it prints the full
typing result. Extern placeholders may typecheck, but execution stops with a
runtime error if evaluation reaches one.

## OPTIONS
`--verbose`
Typecheck and evaluate with verbose output.

`--regime "k=true,..."`  
Seed the regime used for FR-aware typing. Each assignment maps a guard tag to a
truth value. Duplicate tags use last-one-wins.

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
