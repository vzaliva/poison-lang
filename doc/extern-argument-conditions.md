# Extern argument conditions

Status: **selected design, not implemented**. Extern callable arguments should
be extended from bare `Typ` to full `QTyp` so an extern declaration can state
the caller-side condition under which its trusted boundary proof applies.

## Summary

Current extern callable syntax only gives the argument a runtime type:

```poison
extern pfn @12 x : (int) -> ((int :> clean {}))
```

This says the extern takes an `int`, but it cannot say that the input must be
clean or must satisfy a predicate before the extern can honestly promise a clean
result.

The proposed extension is to allow `QTyp` in extern argument position:

```poison
extern pfn @N x : (int :> clean { 1, v => v >= 0 })
  -> ((int :> clean {}))
```

For a boundary proof that only needs ordinary clean input, the condition is:

```poison
extern pfn @N x : (int :> clean {})
  -> ((int :> clean {}))
```

## Meaning

The argument `QTyp` is the extern's precondition. A trusted extern proof covers
only call sites whose argument typing satisfies that qualified input type.

The return `QTyp` remains the extern's output contract. Return predicates are
latent de-poisoning markers on produced values; they are not used to encode what
the caller must prove before the call.

This split keeps the two obligations separate:

- argument `QTyp`: what the caller must establish for the trusted proof to apply;
- return `QTyp`: what the extern promises to produce under that condition.

## Argument-condition satisfaction

Use a conservative structural relation for the first implementation. At an
extern call, the inferred actual argument `QTyp` satisfies the declared extern
argument `QTyp` only when:

- the base/runtime types match;
- if the declared argument is clean, the actual argument is clean under the
  current regime;
- if the declared argument carries no predicate, no predicate match is required;
- if the declared argument carries a predicate, the actual argument must carry
  the same predicate shape after the usual extern tag-resolution/substitution
  machinery; do not attempt general logical implication between predicates.

This intentionally treats argument-condition checking as a syntax- and
regime-aware compatibility check, not theorem proving. It is acceptable for the
first version to reject calls that might be valid under a stronger logical
implication relation.

## Required changes

- Parser: change extern callable argument syntax from `paren_type` / bare `Typ`
  to `qtyp`.
- Core syntax: store the declared argument condition as `QTyp`, not only `Typ`,
  in extern function summaries.
- Typechecker: at an extern call, check that the actual argument's qualified type
  satisfies the declared argument `QTyp` before using the trusted extern result
  contract.
- Ott spec: update extern function forms and application rules so the argument
  condition is explicit in the typing premise.
- Proofs: make the trusted extern boundary proof quantify over calls whose
  argument and captured inputs satisfy the declared argument conditions.

## Implementation objectives

An implementation pass should cover all user-facing, executable, spec, and proof
surfaces affected by changing extern callable parameters from `Typ` to `QTyp`.
The expected objectives are:

- Accept and preserve qualified extern argument annotations in the parser,
  AST, pretty/debug output, and typechecker internals.
- Define the typechecker relation between an actual argument `QTyp` and the
  extern's declared argument-condition `QTyp` using the conservative structural
  relation above.
- Update extern application typing so a trusted clean result is available only
  when the declared argument condition is satisfied.
- Keep return `QTyp` semantics unchanged: return predicates remain output
  markers, not preconditions.
- Update executable examples and golden files. At minimum, add a `sqrt`-style
  positive example and a failing or conservatively-typed call whose argument does
  not meet the declared condition.
- Revisit existing `abs` and `max` examples and builtins. They should either use
  honest argument conditions, remain explicitly untrusted, or be rewritten so the
  examples no longer imply unconditional FR-clean output from dirty inputs.
- Update the Ott specification to match the new extern argument form and
  application typing premises.
- Update narrative documentation (`doc/poison-lang-description.tex`) so the
  surface language description explains extern argument conditions.
- Update proof-site definitions that currently treat extern callable input types
  as bare `Typ`, including trusted registry agreement, extern boundary runs, and
  FR boundary specs.
- Add or adapt proof lemmas for the new argument-condition satisfaction relation;
  the goal is to thread the declared argument `QTyp` through existing
  `agreeOnClean`, regime-consistency, and value-consistency obligations rather
  than invent a separate return-side precondition mechanism.
- Verify with `make test` for executable behavior and `lake build` for the Lean
  implementation and proof tree.

## Motivation

The `abs` declaration

```poison
extern pfn @12 x : (int) -> ((int :> clean {}))
```

is dishonest for fault-robustness: if the input is dirty, two runs may pass
different integers and get different clean outputs. A bare `Typ` argument gives
the declaration no place to state the needed caller-side condition.

Argument-side `QTyp` makes that condition part of the extern contract instead
of hiding it in the return type or in an external proof convention.
