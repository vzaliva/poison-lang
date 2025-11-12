# Extern let placeholders – proposal

## Summary

Add let-bound `extern` placeholders for values, impure functions, and pure functions. These declarations live in the main source file and provide full typing information - including poison flags and guard predicates - for typechecking incomplete programs. They do not change the core typing rules and they have no runtime semantics: evaluating any `extern` expression causes a runtime error in the big-step interpreter.

## Motivation

Extern placeholders are useful for: library interfaces, system interfaces,
testing and verification, modular development, hardware abstraction.

## Current language background

Poison supports single-argument functions only:
- `fn x : ST1 => e : ST2` – impure functions with surface type annotations
- `pfn x : ST1 => pe : ST2` – pure functions with surface type annotations

Type annotations in the core language are surface types (`Typ`). Qualified types
(`QTyp`) - enriched with poison and predicate guards - live in the type system
and are not written on ordinary function types.

## Design overview

- **Externs are let-bound placeholders** for values and single-argument functions. They parse predicate bodies in-place and can mention in-scope names.
- **Typechecking only**: the algorithm consults extern specifications to synthesise types and apply effects. The Ott rules and judgements remain unchanged.
- **Big-step interpreter**: evaluating an extern expression raises a runtime error. Consequently, `let x = extern … in …` fails at runtime if control reaches that binding.
- **Effects**: impure extern functions can update any in-scope memory locations – the parameter or captured references – via an `effects:` block.
- **Guards**: symbolic guard placeholders allow correlating observables and effects. Placeholders are instantiated to fresh tags per call with well-defined scope.
- **No reference returns**: extern functions cannot return reference types. This restriction simplifies location tracking and proof obligations. Extern functions may return base types (int, bool, unit, string) and function types, but not `ref T`.

## Syntax

Externs are introduced with `let` and one of `extern val`, `extern fn`, or `extern pfn`.

### Extern value (any type)

With guard closure:
```poison
let x = extern val : (T :> poisoned|clean { guard gX, a => P(a, ...) })
```

With guard-only (no predicate body for syntactic matching):
```poison
let y = extern val : (T :> poisoned { guard gY })
```

### Extern impure function with effects

```poison
let f =
  extern fn a : (ST₁) -> (T₂ :> poisoned|clean { guard gR, v => P₁(v, a, ...) })
    effects: {
      !a  :> (int :> poisoned|clean { guard gA,  u => P₃(u, a, ...) }),
      !r1 :> (int :> poisoned|clean { guard g1,  w => P₄(w, a, r1, ...) }),
      !r2 :> (int :> poisoned|clean { guard g2,  z => P₅(z, a, r2, ...) })
    }
```

### ~~Extern impure function returning a reference with effect on returned location~~ (DEPRECATED)

**Note**: This pattern is no longer supported. Extern functions cannot return reference types due to location tracking complexity. See issue #72 for details.

~~```poison
let allocAndInit =
  extern fn n : (int) -> (ref int :> clean { no_pred })
    effects: {
      return :> (int :> poisoned { guard g, v => (v >= 0 && v <= n) })
    }
```~~

### Extern pure function (no effects)

```poison
let g =
  extern pfn a : (ST₁) -> (T₂ :> poisoned|clean { guard gR, v => P(v, a, ...) })
```

Notes:
- `!name` may refer to any in-scope variable of reference type: the argument `a` or captured references such as `r1`, `r2`.
- ~~`return` (without `!` prefix) is a special effect target that refers to the memory location of the returned reference. It is only valid when the return type is `ref T`, and the effect spec describes the contents at that location.~~ **DEPRECATED**: Extern functions cannot return references.
- Placeholders like `gR`, `g1` are symbolic. Reusing a placeholder name correlates the same guard across the observable return and any listed effects.
- Functions are single-argument and curried. Multi-argument interfaces are expressed by returning an extern function from an extern function.
- At present the runtime memory stores integers only, so all memory effects must have type `int`. **Extern functions cannot return `ref T` types.**

### Clarifying note: externs are expressions, not type declarations

Extern forms are term-level expressions. The parenthesised `(T :> p { P })` after `->` specifies the observable qualified result of executing the extern closure; it is not a type definition. Likewise, the `effects:` block is a term-level specification of how Γ is updated at application time.

When using nesting to model multiple arguments, the inner `extern fn … -> ( … )` is a value (a closure specification) produced by applying the outer extern. Its surface shape may look type-like because there is no body, but it denotes a value-level closure together with its observable-result and effects specification.

Example (value-level nesting; not a type):

```poison
extern pfn i : (int) -> (
  extern fn r : (ref int) -> (
    int :> poisoned { guard g, v => (v >= 0 && v <= i) }
  )
  effects: {
    !r   :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) }),
    !cap :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) })
  }
)
```

## Guard placeholders – scoping and instantiation

- Placeholders are names local to one extern binding. The same placeholder name may appear in the observable return and in multiple effects to express correlation.
- A single placeholder denotes one predicate, which may be either:
  - A **guard closure** (`guard k pred_closure (x, pe, r)`) when a predicate body is provided
  - A **guard-only** (`guard k`) when no predicate body is provided (just `guard gX` without the lambda)
- All occurrences with the same placeholder must use an identical predicate body (up to renaming of the formal argument) if a body is provided; otherwise the specification is ill-formed and should be rejected by the checker.
- Guard-only predicates cannot be matched syntactically via `match_guard` but can be de-poisoned when the guard tag is known to be true in the logical environment.
- Instantiation happens at first application of the outermost extern function. Each distinct placeholder is assigned a fresh tag, and the mapping is reused for all nested externs produced by that application.
- For extern values, placeholders are instantiated at the let-binding typing time.

## Typing behaviour (algorithmic – no Ott changes)

We keep the core rules intact and adapt the implementation to recognise extern nodes.

- **Let-bound extern value**: synthesise its declared `QTyp` and bind in `σ`. If the value is a reference, no side effects occur at binding time in v1.

- **Let-bound extern functions**: synthesise an arrow type `ST₁ -> ST₂` carrying an extern closure with the captured variable typing environment at the definition site. The closure’s poison at definition is the ambient pc, as with ordinary `fn`/`pfn`.

- **Application of extern fn**:
  1. Typecheck the argument `e₂` and require `ST <: T_arg`.
  2. Form the unified environment `σ′` by extending the captured environment with the parameter bound to `e₂`’s qualified type, joining poison with the current pc.
  3. Instantiate guard placeholders: allocate fresh tags for each distinct placeholder name occurring in the extern spec on first application and reuse the mapping for this call chain (including nested externs returned by the function).
  4. For every effect `!v :> QT_eff`, resolve `v` in `σ′` to `ref T_v @ l` and update `Γ(l)` to `QT_eff`, joining poison with the current pc and substituting placeholders with allocated tags.
  5. Return the declared observable return `QTyp` with poison joined with the current pc and with the same placeholder substitutions.
  6. In pure context, reject application of impure externs.

- **Application of extern pfn**: as above but without effects and in pure context.

## Big-step runtime behaviour

Extern nodes have no evaluation semantics. The interpreter reports a clear error when evaluation encounters them. Consequently, programs that reach an extern binding at runtime will abort even if the bound name is not used subsequently.

Illustrative behaviour in the big-step interpreter:

```lean
-- In LeanPoison/BigStep.lean
| Expr.externVal _ =>
  return .error "Cannot execute extern value – no implementation provided"
| Expr.extern _    =>
  return .error "Cannot execute extern function – no implementation provided"
```

## Examples

### Extern observable (non-function)

```poison
let system_ok = extern val : (bool :> clean { no_pred })
```

### Extern impure function affecting argument and a captured reference

```poison
let global_counter : ref int = ref 0 in
let incrementAndRead =
  extern fn _ : (unit) -> (int :> clean { no_pred })
    effects: { !global_counter :> (int :> clean { no_pred }) } in
...
```

### Correlated guard between observable return and argument’s location

```poison
let readSensor =
  extern fn s : (ref int) -> (int :> poisoned { guard g, v => (v >= 0 && v <= 255) })
    effects: { !s :> (int :> poisoned { guard g, u => (u >= 0 && u <= 255) }) }
```

### Higher-order, curried only

```poison
let applyTwice =
  extern fn f : ((int -> int)) -> ((int) -> (int :> clean { no_pred }))

let inc = fn x : int => x + 1 : int in
let result = (applyTwice inc) 5
```

### Multi-argument via nesting with shared guard placeholders

```poison
let cap : ref int = ref 0 in

let h =
  extern fn i : (int) -> (
    extern fn r : (ref int) -> (
      int :> poisoned { guard g, v => (v >= 0 && v <= i) }  -- inner observable shares g and depends on outer int
    )
    effects: {
      !r   :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) }),  -- effect on second arg shares g
      !cap :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) })   -- effect on captured ref shares g
    }
  )
```

On the first application `h 10`, a fresh tag is chosen for `g` and attached to
both effects carried by the produced inner closure (on `!r` and `!cap`). On the
subsequent application `(h 10) r`, the same tag is reused for the inner
observable and its effects.

```poison
let r : ref int = ref 3 in
let _ = (h 10) r
```

## Technical specification and implementation notes

### Parser and syntax layer

Extend the parser to accept the extern value and function forms described above,
with named parameters, observable qualified return annotations, and an optional
`effects:` clause for impure externs. The concrete AST node shapes are an
implementation choice and are not specified here.

Grammar additions:
- `extern val : (T :> poisoned|clean { guard g, x => pred })` – with guard closure
- `extern val : (T :> poisoned|clean { guard g })` – with guard-only
- `extern val : (T :> poisoned|clean { no_pred })` – with no predicate
- `extern fn a : (ST₁) -> (RET)` where `RET` is either `(T₂ :> …)` or another `extern fn|pfn …`
- `extern pfn a : (ST₁) -> (RET)` with no `effects:` block
- `effects: { !name :> (T :> …), ... }` for impure externs

Note: In all extern forms, `(T :> p { P })` denotes an observable-result specification for an expression, not a new type declaration.

### Poison layer and closures

At typing time, represent extern functions as closures carrying their
specification rather than a body, so that application can apply effects and
return the declared observable type without re-typechecking a body. Reuse
existing `QTyp` and `TPred` (with fresh tag instantiation) and existing
closure/arrow types; the exact carrier structures are an implementation detail.
Update printing/equality only as needed by the implementation.

### Typechecker

Add support for:
- Checking extern values: convert predicate bodies into the internal pure-expression form, allocate fresh tags for placeholders, and synthesise the declared qualified type.
- Checking extern functions: produce an arrow type annotated with the ambient poison at definition time and record the extern specification together with the captured variable environment.

Application of extern functions:
- On first application, allocate a fresh tag for each distinct placeholder and cache the mapping so that nested applications reuse the same tags.
- Resolve each effect key `!name` to a reference location in the unified environment (captured env extended with the argument) and update the memory typing environment at that location with the declared result, joining poison with the current pc.
- Return the declared qualified type for the observable result, with placeholders substituted and poison joined with the current pc.
- Enforce the pure-context restriction for impure externs.

### Big-step interpreter

Add two cases that report an error on evaluation of extern value or extern
function expressions. No other runtime changes are required.

### Parser support

Extend the parser to accept the new forms, including:
- `extern val` with annotated qualified type
- `extern fn` / `extern pfn` with named parameter, annotated observable return, optional `effects:` block
- Nested externs in return position for curried multi-argument interfaces

## Test cases

All test programs that reference externs should typecheck but abort at runtime
if evaluation reaches an extern expression.

### Use in the existing test suite

Once extern functions are implemented, they can be used to test the dependency
invalidation mechanism described in GitHub issue #37. The invalidation examples
(`invalidation-example1.poison`, `invalidation-example2.poison`,
`invalidation-example3.poison`) can be enhanced with extern functions to create
predicates that depend on heap locations. For example,
`invalidation-example1.poison` could be enhanced with:

```poison
let a = ref 5 in
let r = extern val : (int :> poisoned { guard g, x => x > !a }) in
if r > !a then
  a := r + 1;
  r
else 
  5
```

This would allow testing whether the dependency tracking and invalidation mechanism
correctly handles predicates that read from heap locations.

### Basic functionality

```poison
-- extern-basic.poison
let simple = extern val : (int :> clean { no_pred })
let frand_ext =
  extern fn n : (int) -> (int :> poisoned { guard g, y => (y >= 0 && y <= n) })

let _ = simple in
let _ = frand_ext 100
```

### Guard-only (no syntactic matching)

```poison
-- extern-guard-only.poison
let sensor_value = extern val : (int :> poisoned { guard g })
-- Cannot syntactically match guard g, but can be de-poisoned if g becomes true in L
let result = sensor_value + 1  -- result is also poisoned with guard g
```

### Effects on argument and captured references

```poison  
-- extern-effects.poison
let x : ref int = ref 0 in
let y : ref int = ref 0 in

let modifyBoth =
  extern fn r : (ref int) -> (unit :> clean { no_pred })
    effects: {
      !r :> (int :> poisoned { guard g, _ => true }),
      !y :> (int :> clean { no_pred })
    } in

let _ = modifyBoth x in
!x  -- should be typed as poisoned
```

### Higher-order, curried

```poison
-- extern-hof.poison
let applyTwice =
  extern fn f : ((int -> int)) -> ((int) -> (int :> clean { no_pred }))

let inc = fn x : int => x + 1 : int in
let _ = (applyTwice inc) 5
```

### Nested extern with shared guard

```poison
-- extern-nested.poison
let cap : ref int = ref 0 in
let h =
  extern fn i : (int) -> (
    extern fn r : (ref int) -> (
      int :> poisoned { guard g, v => (v >= 0 && v <= i) }
    )
    effects: {
      !r   :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) }),
      !cap :> (int :> poisoned { guard g, u => (u >= 0 && u <= i) })
    }
  ) in
let r : ref int = ref 3 in
let _ = (h 10) r
```

### Error at runtime

```poison
-- extern-runtime-error.poison
let f = extern pfn x : (int) -> (int :> clean { no_pred }) in
let _ = f 42   -- typechecks; evaluating reaches extern and aborts
```

## Restrictions

### No reference returns

Extern functions **cannot return reference types** (`ref T`). This restriction is necessary because:

1. **Location tracking problem**: When an extern function returns a reference, the typechecker must determine which memory location that reference points to. For regular functions, locations are allocated during typechecking when `ref e` is evaluated, but extern functions have no body to analyze.

2. **Proof complexity**: The `returnSpecToQTyp` function would need to allocate fresh locations during application, but these locations would not be properly initialized in Γ, leading to unsound typing and difficult proof obligations.

3. **Workaround**: If an extern function needs to return a reference, the caller can allocate the reference and pass it as a parameter, with the extern function updating it via effects:

```poison
-- Instead of: extern fn n : (int) -> (ref int :> ...)
-- Use:
let r : ref int = ref 0 in
let init = extern fn n : (int) -> (unit :> ...)
    effects: { !r :> (int :> ...) } in
let _ = init 42 in
r  -- Use the reference
```

This restriction applies to both `extern fn` and `extern pfn`. It does **not** restrict:
- Extern functions accepting references as parameters
- Extern functions returning base types (int, bool, unit, string)
- Extern functions returning function types (including nested extern functions)

See issue #72 for technical details.

## Backwards compatibility

This feature is additive and does not change existing semantics:
- No changes to existing `fn`/`pfn` behaviour
- No changes to the core Ott rules – the extension is algorithmic in the implementation
- Parser additions do not conflict with existing syntax

## Implementation plan (Lean)

1) Syntax and parsing
- Add `Expr.externVal` and `Expr.extern` and the syntax-only specs in `Syntax.lean`.
- Extend the parser to accept the new forms and to build the syntax-only specs, keeping predicate bodies as `Expr`.

2) Poison layer
- Add extern closure variants and supporting specs in `Poison.lean` using `PExpr` for predicate bodies.
- Update `Repr`/`BEq` instances as needed.

3) Typechecker
- Implement `typecheckExternVal` and `typecheckExtern` to produce `QTyp`s and extern closures.
- Extend `typecheckApp` to handle extern closures, resolve effects, allocate and substitute guard tags, and propagate mappings to nested externs.
- Enforce the pure-context restriction for impure externs.

4) Big-step interpreter
- Add error cases for evaluating extern nodes.

5) Tests and examples
- Add the files sketched above. Ensure that all programs typecheck and abort at runtime when an extern is evaluated.


