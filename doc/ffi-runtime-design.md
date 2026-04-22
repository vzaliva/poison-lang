# Poison FFI — Runtime Sub-Proposal

Status: working draft. Sub-proposal of `doc/ffi-proposal.md` covering
the runtime semantics of `extern val`, `extern fn`, and `extern pfn`.

This document mostly uses surface syntax, but when it needs to describe
the exact Lean AST shape it refers to the implementation datatype
`ExternReturn` for extern return descriptors. Its relevant constructors
are `ExternReturn.simple ...` for first-order returns,
`ExternReturn.nestedFn ...` for nested impure extern callables, and
`ExternReturn.nestedPfn ...` for nested pure extern callables.

## Identity

Every extern declaration carries a mandatory `Nat` identifier written
at the declaration site after `@`:

```
extern fn  @5 x : (int)  -> ((int :> poisoned { 1, v => v >= 0 }))
extern pfn @6 u : (unit) -> ((int :> clean {}))
extern val @7   : (int :> clean {})
```

Nested callable externs use the same `@id` syntax inside return
descriptors:

```
extern fn @10 n : (int) ->
  (extern pfn @11 x : (int) -> ((int :> clean {})))
```

The identifier is the runtime handle for extern lookup. It is
author-chosen, stable across runs, independent of elaboration order,
and separate from the argument name (`x`, `u` above).
The internal nested-return constructors `ExternReturn.nestedFn` /
`ExternReturn.nestedPfn` carry their own
identifier slots: every extern callable that may be applied at runtime,
including a callable returned by another extern, has its own global
identifier. There is no separate slot/path identity scheme.

## Identifier Reuse

Identifiers are globally unique across all extern declarations. Any
second occurrence of an identifier already used by some `extern val`,
`extern fn`, or `extern pfn` is an error.

The rule is reflected at two layers:

- **Program validation / typechecking** is the authoritative enforcer
  for source-level uniqueness. It collects extern occurrences in the
  program and rejects any duplicate identifier outright.
- **Runtime** dispatches by identifier and checks extern kind against
  the registered implementation.

At runtime there is a second, separate uniqueness check: the
implementation registry is keyed by extern id and rejects duplicate
registrations for the same id. During evaluation, runtime lookup then
performs only id/kind/shape checks for the reached extern. Full-AST
runtime verification against a canonical declaration for a given id is a
possible later extension, not part of this phase. This is separate from
the nested-return shape check below, which does not validate a general
function type; it only checks that a returned value is the expected
extern-closure wrapper whose embedded AST matches the nested descriptor
already present in the currently executing extern summary.

The rule preserves the invariant that one identifier maps to one
implementation. This keeps the registry and the typechecker simple and
keeps the source-level rule uniform across refs and callables.

## Runtime Values

Extern callables are represented as ordinary `Value.closure` /
`Value.peClosure` values whose wrapped body is the extern AST node
itself and whose captured environment is the runtime environment in
scope when that callable instance is created:

- `Expr.externFn  id _ _ _ _` evaluates to
  `Value.closure   argName (Expr.externFn  id ..) config.varEnv`.
- `Expr.externPfn id _ _ _`   evaluates to
  `Value.peClosure argName (Expr.externPfn id ..) config.varEnv`.
- `Expr.externVal id _ _ _`   evaluates directly to the `Value`
  registered under `id`, shape-checked against the declared `Typ`.

`argName` is the extern declaration's existing argument-name field
(`x` in `extern fn x : ...`). This mirrors ordinary closure creation:
externs may mention surrounding Poison variables in effect summaries
and nested-return summaries, so later calls must retain the producing
environment. Registry identity and dispatch depend only on the wrapped
extern AST node, not on the captured environment. "This value is an
extern callable" is therefore a derived predicate of the form
`v = Value.closure _ (Expr.externFn ..) env` (or the `peClosure`
analogue for some `env`).

Environment capture applies to `extern fn` and `extern pfn`. They
behave like ordinary closures in this respect: they may read captured
variables through their return and effect summaries, but they never
mutate the environment itself. `extern val` captures nothing; it is
looked up directly in the registry.

## Registry

```
inductive ExternImpl where
  | val : Value → ExternImpl
  | pfn : (VarEnv → Value → Memory →
             Except ExternError Value) → ExternImpl
  | fn  : (VarEnv → Value → Memory → Address →
             Except ExternError (Value × Memory × Address)) → ExternImpl

abbrev ExternId := Nat
abbrev ExternRegistry := Std.HashMap ExternId ExternImpl
```

The registry lives as an immutable field of `Config`. Threading it
explicitly as a separate `beval` argument would universally quantify
every proof-development lemma that mentions `beval` over it; the
existing `Config` threading is cheaper and the immutability invariant
is a trivial induction (`c.registry = c'.registry`).

The registry is flat: one global map from extern id to implementation.
There is no separate lookup mechanism for top-level and nested callable
externs. If an extern body mentions `@11`, runtime later looks up `11`
in this same map whether that body came from a top-level declaration or
from a nested return descriptor.

The registry is built once by the Lean driver (`Main.lean` or
equivalent) outside evaluation. The driver API is

```
def register (reg : ExternRegistry) (id : ExternId)
             (impl : ExternImpl)
    : Except String ExternRegistry
```

The driver supplies the identifier and the Lean impl. `register`
rejects a second registration under the same identifier.

Passing a function as an argument to an extern is forbidden:
typechecking rejects executable extern signatures with function-typed
input positions, and runtime dispatch independently raises
`ExternError.shapeMismatch` if such a call is reached. Under the
current heap model, the intended executable input types are the
first-order surface types `{ int, bool, unit, string, ref int }`.

Each extern invocation consumes one evaluator fuel unit before the
registered implementation is called; the implementation interface does
not receive or return fuel.

Impl signatures:

Here `Address` means the current concrete allocation cursor
`Config.nextAddr`. An impure extern may need it when allocating fresh
runtime cells in `Memory`, so `ExternImpl.fn` receives it and returns an
updated cursor. Pure externs do not allocate or update runtime memory,
so `ExternImpl.pfn` does not receive an `Address` argument.

- `ExternImpl.val v` — the stored `Value` is returned directly. For
  `ref int` this is a `Value.loc l` that the driver has already
  wired into `Config.memory`; see the reference-types section.
- `ExternImpl.pfn f` — receives the unified runtime environment of the
  call (captured env plus the current argument binding), the current
  argument as a `Value`, and the current `Memory`. The environment and
  memory are read-only inputs: pure impls may inspect them but do not
  return or mutate them. The result is a `Value`, which may itself be a
  nested extern closure.
- `ExternImpl.fn f` — as `pfn`, but it may return updated `Memory` and
  updated `nextAddr` along with the returned `Value`.

For nested return specs, the impl returns the nested callable value
directly rather than asking the evaluator to synthesize it. In the
intended design, that returned value is the corresponding extern
closure, carrying the nested id from the declared return summary and
whatever captured environment the impl chooses to preserve. The runtime
does not validate a returned callable against a general function type;
it only checks that the returned value has the expected extern-closure
shape and that the embedded extern AST matches the declared nested
summary.

Kind disagreement between the current extern AST constructor and the
registered impl — for instance, a `.val` impl registered under an
identifier that the program reaches through an `externFn` node — is a
driver bug caught at dispatch as `ExternError.kindMismatch`.

## Nested Return Instantiation

When an extern application's outermost return summary is nested, the
impl returns the nested callable value directly. Operationally:

1. Start from the extern closure's captured runtime environment.
2. Bind the current argument under the extern's argument name, yielding
   `unifiedEnv`.
3. Invoke the registered impl.
4. If the outermost return summary is nested, the impl returns the
   nested callable as a `Value.closure` / `Value.peClosure`.
5. The runtime performs this same structural extern-closure check
   against the declared nested summary.

For `ExternReturn.nestedFn innerId innerArg innerArgTyp innerRet innerEffects`,
the accepted shape is exactly:

`Value.closure innerArg (Expr.externFn innerId innerArgTyp innerRet innerEffects) env`

where `innerId` is the identifier carried by the nested return
descriptor. For `ExternReturn.nestedPfn innerId innerArg innerArgTyp innerRet`,
the accepted shape is exactly:

`Value.peClosure innerArg (Expr.externPfn innerId innerArgTyp innerRet) env`

with the corresponding nested identifier. Any other returned value is
rejected as `ExternError.nestedReturnMismatch`.

In the intended use, that returned value is the corresponding extern
closure, carrying the nested id declared in the return summary and an
environment derived from `unifiedEnv`. On later application, it goes
through the same runtime prologue and registry lookup as a top-level
extern value, keyed by its own nested identifier.

Later executability therefore comes from that nested identifier alone.
The closure does not carry any separate slot index, bundle reference,
or other auxiliary runtime tag.

## Shape Checking

A single helper `valueMatchesTyp : Value → Typ → Bool` maps value
constructors to `Typ` cases. It is applied:

- on call entry, to the argument against the declared input `Typ`;
- on call exit for simple returns, to the returned value against the
  declared output `Typ` from the currently-dispatched extern's
  outermost return descriptor;
- on `Expr.externVal` dispatch, to the stored value against the
  declared `Typ`.

`valueMatchesTyp` does not inspect predicates or effect summaries;
runtime `Value`s do not carry poison metadata anyway, since poison lives
only in the typing and proof layers. Nested returns are checked
separately by exact closure-shape validation as described above.

## Errors

```
inductive ExternError where
  | missing           (id : ExternId)
  | kindMismatch      (id : ExternId)
  | nestedReturnMismatch (id : ExternId)
  | shapeMismatch     (id : ExternId)
  | implFailure       (id : ExternId) (msg : String)
```

All cases surface through `EvalResult.runtimeError` with a formatted
message; no new top-level result case is added.

For nested return specs, the runtime relies on the impl to return the
corresponding nested callable value directly. Any violation of that
expectation surfaces as `ExternError.nestedReturnMismatch`.

## `beval` Dispatch

`Config` gains a `registry : ExternRegistry` field. Every dispatch of
an extern AST node runs the same prologue before any kind-specific
work:

1. Extract the identifier from the current AST node.
2. Look up the impl for the identifier; missing →
   `ExternError.missing`.
3. Compare the current AST node's extern kind against the
   registered impl variant tag; disagree → `ExternError.kindMismatch`.

After the prologue, the three extern placeholder branches in
`BigStep.lean` that currently return `runtimeError` are replaced:

- `Expr.externVal id _ _ _`: take the `Value` from
  `ExternImpl.val`, shape-check it against the declared `Typ`,
  return it. Like every extern dispatch, this consumes one evaluator
  fuel unit.
- `Expr.externFn id _ _ _ _`: yield
  `Value.closure argName (Expr.externFn id ..) config.varEnv`.
- `Expr.externPfn id _ _ _`: yield
  `Value.peClosure argName (Expr.externPfn id ..) config.varEnv`.

Application dispatch keeps its existing `Value.closure` /
`Value.peClosure` branches. Inside each branch, the wrapped body is
inspected one level further: when the body's head constructor is
`Expr.externFn` (respectively `Expr.externPfn`), the prologue above
runs on the wrapped AST, then `unifiedEnv := closureEnv[param := arg]`
is formed, the runtime checks the current argument against the declared
input `Typ`, and the raw `Value` is passed to the impl. Pure extern
impls receive `unifiedEnv`, the argument, and the current `Memory`;
impure extern impls additionally receive the current `nextAddr` (see
`ExternImpl` signatures above). Reaching this point has already
consumed one evaluator fuel unit, exactly like any other application
step. The returned `Value` is shape-checked against the declared
outermost `Typ`; when the return summary is nested, exact
closure-shape validation is applied instead of relying on
`valueMatchesTyp` alone. For impure externs, `Memory` and `nextAddr`
are updated from the impl result. For pure externs, the current
`Memory` and `nextAddr` are preserved. Otherwise the existing
user-closure path runs unchanged. The impure extern branch is rejected
in `pureMode` exactly as a user-defined `Value.closure` would be.

Extern implementations may still return nested extern closures when the
declared return summary is nested.

## Example: Curried `max`

This design still models a multi-argument extern by currying through a
nested callable return. A pure two-argument `max` can be written as:

```poison
let max =
  extern pfn @10 a : (int) -> (
    extern pfn @11 b : (int) -> ((int :> clean {}))
  )
in
(max 3) 5
```

The outer declaration `@10` is the first argument stage. Its nested
return summary says that applying `@10` yields another pure extern
callable `@11`, which consumes the second argument.

The driver registers one implementation per extern id:

```lean
def outerMax :
  VarEnv → Value → Memory →
  Except ExternError Value
| unifiedEnv, Value.num _a, _mem =>
    pure (Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int
        (ExternReturn.simple Typ.int false SyntaxPredicate.noPred))
      unifiedEnv)
| _, _, _ =>
    -- Defensive only: runtime shape checking rejects non-ints first.
    .error (.implFailure 10 "expected int argument")

def innerMax :
  VarEnv → Value → Memory →
  Except ExternError Value
| unifiedEnv, Value.num b, _mem =>
    match VarEnv.lookup unifiedEnv "a" with
    | some (Value.num a) => pure (Value.num (max a b))
    | _ => .error (.implFailure 11 "captured a missing or not an int")
| _, _, _ =>
    -- Defensive only: runtime shape checking rejects non-ints first.
    .error (.implFailure 11 "expected int argument")

reg : Except String ExternRegistry := do
  let reg0 : ExternRegistry := {}
  let reg1 ← register reg0 10 (.pfn outerMax)
  let reg2 ← register reg1 11 (.pfn innerMax)
  pure reg2
```

Operationally the run goes as follows:

1. Evaluating `extern pfn @10 ...` yields
   `Value.peClosure "a" (Expr.externPfn 10 ...) config.varEnv`.
2. Applying `max 3` dispatches to `@10`. The runtime forms
   `unifiedEnv := closureEnv["a" := Value.num 3]`, checks the argument
   against `int`, and calls `outerMax unifiedEnv (Value.num 3) currentMemory`.
3. `outerMax` returns
   `Value.peClosure "b" (Expr.externPfn 11 ...) unifiedEnv`.
   The runtime validates that this exactly matches the declared nested
   return summary for `@11`.
4. Applying the returned closure to `5` dispatches to `@11`. The
   runtime extends the captured environment to
   `updatedEnv := unifiedEnv["b" := Value.num 5]` and calls
   `innerMax updatedEnv (Value.num 5) currentMemory`.
5. `innerMax` reads the captured `"a"` from its environment, compares
   it with the current `"b"`, and returns `Value.num 5`.
6. The runtime shape-checks that simple return against the declared
   `int` result and finishes the evaluation.

The only higher-order feature in play is the returned nested extern
closure, which is exactly the mechanism used to encode a curried
multi-argument API.

Because the driver must construct the returned nested extern AST in
exact agreement with the declaration's nested return descriptor, a
small helper for building that closure from the declared descriptor may
be worthwhile in the implementation to reduce driver-side mismatch
errors.

## `extern val` and Reference Types

The current typechecker admits `extern val : T` for
`T ∈ { int, bool, unit, string, ref int }`. The `ref int` case is
the only one where runtime dispatch must cooperate with the driver.

Typechecking for `extern val @c : (ref int :> poisoned { k })`:

- Requires that `@c` be unique among all extern declarations in the
  program.
- Allocates a fresh typing-level location `l_c` in the memory-type
  environment and records the declared qualified type there, exactly as
  the current typechecker does for one `extern val` occurrence.
- Resolves symbolic tag indices (`k` above) through the existing
  `collectAndAllocExternTags` / `resolveSyntaxPred` path, producing
  fresh concrete tags from `nextTag`. This is unchanged by the FFI and
  remains use-site-local.

There is no identifier-driven logical-location sharing for `extern
val`. Each declaration site gets its own logical location. Sharing
must be expressed explicitly through ordinary Poison bindings rather
than by repeating the same extern identifier.

Driver obligations for a ref-typed `extern val`:

- Register `ExternImpl.val (Value.loc a)` where `a : Address` is a
  concrete address chosen by the driver.
- Populate `Config.memory` at `a` with an integer before any
  evaluation that could dereference it. A declaration that is only
  passed around without being dereferenced needs no pre-population
  before the first observation, but the cell must be live whenever
  a deref is reached.
- Keep the address stable across all evaluations of that declaration in
  one run.
- Use distinct addresses for distinct identifiers, so aliasing is
  never introduced by the registry.
- Initialize `Config.nextAddr` above every driver-supplied address
  present in the initial memory. Thereafter, all fresh allocation in
  Poison code and in impure extern calls goes through the threaded
  `nextAddr` discipline.

If a program wants two names for the same extern reference, it should
bind the extern value once and reuse the variable:

```
let r = extern val @7 : (ref int :> clean {}) in
let s = r in
...
```

Repeating `extern val @7` at two declaration sites is not the sharing
mechanism in this design; it is rejected.

## Affected Files

- `LeanPoison/Syntax.lean`: add the identifier field to the three
  extern `Expr` constructors and to `ExternReturn.nestedFn` /
  `ExternReturn.nestedPfn`; extend the existing extern `BEq` cases
  to account for the new field.
- `LeanPoison/Runtime.lean`: add `ExternImpl`, `ExternRegistry`,
  `ExternError`, `valueMatchesTyp`, and a `register` helper; add
  `registry` to `Config`.
- `LeanPoison/BigStep.lean`: replace the three placeholder branches,
  run the dispatch prologue (lookup and kind-compatibility) on every
  extern AST, extend `Expr.app` dispatch, capture env when building
  extern closures, pass first-order argument values directly to impls,
  and accept nested returned extern callables from impl results.
- `LeanPoison/Typecheck.lean`: enforce the identifier-reuse rule by
  collecting extern occurrences and rejecting any duplicate identifier
  outright; keep fresh logical-location allocation for each accepted
  `extern val` occurrence.
- `LeanPoison/Parser.lean` and `parser/`: accept the identifier
  after `@` at each extern declaration.
- `poison-lang-spec/poison-lang.ott`,
  `doc/poison-lang-description.tex`: reflect the new identifier slot,
  extern-as-closure evaluation, the `Config.registry` field, and the
  executable input-type restriction to `{ int, bool, unit, string,
  ref int }`.
- `examples/`: add tests for `extern val` of each admitted type,
  `extern fn` with memory effects, `extern pfn` in predicates,
  duplicate-identifier rejection across all extern kinds,
  and a curried multi-argument extern such as `max`.
