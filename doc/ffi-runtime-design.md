# Poison FFI — Runtime Sub-Proposal

Status: working draft. Sub-proposal of `doc/ffi-proposal.md` covering
the runtime semantics of `extern val`, `extern fn`, and `extern pfn`.

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

The identifier is the shared handle between the runtime registry and
proof-side evidence. It is author-chosen, stable across runs,
independent of elaboration order, and separate from the argument name
(`x`, `u` above). `ExternReturn.nestedFn` / `ExternReturn.nestedPfn`
carry their own identifier slots: every extern callable that may be
applied at runtime, including a callable returned by another extern,
has its own global identifier. The same identifier is later used for
runtime implementation lookup and for any optional FR-side guarantee
lookup. There is no separate slot/path identity scheme, and no theorem
or evidence object is stored inside runtime closure values.

## Identifier Reuse

Identifiers are globally unique across all extern declarations. Any
second occurrence of an identifier already used by some `extern val`,
`extern fn`, or `extern pfn` is a typechecking error, regardless of
kind or structural equality.

The rule is reflected at two layers:

- **Typechecker** is the authoritative enforcer. It collects extern
  occurrences and rejects any duplicate identifier outright.
- **Runtime** dispatches by identifier and checks extern kind against
  the registered implementation.

The current runtime proposal relies on typechecking plus the
global-unique-id discipline and performs only id/kind/shape checks.
Full-AST runtime verification against a canonical declaration is a
possible later extension, not part of this phase.

The rule preserves the invariant that one identifier maps to one
implementation and one set of proof-side evidence. This is stricter
than allowing structurally-equal declarations to share an id, but it
keeps the registry and the typechecker simple and avoids special reuse
rules for refs versus callables.

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

Environment capture is therefore part of the current design, not an
open question. Extern callables behave like ordinary closures in this
respect: they may read captured variables through their deferred
summaries, but they never mutate the environment itself.

## Registry

```
inductive ExternImpl where
  | val : Value → ExternImpl
  | pfn : (VarEnv → Value → Memory → Address → Nat → CallbackDriver →
             Except ExternError Value) → ExternImpl
  | fn  : (VarEnv → Value → Memory → Address → Nat → CallbackDriver →
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

Extern impls are expected to be deterministic under fixed inputs. The
runtime does not enforce this, but any FR-facing guarantee keyed by the
same id presupposes it.

On the proof side, the only assumption relevant here is that any
optional additional guarantee is keyed by the same extern id. The Lean
representation of that guarantee map is out of scope for this runtime
sub-proposal.

Impl signatures:

- `ExternImpl.val v` — the stored `Value` is returned directly. For
  `ref int` this is a `Value.loc l` that the driver has already
  wired into `Config.memory`; see the reference-types section.
- `ExternImpl.pfn f` — receives the unified runtime environment of the
  call (captured env plus the current argument binding), the argument
  value directly, the current `Memory`, the current `nextAddr`,
  remaining fuel, and the callback driver. The environment, memory, and
  `nextAddr` are read-only inputs: pure impls may inspect them but do
  not return or mutate them. The result is a `Value`, which may itself
  be a nested extern closure.
- `ExternImpl.fn f` — as `pfn`, but it may return updated `Memory` and
  updated `nextAddr` along with the returned `Value`.

Whether an impure extern may delete cells or otherwise violate the
language's usual memory-monotonicity discipline is intentionally left
unspecified here and should be reviewed separately from the allocation
interface.

For nested return specs, the impl returns the nested callable value
directly rather than asking the evaluator to synthesize it. In the
intended design, that returned value is the corresponding extern
closure, carrying the nested id from the declared return summary and
whatever captured environment the impl chooses to preserve. The runtime
does not enforce full conformance beyond ordinary kind/shape checks.

Kind disagreement between the current extern AST constructor and the
registered impl — for instance, a `.val` impl registered under an
identifier that the program reaches through an `externFn` node — is a
driver bug caught at dispatch as `ExternError.kindMismatch`.

Possible later extension: the registry could additionally store a
canonical extern AST and use `beqExpr` as a runtime sanity check. That
is intentionally not part of the current design surface.

## Nested Return Instantiation

When an extern application's outermost return summary is nested, the
impl returns the nested callable value directly. Operationally:

1. Start from the extern closure's captured runtime environment.
2. Bind the current argument under the extern's argument name, yielding
   `unifiedEnv`.
3. Invoke the registered impl.
4. If the outermost return summary is nested, the impl returns the
   nested callable as a `Value.closure` / `Value.peClosure`.

In the intended use, that returned value is the corresponding extern
closure, carrying the nested id declared in the return summary and an
environment derived from `unifiedEnv`. On later application, it goes
through the same runtime prologue and registry lookup as a top-level
extern value, keyed by its own nested identifier.

Later executability and FR lookup therefore come from that nested
identifier alone. The closure does not carry any separate proof-side
token, theorem handle, slot index, or bundle reference. Any optional
guarantee for the nested callable is recovered exactly as for a
top-level extern: by looking up the nested id in the externally
supplied guarantee map.

## Callbacks

Impls may apply Poison-level callables (closures or other extern
callables) through a driver handed to them by `beval`:

```
abbrev CallbackDriver :=
  (callable : Value) → (arg : Value) → (mem : Memory) →
  (nextAddr : Address) → (fuel : Nat) →
    Except ExternError (Value × Memory × Address)
```

The driver dispatches `callable arg` against `mem` and `nextAddr` with
`fuel`, exactly as `beval` would for an `Expr.app` node. Purity is
inferred from the callable constructor exactly as today:
`Value.peClosure` runs without memory effects and returns the input
memory and `nextAddr` unchanged; `Value.closure` may update memory and
advance `nextAddr`, and is rejected when a pure impl supplies it
(mirroring the existing `pureMode` rule). Operationally, `beval`
constructs the callback driver at the call site: impure extern calls
get a driver that may execute both closure kinds, while pure extern
calls get a driver that rejects `Value.closure` immediately.

Fuel threads through the driver: each callback deducts one unit before
invoking `beval` on the callable's body. `beval`, the driver, and
`bevalFunctionBody` share one termination measure; no new well-founded
argument is needed.

An impl unable to complete within its budget returns
`ExternError.fuelExhausted`. Nothing in the language lets an impl
reach the enclosing program by name — it can only apply callables it
was handed as arguments or obtained from previous driver calls.

## Shape Checking

A single helper `valueMatchesTyp : Value → Typ → Bool` maps value
constructors to `Typ` cases. It is applied:

- on call entry, to the argument against the declared input `Typ`;
- on call exit, to the returned value against the declared output
  `Typ` from the outermost `ExternReturn`;
- on `Expr.externVal` dispatch, to the stored value against the
  declared `Typ`.

It does not inspect poison, predicates, or effect summaries. Those
are proof-side concerns.

## Errors

```
inductive ExternKind where
  | val | fn | pfn

inductive ExternError where
  | missing           (id : ExternId)
  | kindMismatch      (id : ExternId) (site : ExternKind) (impl : ExternKind)
  | shapeMismatch     (id : ExternId) (at_ : ArgOrReturn) (expected : Typ) (actual : Value)
  | implFailure       (id : ExternId) (msg : String)
  | fuelExhausted     (id : ExternId)
```

All cases surface through `EvalResult.runtimeError` with a formatted
message; no new top-level result case is added.

For nested return specs, the runtime relies on the impl to return the
corresponding nested callable value directly. Any violation of that
expectation surfaces as a downstream kind/shape/runtime error rather
than through a dedicated top-level result case.

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
  return it.
- `Expr.externFn id _ _ _ _`: yield
  `Value.closure argName (Expr.externFn id ..) config.varEnv`.
- `Expr.externPfn id _ _ _`: yield
  `Value.peClosure argName (Expr.externPfn id ..) config.varEnv`.

Application dispatch keeps its existing `Value.closure` /
`Value.peClosure` branches. Inside each branch, the wrapped body is
inspected one level further: when the body's head constructor is
`Expr.externFn` (respectively `Expr.externPfn`), the prologue above
runs on the wrapped AST, then `unifiedEnv := closureEnv[param := arg]`
is formed, and the impure (respectively pure) impl is invoked with
`unifiedEnv`, the argument value, the current `Memory`, the current
`nextAddr`, `(fuel-1)`, and the callback driver. The returned `Value`
is shape-checked against the declared outermost `Typ`. For impure
externs, both `Memory` and `nextAddr` are updated from the impl result.
Otherwise the existing user-closure path runs unchanged. The
impure extern branch is rejected in `pureMode` exactly as a
user-defined `Value.closure` would be.

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
  `CallbackDriver`, `ExternKind`,
  `ExternError`, `valueMatchesTyp`, and a `register` helper; add
  `registry` to `Config`.
- `LeanPoison/BigStep.lean`: replace the three placeholder branches,
  run the dispatch prologue (lookup and kind-compatibility) on every
  extern AST, extend `Expr.app` dispatch, capture env when building
  extern closures, accept nested returned extern callables from impl
  results, define the callback driver inline.
- `LeanPoison/Typecheck.lean`: enforce the identifier-reuse rule by
  collecting extern occurrences and rejecting any duplicate identifier
  outright; keep fresh logical-location allocation for each accepted
  `extern val` occurrence.
- `LeanPoison/Parser.lean` and `parser/`: accept the identifier
  after `@` at each extern declaration.
- `poison-lang-spec/poison-lang.ott`,
  `doc/poison-lang-description.tex`: reflect the new identifier slot,
  extern-as-closure evaluation, the `Config.registry` field, and the
  callback semantics.
- `examples/`: add tests for `extern val` of each admitted type,
  `extern fn` with memory effects, `extern pfn` in predicates,
  duplicate-identifier rejection across all extern kinds,
  and an extern invoking a callback.
