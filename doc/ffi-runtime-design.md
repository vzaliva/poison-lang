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

Environment capture is part of the current design. Extern callables
behave like ordinary closures in this respect: they may read captured
variables through their return and effect summaries, but they never
mutate the environment itself.

## Registry

```
structure ExternCallable where
  invoke : ExternValue → Memory → Address → Nat →
             Except ExternError (ExternValue × Memory × Address × Nat)

inductive ExternValue where
  | plain    : Value → ExternValue
  | callable : ExternCallable → ExternValue

inductive ExternImpl where
  | val : Value → ExternImpl
  | pfn : (VarEnv → ExternValue → Memory → Address → Nat →
             Except ExternError (Value × Nat)) → ExternImpl
  | fn  : (VarEnv → ExternValue → Memory → Address → Nat →
             Except ExternError (Value × Memory × Address × Nat)) → ExternImpl

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

A driver may additionally validate registry coverage against the
program's declared extern ids before evaluation begins. If it does not,
missing entries surface on first reach as `ExternError.missing`.

Extern impls are expected to be deterministic under fixed inputs. The
runtime does not enforce this, but any FR-facing guarantee keyed by the
same id presupposes it.

Fuel is threaded through extern invocation and callable capabilities
because callback-enabled execution can form cross-boundary call cycles:
Poison may call an extern, the extern may invoke a passed Poison
callable, and that callable may call the extern again (or another
extern). The runtime therefore keeps one explicit fuel budget across
ordinary evaluation, extern calls, and capability invocation so the
combined execution remains terminating by fuel.

On the proof side, the only assumption relevant here is that any
optional additional guarantee is keyed by the same extern id. The Lean
representation of that guarantee map is out of scope for this runtime
sub-proposal.

Impl signatures:

- `ExternImpl.val v` — the stored `Value` is returned directly. For
  `ref int` this is a `Value.loc l` that the driver has already
  wired into `Config.memory`; see the reference-types section.
- `ExternImpl.pfn f` — receives the unified runtime environment of the
  call (captured env plus the current argument binding), the marshalled
  argument as `ExternValue`, the current `Memory`, the current
  `nextAddr`, and remaining fuel. The environment, memory, and
  `nextAddr` are read-only inputs: pure impls may inspect them but do
  not return or mutate them. The result is a `Value`, which may itself
  be a nested extern closure, together with the remaining fuel after the
  impl finishes its work.
- `ExternImpl.fn f` — as `pfn`, but it may return updated `Memory` and
  updated `nextAddr` along with the returned `Value` and the remaining
  fuel.

Whether an impure extern may delete cells or otherwise violate the
language's usual memory-monotonicity discipline is intentionally left
unspecified here and should be reviewed separately from the allocation
interface.

For nested return specs, the impl returns the nested callable value
directly rather than asking the evaluator to synthesize it. In the
intended design, that returned value is the corresponding extern
closure, carrying the nested id from the declared return summary and
whatever captured environment the impl chooses to preserve. The runtime
checks nested returned callables against the declared nested summary
before accepting them.

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
5. The runtime validates that returned value against the declared nested
   summary.

For `ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects`,
the accepted shape is exactly:

`Value.closure innerArg (Expr.externFn innerId innerArgTyp innerRet innerEffects) env`

where `innerId` is the identifier carried by the nested return
descriptor. For `ExternReturn.nestedPfn innerArg innerArgTyp innerRet`,
the accepted shape is exactly:

`Value.peClosure innerArg (Expr.externPfn innerId innerArgTyp innerRet) env`

with the corresponding nested identifier. Any other returned value is
rejected as `ExternError.nestedReturnMismatch`.

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

## Callable Capabilities

Extern impls are not given a general-purpose hook for running arbitrary
Poison code. Instead, when a Poison callable crosses into extern land,
the runtime marshals it as an `ExternValue.callable` carrying:

- a specialized `invoke` lambda for that specific callable.

These capability objects are created by the runtime during marshalling.
Impls are consumers of capabilities, not their constructors.

That lambda is a partially specified application step derived from the
ordinary evaluator: it applies the already-fixed callable to one
marshalled argument, threading `Memory`, `nextAddr`, fuel, and runtime
errors exactly as normal Poison application would. Concretely,
`invoke arg mem nextAddr fuel` behaves as applying the specific callable
that was marshalled into this capability to the Poison value
represented by `arg` under those runtime inputs. The result is
re-marshalled as `ExternValue`, and the returned `Nat` is the remaining
fuel after that application step.

This keeps the boundary capability-scoped:

- an extern may invoke only callable values explicitly passed to it or
  returned to it from earlier capability invocations,
- it may not ask the runtime to evaluate an arbitrary `Expr`, and
- it may not discover additional call targets by name lookup in the
  surrounding program.

Callable capabilities are invocation-only. An extern may use them by
calling `invoke`, but it may not pass an arbitrary received Poison
callable back into Poison unchanged. If an extern wants to return a
callable, it must return an explicitly constructed extern closure of
the declared result shape.

When a capability invocation returns a Poison callable, the runtime
marshals that result back into `ExternValue.callable` before handing it
to the extern impl. In this way, higher-order interaction remains
possible without exposing a general evaluator interface.

Purity remains aligned with ordinary Poison application semantics. The
capability for a pure callable preserves `Memory` and `nextAddr`; a
capability for an impure callable may update both. The runtime should
not expose an invokable impure capability to a pure extern in any case
where ordinary `pureMode` would reject that application. If a pure
extern invokes a capability that nevertheless returns modified `Memory`
or `nextAddr`, the runtime ignores those modifications and keeps the
caller's original state.

Fuel threads through capability invocation exactly as it does through
ordinary application: each invocation deducts one unit before reusing
the existing application logic, and the returned `Nat` is the remaining
budget for subsequent work. An impl unable to complete within its
budget returns `ExternError.fuelExhausted`.

## Shape Checking

A single helper `valueMatchesTyp : Value → Typ → Bool` maps value
constructors to `Typ` cases. It is applied:

- on call entry, to the argument against the declared input `Typ`;
- on call exit for simple returns, to the returned value against the
  declared output `Typ` from the currently-dispatched extern's
  outermost `ExternReturn`;
- on `Expr.externVal` dispatch, to the stored value against the
  declared `Typ`.

It does not inspect poison, predicates, or effect summaries. Those
are proof-side concerns. Nested returns are checked separately by exact
closure-shape validation as described above.

## Errors

```
inductive ExternKind where
  | val | fn | pfn

inductive ExternError where
  | missing           (id : ExternId)
  | kindMismatch      (id : ExternId) (site : ExternKind) (impl : ExternKind)
  | nestedReturnMismatch (id : ExternId) (actual : Value)
  | shapeMismatch     (id : ExternId) (at_ : ArgOrReturn) (expected : Typ) (actual : Value)
  | implFailure       (id : ExternId) (msg : String)
  | fuelExhausted     (id : ExternId)
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
is formed, and the argument value is marshalled into `ExternValue`
before crossing the boundary. For first-order values this is
`ExternValue.plain`; for callable values it is
`ExternValue.callable ⟨invoke⟩`, where `invoke` is the specialized
application capability described above. The impure (respectively pure)
impl is then invoked with `unifiedEnv`, the marshalled argument, the
current `Memory`, the current `nextAddr`, and `(fuel-1)`. The returned
`Value` is shape-checked against the declared outermost `Typ`; when the
return summary is nested, exact closure-shape validation is applied
instead of relying on `valueMatchesTyp` alone. For impure externs,
`Memory`, `nextAddr`, and remaining fuel are updated from the impl
result. For pure externs, remaining fuel is updated from the impl
result but any returned `Memory` / `nextAddr` modifications are
ignored. Otherwise the existing user-closure path runs unchanged. The
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
  `ExternCallable`, `ExternValue`, `ExternKind`, `ExternError`,
  `valueMatchesTyp`, and a `register` helper; add `registry` to
  `Config`.
- `LeanPoison/BigStep.lean`: replace the three placeholder branches,
  run the dispatch prologue (lookup and kind-compatibility) on every
  extern AST, extend `Expr.app` dispatch, capture env when building
  extern closures, marshal callable arguments into invocation
  capabilities, and accept nested returned extern callables from impl
  results.
- `LeanPoison/Typecheck.lean`: enforce the identifier-reuse rule by
  collecting extern occurrences and rejecting any duplicate identifier
  outright; keep fresh logical-location allocation for each accepted
  `extern val` occurrence.
- `LeanPoison/Parser.lean` and `parser/`: accept the identifier
  after `@` at each extern declaration.
- `poison-lang-spec/poison-lang.ott`,
  `doc/poison-lang-description.tex`: reflect the new identifier slot,
  extern-as-closure evaluation, the `Config.registry` field, and the
  callable-capability semantics.
- `examples/`: add tests for `extern val` of each admitted type,
  `extern fn` with memory effects, `extern pfn` in predicates,
  duplicate-identifier rejection across all extern kinds,
  and an extern invoking a function argument through its capability.
