# Extern Read Dependencies (`captures:`)

Status: design note. This records the dependency issue exposed by the
curried `max` builtin and specifies explicit extern read dependencies via
`captures:`.

Related documents:

- `doc/ffi-proposal.md` is the authoritative FFI status and roadmap document.
- `doc/extern-env-deps-plan.md` tracks implementation status for this design on
  the active `extern-env-deps` branch.
- `doc/extern-poison.md` explains the broader extern precondition, regime, and
  trust model that `captures:` extends to read dependencies.
- `doc/ffi-axioms.md` explains the proof-boundary structures that consume the
  trusted read-dependency obligations.

## Problem

Extern callable implementations receive a runtime environment and memory as
well as the explicit argument. The current extern argument precondition only
describes the explicit argument.

For `abs`, that is enough:

```poison
extern pfn @12 x : (int :> clean {}) -> ((int :> clean {}))
```

The implementation depends only on `x`. If two calls satisfy the clean
argument precondition, the two `x` values agree, so the clean result can agree.

Curried `max` is different:

```poison
let max =
  extern pfn @10 a : (int :> clean {}) -> (
    extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})))
in (max 3) 5
```

The runtime shape is:

```text
@10 a  returns an @11 closure that captures a
@11 b  returns max captured_a b
```

The `@11` declaration says that `b` must be clean and the result is clean, but
it does not say that the captured `a` is also a dependency of the result. In
the actual program, `@10` gates `a` as clean before producing the `@11`
closure. However, the abstract `@11` call-boundary proof quantifies over any
`@11` closure shape, including one whose runtime captured environment contains
a dirty or untracked `a`. Then two runs can agree on clean `b` but disagree on
captured `a`, producing different clean `max a b` results.

The proof gap is therefore not specific to `max`; it is a missing way to say:

```text
this extern may read these captured environment or memory entries, with these
qualified types
```

## Proposed Precise Model

Add explicit read dependencies to extern callable summaries. The dependency
list is a subset of the environment and memory entries that may be present,
not an exact description of all entries that may exist.

Proposed surface syntax:

```poison
extern pfn @10 a : (int :> clean {}) -> (
  extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})),
    captures: { a :> (int :> clean {}) })
```

For top-level externs, the same clause applies when an implementation
intentionally reads variables from its declaration environment or memory
locations reached through references:

```poison
extern pfn @id x : (ref int :> clean {}) -> ((int :> clean {})),
  captures: { !x :> (int :> clean {}) }
```

The clause is deliberately parallel to the existing `effects:` suffix. The
left side names the read dependency target, and `:>` introduces the qualified
type contract required for that dependency. Bare targets such as `a` name
environment entries; bang targets such as `!x` name memory entries reached
through references. As with `effects:` targets, a bang target is resolved in
the callable environment: it may name a captured reference variable or the
explicit argument when that argument is reference-typed. If an extern has both
clauses, the grammar should treat them as sibling contract clauses on the same
extern callable, not as part of the return type.

A memory-read example is `maxmem`: it takes two clean references to clean
integer cells and returns the max of the two cell values. The implementation
could compute the max directly or delegate the arithmetic to the existing
curried `max` extern after reading the cells.

```poison
let left = ref 3 in
let right = ref 5 in
let maxmem =
  extern pfn @20 r1 : (ref int :> clean {}) -> (
    extern pfn @21 r2 : (ref int :> clean {}) -> ((int :> clean {})),
      captures: { !r1 :> (int :> clean {}), !r2 :> (int :> clean {}) })
in (maxmem left) right
```

Here `!r1` is a memory dependency reached through a captured reference, while
`!r2` is a memory dependency reached through the explicit argument of `@21`.

An empty dependency list means the implementation's trusted result may depend
on the explicit argument and on registry-local implementation state that agrees
across the two FR runs, but not on ambient environment or memory entries.
`effects:` remains memory-write only.

Conceptually, this brings extern closures closer to ordinary closures. Normal
closure proofs already track per-captured-variable consistency through
`closureCapturedVarsRegime` / `consistentWithRegime`; `captures:` exposes the
read footprint that trusted extern proofs need in order to reuse the same kind
of agreement reasoning.

## Contract Syntax and Variance

Surface syntax should keep `:>` as contract/ascription syntax, not as the
variance relation. It appears inside `QTyp` values, such as
`(int :> clean {})`, and in extern clauses, such as
`captures: { a :> (int :> clean {}) }` and
`effects: { !r :> (int :> poisoned { 7 }) }`. The position of the contract
determines whether it is a precondition or postcondition.

The typing rules should use one structural relation:

```text
Qactual <:R Qdecl
```

In Ott/LaTeX, render this as `<:` with regime `R` as a subscript.

This relation means that an actual qualified type satisfies a declared
qualified type under regime `R`. Its shape is:

- Base type: the surface/runtime base types must match after erasure.
- Poison flag: a declared `poisoned` requirement accepts clean or poisoned
  actuals; a declared `clean` requirement needs the actual to be clean under
  `R`.
- Predicate: a declared `noPred` imposes no predicate obligation; a declared
  predicate requires the actual to carry the same structural predicate shape.
  There is no general logical implication.
- Tags/regime: an actual guarded value counts as clean under `R` when its guard
  tag is active in `R`; predicate-shape matching is modulo concrete tag identity
  in the current extern-argument design.

Arguments and `captures:` are input-side contracts, so the local check is:

```text
actual argument/dependency <:R declared requirement
```

Returns and `effects:` are output-side contracts, so the trusted obligation is:

```text
produced return / written cell <:R declared postcondition
```

When comparing whole extern specs, this same relation is lifted with the usual
variance: arguments and captures are contravariant
(`expected requirement <:R implementation requirement`), while returns and
effects are covariant (`implementation postcondition <:R expected
postcondition`). Variance belongs in these rule and spec-comparison layers, not
in the surface `:>` glyph.

Branch joins must respect the same variance. Return/effect postconditions may
combine by join, including collapsing distinct predicate shapes to `noPred`.
Capture preconditions combine by conjunction, not by return-side join: if two
branches require distinct non-`noPred` predicate shapes for the same target,
there may be no single `target :> QTyp` meet. The implementation must reject
that merge, poison enough to avoid relying on the capture, or otherwise require
compatible predicate shapes; it must not collapse capture predicates to
`noPred`, because that would drop a precondition the extern implementation may
depend on.

## Intended Typechecking Meaning

Each declared read dependency must be resolvable and must satisfy the
declared qualified type requirement at the extern call boundary. This is a
call-site contract, matching the extern argument precondition: a trusted result
is available only when the actual argument and every declared read dependency
currently satisfy their declared requirements under the call-site regime.

Bare environment dependencies are resolved in the callable environment, and
bang memory dependencies are resolved through that same callable environment to
the referenced memory entry, then checked against the memory entry's current
qualified type. The callable environment is the captured environment plus the
explicit argument binding, so a target may refer to either source:

- `name :> Q` checks the current callable-environment type of `name`;
- `!name :> Q` checks the current memory typing of the location reached through
  callable-environment reference `name`.

For the nested `@11` closure above:

1. `@10` is applied to `a`.
2. The `@10` argument precondition establishes that the actual `a` is clean.
3. The nested `@11` `captures: { a :> (int :> clean {}) }` descriptor records
   that every `@11` call must find `a` in the callable environment with a clean
   integer qualified type.
4. At an `@11` call, the call-boundary proof can use ordinary
   `agreeOnClean` at the body-entry context to conclude that captured `a`
   agrees across runs. This is the unguarded-clean path used by `max`; guarded
   dependencies need the call-site regime evidence described below.

The explicit argument `b` continues to be handled by the existing extern
argument-condition gate.

## Trusted Boundary Meaning

A trusted extern entry must justify that its implementation's clean result
depends only on:

- the explicit argument, under the declared argument precondition;
- the listed environment and memory read dependencies, under their declared
  qualified types;
- memory writes allowed by the existing extern effect summary.

Unlisted environment and memory entries may still be present at runtime. They
are outside the dependency contract: the trusted implementation proof must not
use them to justify a clean result. If an implementation reads such an entry in
a way that can affect the result, that entry must be listed as a dependency or
the result must be typed poisoned/guarded accordingly.

The typechecker verifies only the listed entries: each listed dependency exists
and satisfies its declared `QTyp`. It does not verify that the dependency list
is complete. Completeness is a trusted obligation: for a clean result, the
implementation must be relationally insensitive to all unlisted environment
and memory entries. Equivalently, across two FR runs with agreeing explicit
arguments, agreeing listed read dependencies, and agreeing registry-local
implementation state, the clean outputs must agree; any memory writes must
also stay within and satisfy the declared `effects:` summary.

This side condition matters for empty `captures:` clauses. A deterministic
implementation that reads only the explicit argument can have
`captures: {}`. A nondeterministic implementation, or one whose clean result
depends on registry-local state that need not agree across runs, must either
return a poisoned result for the nondeterministic part or stay outside the
trusted FR registry for that clean-return contract.

This preserves precision without requiring runtime closure environments or
memory footprints to be exactly equal to the declared dependency list.

## Implementation Status And Branch Boundary

The `extern-env-deps` branch implements this design on top of the `ffi`
integration branch. The curried-`max` environment-read path is implemented and
proved end-to-end. Guarded captures are implemented at the typecheck gate and
proved at the trusted call boundary. Memory-read (`!r`) dependencies are
implemented and proved end-to-end (the `maxmem` `!r2` explicit-argument form).
Branch-join capture conjunction merging is implemented (structurally, via the
existing closure-member set-merge) and proved. The pfn-side read-dependency
surface described here is therefore complete.

Already implemented for the curried-`max` path:

- `LeanPoison/Syntax.lean`, `parser/`, `LeanPoison/Parser.lean`, and
  `Pretty.lean` carry and round-trip the optional `captures: { ... }` clause.
- `LeanPoison/Typecheck.lean` stores declared pfn dependencies on extern typing
  closures and checks them at the extern call boundary through
  `capturesSatisfied`.
- `LeanProofs/ExternRuntime.lean`, `ExternBoundary.lean`, and the reachability
  stack carry dependency data through declarations, trusted registry agreement,
  and pfn call-boundary facts.
- `LeanProofs/ExternProofs.lean` proves the capture-bearing `@11` call fields
  for the captured-`a` dependency, and the curried-`max` program-level FR
  artifacts exercise the nested returned callable path.
- `LeanProofs/ExternProofs.lean` also proves
  `builtinMax11Guarded_callFR` / `builtinMax11GuardedSpec` for a guarded
  captured dependency; `LeanProofs/GuardedCapturesFR.lean` records the
  bare-declaration program-FR artifact.
- `LeanProofs/ExternProofs.lean` proves the memory-read extern `@23`
  (`builtinMemDerefSpec`, whose `builtinMemDeref_callFR` composes the
  reference-clean argument condition with the cell-clean `!r` capture);
  `LeanProofs/MemReadCapturesFR.lean` records both the bare-declaration and the
  applied/routed (`@23 (ref 3)`) program-FR artifacts. `@23` is registered in the
  shared `defaultRegistry`, so `examples/extern_captures_memread.poison` runs
  end-to-end and `examples/extern_captures_memread_poisoned.poison` is rejected.
- `LeanProofs/CaptureJoinConjunction.lean` records the branch-join capture
  conjunction: branch joins keep distinct capture-bearing members separate
  (`mergePFnTClosures` deduplicates by `beqPFnTClosure`, which compares the
  captures), never route capture contracts through the `noPred`-collapsing
  predicate join, and gate on every member when the merged closure is applied.
  `mem_mergePFnTClosures_extern_captures` is the structural fact (every branch's
  capture contract survives the merge verbatim) and
  `mergedParrow_apply_captures_conjunction` the operational one (applying the
  merged `parrow` requires both branches' capture gates). FR-soundness is
  inherited from the generic step theorem, which reads the applied member's
  captures directly from the merged function-position member list.
- `poison-lang-spec/poison-lang.ott` and `doc/poison-lang-description.tex`
  describe the surface syntax and call-time satisfaction judgement (including the
  memory-read two-cleanness-facts reading and the branch-join conjunction of
  capture preconditions).

All pfn-side read-dependency items required before merging this branch to `ffi`
are complete: bare environment reads, guarded call-time satisfaction,
memory-read `!r` dependencies, and branch-join capture conjunction merging.

The accepted/rejected example suite is in place: the guarded cases
(`extern_captures_guarded{,_inactive}.poison`), the memory-read cases
(`extern_captures_memread{,_poisoned}.poison`), and the branch-join cases
(`extern_captures_join_memread{,_poisoned}.poison` and
`extern_captures_join_guarded{,_incompatible}.poison`) cover both acceptance and
the call-gate rejection path.

Still out of scope for this branch:

- fn-side captures (`extern fn ... captures:`), unless explicitly promoted into
  this effort later;
- trusted guarded-value producer and applied-program routing for guarded
  de-poisoned values;
- trusted specs for default-registry builtins whose behavior is unrelated to
  read dependencies.

`LeanPoison/BigStep.lean` / `Runtime.lean` should continue to keep runtime
behavior permissive: the precise-dependency model does not restrict the runtime
environment or memory, but the trusted proof must show that unlisted entries do
not matter.

## Settled Design Choices

- Dependency lists should be allowed on every extern callable, whether
  top-level or nested. The list may be empty.
- Dependency requirements should use `target :> QTyp` entries, matching the
  shape used by `effects:`. Here `:>` is contract/ascription syntax, not the
  variance relation. Bare targets name environment entries; bang targets name
  memory entries.
- A bang target in `captures:` is resolved in the callable environment, so it
  may point through either a captured reference variable or the explicit
  argument when that argument is reference-typed.
- The typechecker should check a dependency requirement the same way it checks
  an extern argument condition: the current qualified type must satisfy the
  declared requirement via `Qactual <:R Qdecl`, rather than requiring literal
  equality.
- Dependency checks happen at the extern call boundary for both bare
  environment targets and bang memory targets. This is the specified behavior,
  not an implementation compromise: the extern is checked when it is about to
  rely on the dependency.
- Guarded predicates and extern-regime policy should use the same satisfaction
  relation as extern argument conditions. A declared-clean dependency requires
  the actual dependency target to be clean under the current regime: either
  literally clean, or carrying a guard whose tag is active in the regime. A
  declared predicate uses the same structural predicate-shape match as
  arguments, with no general logical implication.
- Runtime closure environments and memory may still contain entries not listed
  in `captures:`. The trusted contract, not runtime footprint restriction, is
  what states independence from unlisted entries.
- `captures:` supports environment and memory read targets. `effects:` remains
  memory-write only.
- For nested externs of any depth, the already-recorded outer dependencies
  become part of the callable environment used to check inner dependency
  targets. The model is not limited to the two-level `max` example.

## Guarded Dependencies

The argument check and capture check are both call-site gates. Extern arguments
are checked at call time because that is when the argument expression is
evaluated. Captured environment dependencies are also checked at call time,
because the extern implementation reads the callable environment when it is
called. Memory read dependencies are checked at the same boundary, because memory
may have changed since the closure was created.

For example:

```poison
captures: {
  a :> (int :> clean { 7, v => v >= 0 }),
  !r :> (int :> clean {})
}
```

means that both targets must satisfy their qualified requirements under the
current regime at the call boundary. If guard `7` is active in the call-site
regime, `a` can be accepted as clean-under-regime in the same sense as an extern
argument. If it is inactive at the call site, the gate rejects the trusted result
even if the guard was active when the closure was created.

This call-time rule is intentional. It avoids treating a stale capture-time
guard fact as a call-time fact, and it gives environment and memory dependencies
the same operational interpretation: the contract is checked when the extern is
about to rely on the dependency. For pfn captures, this obligation is implemented
at the typecheck gate and proved for the trusted guarded inner-`max` call
boundary. Routing that guarded call boundary through an applied program that
consumes a de-poisoned captured value remains later FFI/regime work: it needs a
trusted producer extern that returns a guarded/de-poisoned value for the consumer
extern to capture. That missing producer/routing proof is not a
declaration-time/call-time regime reconciliation issue.

Read-target resolution is also part of the trusted proof story. For a bang
target, the location set used by the typechecker/proof must be the same
location set that the implementation reads after unifying the captured
environment with the explicit argument. Under-approximating the listed read
targets is unsound for clean results, unless the trusted proof separately shows
that the omitted reads cannot affect the result.
