# Probe 3: Boundary Constructors

## Problem

Probe 2 made the fault-robustness theorem consume trusted extern evidence under
a populated runtime registry. The remaining gap is usability: concrete extern
drivers must still prove the raw `ExternBoundarySpec` fields directly:

- relational declaration and call FR fields ending in `StepFRPost`;
- single-run declaration and call fields ending in `ExternBoundarySinglePost`;
- the operational field `ExternOperationalSafe`, including impure-call
  `nextAddr` monotonicity.

That surface is too large for driver proofs. Probe 3 should introduce reusable
constructors that let driver proofs supply compact implementation behavior facts
and get a complete `ExternBoundarySpec`.

The top-level theorem impact is unchanged. Probe 3 must not weaken
`FaultRobustnessSpec`, add public preconditions, or change executable
semantics. It should only add proof-side constructor APIs.

## Analysis

The current proof stack has the right consumers:

- `LeanProofs/ExternRuntime.lean` defines `ExternDeclBoundaryRun`,
  `ExternCallBoundaryRun`, and `ExternOperationalSafe`.
- `LeanProofs/ExternBoundary.lean` defines `ExternBoundarySpec`,
  `ExternBoundarySinglePost`, `TrustedExternEntry`, `TrustedRegistry`, and
  `TrustedRegistry.operationalSafe`.
- `LeanProofs/StepFR.lean` defines `BoundaryTagMeaningPost` and `StepFRPost`,
  which are the target postconditions constructors must package.

The highest-risk constructor is `pureUnaryCleanInt`: it is the intended path for
`abs` (`@12`) and the inner stage of `max` (`@11`). It exercises successful
pure extern call runs, `validateExternReturn`, clean integer agreement, value
typing, single-run posts, and the pure branch of `ExternOperationalSafe`.

Lower-risk constructors should follow only after `pureUnaryCleanInt` compiles,
because they can reuse its helper layer:

- `constCleanInt` covers extern integer values such as `@20`.
- `nestedPfn` covers the outer curried `max` stage (`@10`), returning an extern
  pure closure.
- `refValInitialized` covers initialized reference values such as `errno`
  (`@21`).
- `impureCellUpdate` covers impure cell updates such as `set_err` (`@22`).

## Proposed Approach

Add a new proof module:

```lean
LeanProofs/ExternBoundaryConstructors.lean
```

The module should import `LeanProofs.ExternBoundaryProofs` and define
constructor-facing behavior predicates plus the public constructor lemmas under
`namespace ExternBoundarySpec`. Since `lakefile.lean` uses
`globs := #[.submodules LeanProofs]`, no lakefile change is needed.

Keep the existing trusted-boundary interfaces stable unless a constructor proof
shows that a current boundary payload cannot expose a required fact. In that
case, stop the constructor proof, record the exact missing projection, and make
the smallest payload/API change needed before continuing.

All helper declarations should be `private` by default. Make a helper public
only when a later constructor or driver proof will call it directly.

Constructor behavior predicates should not duplicate facts already exposed by
`ExternCallBoundaryRun.fn` / `.pfn`. In particular, successful call-boundary
runs already include `validateExternReturn` success, so constructors should use
that evidence for output-shape glue and reserve behavior predicates for
implementation-specific facts such as the integer function being computed, the
captured environment dependency, or the updated cell address.

## Plan

### Stage 1: Constructor Module and Shared Skeleton

Create `LeanProofs/ExternBoundaryConstructors.lean` with:

- imports, namespace setup, and short module documentation;
- impossible-case helpers for declaration/call kind mismatches;
- helper lemmas for packaging unchanged-output configs for pure calls and
  extern values;
- helper lemmas for first-order clean values:
  `valueHasETyp` for `Value.num`, `valueConsistentWithRegime` for clean
  no-predicate integers, and `resultAgreesIfClean` from equality of clean
  integer outputs;
- dedicated helpers that produce the `BoundaryTagMeaningPost` fragment before
  assembling the rest of `StepFRPost`;
- one private full-post assembler invoked by the constructors, so tag-meaning
  details do not leak into driver-facing behavior predicates;
- a local proof pattern for turning one-run constructor facts into
  `ExternBoundarySinglePost`.

Done when the new module compiles with no public constructor theorem yet.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternBoundaryConstructors.lean
```

Status: completed on 2026-05-13.

Implemented `LeanProofs/ExternBoundaryConstructors.lean` with a private helper
layer only; no public constructor theorem was added in this stage. The module
currently provides:

- declaration/call/implementation mismatch helpers for impossible extern-kind
  branches;
- unchanged-output helpers for declaration runs and pure `pfn` call body-output
  configs;
- clean integer helper facts for `valueHasETyp`,
  `valueConsistentWithRegime`, `agreeValueUnder`, and
  `resultAgreesIfClean`;
- `BoundaryTagMeaningPost` packaging from explicit tag facts;
- private `StepFRPost` and `ExternBoundarySinglePost` assemblers;
- a same-state single-run assembly helper for one-run constructor fields.

Cascading adjustments:

- Stage 2 should assemble both `declFR` and `callFR` through the private
  `stepFRPost_of_parts` helper, so the `pureUnaryCleanInt` behavior predicate
  can focus on extern-specific integer behavior rather than raw
  `StepFRPost` structure.
- Stage 2 and Stage 4 pure-call proofs should use
  `callRun_pfn_bodyOutputConfig_eq_bodyConfig` for the unchanged synthetic
  body-output config.
- Stage 3 value constructors can use `declRun_output_config_eq_input` for
  declaration single-run/FR unchanged-state facts and
  `false_of_call_run_kind_val` for impossible call-boundary obligations.
- If Stage 2 needs a same-state two-run assembler specialized to unchanged
  declaration configs, add it as a private wrapper around
  `stepFRPost_of_parts` rather than exposing a new public helper.

### Stage 2: `pureUnaryCleanInt`

Define a small behavior predicate for pure unary integer externs. It should be
specific enough that built-in `abs` and inner `max` can prove it directly, but
general enough to avoid mentioning those concrete ids.

The predicate should require:

- declaration shape: `d.kind = .pfn`, `d.typ = .int`,
  `d.argName = some x`, and
  `d.retSpec = some (.simple .int false .noPred)`;
- implementation shape: `impl = ExternImpl.pfn implPfn`;
- inversion-shaped successful runtime behavior:
  every `implPfn env vArg mem = .ok vOut` produces
  `vArg = Value.num n` and `vOut = Value.num (f env n)` for some `n`;
- no mutation or allocation, inherited from `ExternImpl.pfn`;
- clean-agreement preservation:
  if the two body-entry environments agree on clean captured variables and the
  argument values are clean-agreeing integers, then `f env0 n0 = f env1 n1`;
- single-run well-formedness:
  every successful raw output is `wfValue addr`.

The inversion-shaped behavior fact is required because constructor proofs start
from `ExternCallBoundaryRun.pfn`, whose payload contains an arbitrary successful
`vArg` / `vRaw` pair plus `validateExternReturn` success. The behavior predicate
should identify the implementation-specific integer computation; validation
should provide the remaining return-shape compatibility with `retSpec`.

Then implement:

```lean
theorem ExternBoundarySpec.pureUnaryCleanInt :
  PureUnaryCleanIntSpec d impl ->
  ExternBoundarySpec d impl
```

The theorem must fill:

- `declFR` by using the extern declaration run facts to prove the returned
  `Value.peClosure` has the expected extern closure type and unchanged config;
- `callFR` by inverting `ExternCallBoundaryRun.pfn`, using the behavior
  predicate to identify integer outputs, and packaging `StepFRPost`;
- `declSingle` and `callSingle` by reusing the same typed-value and
  regime-consistency facts in one-run form;
- `operational` by proving the pure `pfn` clause and closing `fn`/`val`
  clauses by constructor mismatch.

Done when the constructor compiles without `sorry` or new `axiom`, and its
statement is usable without unfolding `StepFRPost` at call sites.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternBoundaryConstructors.lean
make lean-build-file FILE=LeanProofs/FaultRobustnessProofs.lean
```

Status: partially completed / blocked on 2026-05-13.

Implemented the public `PureUnaryCleanIntSpec` behavior structure and a private
`pureUnaryCleanInt_operational` helper that derives the `ExternOperationalSafe`
projection for pure unary integer `pfn` implementations. The full public
constructor theorem

```lean
theorem ExternBoundarySpec.pureUnaryCleanInt :
  PureUnaryCleanIntSpec d impl ->
  ExternBoundarySpec d impl
```

is not yet added, because Stage 2 exposed an underspecification in the current
FR boundary contract:

- `ExternDeclBoundaryRun` is runtime evidence. It is indexed by `res`, but the
  declaration facts rightly do not restate the typechecker's result-shape facts.
  The problem is that `ExternBoundarySpec.declFR` / `.declSingle` currently ask
  a driver spec to prove posts for an arbitrary `res` under a successful
  runtime declaration run, without also receiving the evidence that this `res`
  was produced by successful typechecking.
- `ExternCallBoundaryRun` has the same split. The runtime run records the
  extern implementation call and `validateExternReturn` success. It should not
  duplicate the typechecker's conclusions about the member result. The FR
  contract nevertheless needs a typing-origin premise for the call result in
  order to derive `ctxAfter bodyCtx res`, result `QTyp`, regime, and clean
  agreement facts.

Chosen cascading adjustment before continuing Stage 2:

- Strengthen the theorem-facing boundary contracts with explicit
  typechecking-origin premises, instead of adding structural typechecker facts
  to `ExternDecl*Facts` / `ExternCall*Facts`.
- Keep `ExternRuntime.lean` focused on runtime facts. This avoids duplicating
  typechecker logic in boundary-run payloads and keeps the source of truth for
  `res.qualType`, `res.tagEnv'`, predicates, and `ctxAfter` in the typechecker
  proof layer.
- Add small proof-carrying wrappers under one namespace:

  ```lean
  namespace ExternBoundaryTyping

  inductive Decl :
      ExternDeclaration -> Expr -> TypeContext -> TypeResult -> Prop

  inductive Call :
      ExternDeclaration -> Expr -> ExternCallEntry -> TypeResult -> Prop

  end ExternBoundaryTyping
  ```

  These wrappers should carry successful typechecking / closure-application
  origin evidence, not hand-written copies of the resulting shape. Constructor
  proofs can then invert the wrapper using existing typechecker lemmas. The
  declaration predicate should be relation-carrying, not merely
  `∃ fuel, typecheck ctx postExpr fuel = .ok res`: it must also tie
  `postExpr` to the corresponding `d` so a boundary proof cannot use a result
  typed from an unrelated expression.
- Make `ExternBoundaryTyping.Call` project from the existing app-typing evidence already
  built by StepFRApp (`AppFnClosureListFromTypecheck` /
  `AppPfnClosureListFromTypecheck`) plus the selected extern closure-member
  application evidence. Avoid introducing a second, parallel notion of "this
  call result came from typechecking".
- Before threading the wrappers through every provider, do a narrow spike on
  the `pureUnaryCleanInt` declaration `declFR` case: assume
  `ExternBoundaryTyping.Decl` exists and confirm that existing extern
  typecheck inversion lemmas expose the needed projections for
  `res.qualType.etyp`, `res.qualType.pred`, `ctxAfter ctx res`, and
  `res.tagEnv'`. If any projection is missing, add a focused typechecker
  inversion lemma before the broader boundary-contract refactor.
- Thread the declaration wrapper through `ExternBoundarySpec.declFR`,
  `.declSingle`, `ExternDeclBoundaryFRContract`,
  `ExternDeclBoundarySingleMaskedContract`, and their adapters.
- Thread the call wrapper through `ExternBoundarySpec.callFR`, `.callSingle`,
  `ExternCallBoundaryFRContract`, `ExternCallBoundarySingle*Contract`, the
  StepFRApp boundary-run provider helpers, and the keyed/direct call adapters.

Feasibility check:

- Declaration sites are straightforward. In `FaultRobustnessProofs.lean`, both
  single-run and two-run extern declaration branches still have
  `htc : typecheck ctxᵢ (Expr.extern...) ... = .ok res` in scope when they
  build `ExternDeclBoundaryRun.of_terminatesTo_extern*` and call
  `hdeclSingle` / `hdeclFR`.
- Call sites are feasible but higher-impact. `StepFRApp.lean` already builds
  `AppFnClosureListFromTypecheck` / `AppPfnClosureListFromTypecheck` from the
  app-level `htc`, and the extern-member paths expose
  `applyFnTClosure_staticSource_of_threaded_mem` /
  `applyPFnTClosure_staticSource_of_threaded_mem` evidence for the concrete
  member result passed to `ExternCallBoundaryRun`. Some provider signatures
  currently discard that evidence, so the refactor must thread a compact call
  result-origin witness alongside the existing run provider.
- Only after this boundary-contract adjustment should the public
  `ExternBoundarySpec.pureUnaryCleanInt` theorem be added. Stages 3-5 should
  wait on it, because value, nested, and impure constructors need the same
  typechecking-origin discipline.

### Stage 3: Value Constructors

Implement `constCleanInt` and `refValInitialized`.

`constCleanInt` should require:

- `d.kind = .val`, `d.typ = .int`, and `impl = ExternImpl.val (Value.num n)`;
- the declaration result is clean integer/no-predicate compatible;
- stored value well-formedness for every consumer config.

It should prove declaration FR/single fields directly and prove call FR/single
fields by showing no `ExternCallBoundaryRun` can exist for a value
implementation.

`refValInitialized` should require:

- `d.kind = .val`, `d.typ = .ref .int`, and
  `impl = ExternImpl.val (Value.loc a)`;
- a logical location `l` in the result locset with `theta.lookup l = some a`;
- the input memory contains the initialized driver cell at `a`;
- the address is below the consumer `nextAddr` whenever `wfConfig` is required.

It should package `valueHasETyp.loc`, runtime-instantiation preservation, and
the `val` branch of `ExternOperationalSafe`.

Done when both value constructors compile and can construct complete
`ExternBoundarySpec` values without call-boundary obligations leaking to the
driver.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternBoundaryConstructors.lean
```

### Stage 4: `nestedPfn`

Implement the constructor for pure externs returning nested pure extern
closures, targeting the outer curried `max` shape.

The behavior predicate should require:

- outer declaration shape: `d.kind = .pfn`, integer argument type, and
  `retSpec = some (.nestedPfn innerId innerArg innerArgTyp innerRet)`;
- implementation shape: `impl = ExternImpl.pfn implPfn`;
- inversion-shaped successful runtime behavior:
  every `implPfn env vArg mem = .ok vOut` exposes the integer argument and the
  returned closure data needed by the constructor;
- returned closure behavior matches
  `Value.peClosure innerArg (Expr.externPfn innerId innerArg innerArgTyp innerRet) envOut`;
- `envOut` matches the unified call-entry environment, or a specified captured
  environment derived from it;
- captured runtime values typecheck against `VarTypeEnv.toCaptured` and are
  covered in the runtime environment;
- clean-agreement preservation for the captured environment so later inner
  calls can consume the returned closure.

The constructor must prove the returned closure facts for:

- structural tag-meaning extension for the inner closure body via
  `ExternBatchTagMeaningExtension`, packaged as `BoundaryTagMeaningPost`;
- `valueHasETyp.peClosure_extern`;
- `valueConsistentWithRegime` for extern pure closures;
- `resultAgreesIfClean` for clean returned closures;
- declaration/call single-run fields;
- pure `ExternOperationalSafe`.

As in `pureUnaryCleanInt`, the call-boundary payload's
`validateExternReturn` success should discharge the generic nested-return shape
check. The constructor behavior predicate should supply the implementation-side
facts about which closure is returned, how `envOut` is related to the call-entry
environment, and how the captured clean facts are preserved.

Done when the constructor can express the `@10` outer `max` proof shape without
requiring the driver to build closure-typing or regime-consistency conjunctions
manually.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternBoundaryConstructors.lean
make lean-build-file FILE=LeanProofs/StepFRApp.lean
```

### Stage 5: `impureCellUpdate`

Implement the constructor for impure externs that update an existing integer
cell and return `unit`, targeting `set_err` (`@22`).

The behavior predicate should require:

- declaration shape: `d.kind = .fn`, `d.typ = .int`,
  `d.retSpec = some (.simple .unit false .noPred)`;
- implementation shape: `impl = ExternImpl.fn implFn`;
- successful runtime behavior:
  `implFn env (Value.num n) mem addr =
    .ok (Value.unit, Memory.update mem cellAddr n, addr)`;
- inversion-shaped success for arbitrary successful `vArg` / raw output pairs,
  with `validateExternReturn` providing the return-shape check against
  `.simple .unit false .noPred`;
- no allocation, stated as `addr' = addr`, which implies `addr <= addr'`;
- memory-domain preservation: updating `cellAddr` does not introduce an
  address outside the configured bound;
- input precondition that the updated cell is already initialized and below
  `addr`;
- clean-agreement preservation for the updated memory under the effect
  predicate and current regime.

The constructor must prove:

- impure `fn` operational monotonicity and well-formedness;
- declaration FR/single for the extern function closure;
- call FR/single for the unit result and updated memory;
- impossible pure/value operational clauses by constructor mismatch.

Done when impure address monotonicity, `wfConfig`, and clean-memory agreement
are all derived from the compact behavior predicate.

Verification:

```bash
make lean-build-file FILE=LeanProofs/ExternBoundaryConstructors.lean
make lean-build-file FILE=LeanProofs/SemanticsProperties.lean
```

### Stage 6: Public API Polish

Review the constructor statements from the perspective of future driver proofs.
The public API should expose only:

- the five constructor theorem names listed in `doc/ffi-axioms.md`;
- the minimal behavior-spec structures needed as theorem inputs;
- any helper that a concrete built-in proof must reasonably call.

Keep raw `StepFRPost` and `ExternBoundarySinglePost` assembly internal to the
constructor module. Update doc comments so each constructor states which runtime
extern shape it covers and which built-in ids motivated it.

Done when `rg "StepFRPost" LeanProofs/ExternBoundaryConstructors.lean` shows
direct assembly only in constructor internals, not in behavior-spec statements.

Verification:

```bash
make lean-build
```

## Acceptance Criteria

- `LeanProofs/ExternBoundaryConstructors.lean` exists and compiles.
- The following public theorem names exist:
  - `ExternBoundarySpec.pureUnaryCleanInt`
  - `ExternBoundarySpec.constCleanInt`
  - `ExternBoundarySpec.nestedPfn`
  - `ExternBoundarySpec.refValInitialized`
  - `ExternBoundarySpec.impureCellUpdate`
- Each constructor derives all five fields of `ExternBoundarySpec`.
- No constructor asks concrete drivers to prove `StepFRPost` or
  `ExternBoundarySinglePost` directly.
- No new public hypothesis is added to
  `TypeSystemEnforcesFaultRobustness`.
- No executable semantics, parser behavior, examples, Ott spec, or user-facing
  language docs change as part of Probe 3.
- There is no net increase in `sorry`, and no new `axiom`.
- `make lean-build` succeeds.

## History

Probe 1 made extern closures and call boundaries first-class proof objects:
`BoundaryTagMeaningPost`, `StepFRPost`, extern ids in closure typing, transitive
extern-return reachability, and app inversion facts.

Probe 2 made the fault-robustness theorem registry-aware. Successful extern
declarations and calls now consume trusted boundary evidence from
`TrustedRegistry`, and `TrustedRegistry.operationalSafe` bridges each entry's
`ExternOperationalSafe` into the registry-level operational predicate consumed
by semantic preservation lemmas.

The Probe 3 ordering is high-risk-first. `pureUnaryCleanInt` is scheduled before
the broader constructor set because it validates the core constructor pattern
against a realistic pure extern call before investing in value, nested closure,
or impure-memory variants.
