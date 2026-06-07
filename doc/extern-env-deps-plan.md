# Implementation Plan: `captures:` extern read dependencies

Implements `doc/extern-env-deps.md`. Branch: `extern-env-deps`, directly above
the FFI integration branch `ffi`.

Related documents:

- `doc/extern-env-deps.md` is the design source of truth for `captures:`.
- `doc/ffi-proposal.md` is the authoritative FFI status and roadmap document.
- `doc/extern-poison.md` explains the extern precondition, regime, and trust
  model that `captures:` extends.
- `doc/ffi-axioms.md` explains the proof-boundary structures used by the
  trusted specs mentioned here.

The driving case is curried `max`: the inner `@11` reads the captured outer
argument `a`, which the abstract extern call-boundary proof could not previously
justify as a clean dependency. That curried-`max` (all-clean) path is now
**implemented and proved end-to-end**. The branch is not complete merely because
that path is green: `extern-env-deps` should merge to `ffi` only after the pfn
read-dependency model is complete enough to match the goal document. Guarded
dependencies are now implemented/proved to the same maturity level as extern
argument guards: typecheck/examples are end-to-end and the trusted call boundary
is proved. Memory-read (`!r`) dependencies are now implemented/proved end-to-end
as well — including an applied/routed program-FR (`@23 (ref 3)`) and a runnable
example. The final pfn read-dependency item, branch-join capture conjunction
merging, is now implemented/proved as well, so every pfn read-dependency item
required before merging is complete. The remaining guarded-value work is a
trusted producer extern plus an applied program-FR proof that routes
`producer -> captured value -> consumer`; that is broader FFI/regime validation,
not a blocker for this branch.

## Status — curried-`max` path: DONE; branch still in progress

Last verified curried-`max` state: `lake build` green (11464 jobs), `make test`
104/104, repo-wide 0 `sorry`, 0 warnings. Axiom status (precise): this work adds
**no `sorry` and no new axioms**. The new boundary specs and the
`defaultRegistry_lookup_*` interpreter-registry lemmas are axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only). `maxCurried_FR` /
`appliedMaxCurried_FR` / `TypeSystemEnforcesFaultRobustness` inherit the FR step
stack's **pre-existing** `native_decide` axioms (from `StepFRIte.lean` /
`StepFR.lean` / `FaultRobustnessProofs.lean`, untouched by this work) —
eliminating those is a separate, opt-in task and is not part of the `captures:`
effort.

What is implemented and proved:

- **Surface syntax + AST.** `CaptureTarget` (`bareVar`/`memVar`) and `Capture`
  (`target`, `typ`, `poison`, `pred`); `captures` on `ExternDeclaration`, the four
  AST nodes (`Expr.externFn/externPfn`, `ExternReturn.nestedFn/nestedPfn`), and
  `PFnTClosure.extern`. `parser/` grammar + `LeanPoison/Parser.lean` parse the
  optional `captures: { … }` clause (bare and `!`bang targets); `Pretty.lean`
  round-trips it.
- **Typecheck — population + call-boundary gate.** `typecheckExternPfn` records
  the declared captures on the produced closure member, and
  `applyPFnTClosure(AtCursor)` enforces them at the call boundary via
  `capturesSatisfied` (the same `Qactual <:R Qdecl` shape as the extern argument
  condition). One captures value per extern id = the source contract, consistent
  across the typed closure, reachability, and the runtime declaration.
- **Two-track decoupling.** The *contract* captures (the closure type member, what
  `capturesSatisfied` gates on) is independent of the *runtime body-AST* captures.
  The value-track lemmas carry an independent `memberCap`; `Call.pfnExternMember`
  carries a decoupled `bodyCaptures`; and the runtime check `validateExternReturn`
  compares a nested return's produced closure **modulo captures** (the body shape,
  not the contract — the contract is enforced at the call gate). Gated to
  captures-bearing nested returns, so `captures = []` programs are byte-identical.
- **Trusted boundary specs.** `builtinMax11_callFR` discharges the inner `@11`
  call boundary using the captured-`a` dependency (body-entry `agreeOnClean`
  forces `a₀ = a₁`, the argument gate forces `b₀ = b₁`, so `max a b` agrees).
  Full 5-field `ExternBoundarySpec`s: `builtinMax10Spec` (whose `callFR` returns
  the capture-bearing `@11` closure) and `builtinMax11CapturesSpec`.
- **Shared runtime core (interpreter ↔ proof dedup).** The built-in extern
  implementations and default initial state (`outerMaxImpl`, `innerMaxImpl`,
  `absImpl`, `sqrtImpl`, `setErrImpl`, `errnoAddr`, `defaultInitialState`,
  `defaultRegistry`) live in `LeanPoison/ExternBuiltins.lean`, imported by both
  the interpreter (`Main.lean`) and the proof side (`ExternProofs.lean`), so
  `builtinMax10Impl ≡ .pfn outerMaxImpl` *definitionally* — the running
  interpreter and the trusted boundary specs reference the **same** runtime
  functions, not textually-equal copies. The build-checked lemmas
  `defaultRegistry_lookup_max10` / `_max11` / `_abs` confirm the interpreter's
  assembled `defaultRegistry` resolves `@10`/`@11`/`@12` to exactly those trusted
  impls. (This is *function-level* agreement: the 7-entry interpreter registry is
  still a different object from the 2-entry proof `maxCurriedRegistry` — only the
  shared `@10`/`@11`/`@12` impls coincide.)
- **Program-level FR.** `MaxCurriedFR.maxCurried_FR` (the `@10` declaration; the
  registry `[@10, @11captures]` agrees with the reachable decls — `@10` `captures
  []`, `@11` `captures [a]` via `nestedPfn_here` — discharging
  `TrustedRegistryAgreesWithReachable`) and
  `MaxCurriedFR.appliedMaxCurried_FR` (the **applied** program
  `let m = @10 in (m 7) 2`, which applies `@11` so the FR derivation routes that
  application through `builtinMax11CapturesSpec.callFR` — the captured-`a` gate
  fires). The `nestedPfn_here` `rfl` forces the `[a]` registry decl (the `[]` decl
  fails to compile), so the result is non-vacuous.
- **Guarded captures.** `captures:` accepts guarded read dependencies at the
  call boundary using the same regime-sensitive satisfaction relation as extern
  argument conditions. `examples/extern_captures_guarded.poison` is accepted
  when `@238` is selected true by `--extern-regime`, while
  `examples/extern_captures_guarded_inactive.poison` is rejected when the guard
  is inactive. The trusted guarded inner-`max` call boundary
  `builtinMax11Guarded_callFR` and full 5-field `builtinMax11GuardedSpec` are
  proved axiom-clean; `GuardedCapturesFR.guardedCaptures_FR` gives the
  bare-declaration registry-agreement/program-FR artifact. Routing the guarded
  `callFR` through an applied program remains later FFI/regime work: it needs a
  trusted producer extern that returns a guarded/de-poisoned value for the
  consumer extern to capture.
- **Spec + examples.** `poison-lang.ott`: `capture_spec`/`capture_list` grammar,
  `CSL` on the extern declarations, the `capturesSatisfied` satisfaction
  judgement; `doc/poison-lang-description.tex`: the "Extern read dependencies"
  subsection (incl. the two-track / modulo-captures semantics).
  `examples/extern_captures_clause.poison` (simple-return) and
  `examples/extern_captures_curried_max.poison` (nested, runs to `7`).

Commits: `dc43938` (capture-generic stack), `b631c0e` (captures population),
`20a20c3` (`@10` `[a]` path + `validateExternReturn` modulo captures), `ed19340`
(`builtinMax11CapturesSpec`), `5583bfb` (`maxCurried_FR`), `971bf45`
(`appliedMaxCurried_FR`), `b46d156` (spec-doc consistency), plus the earlier
syntax/parser/Ott commits.

## Validated design (the crux, for reference)

`@11`'s `callFR` was the obligation the abstract extern summary could not
discharge: `@11` returns `max a b` reading captured `a`, but inverting
`Call.pfnExternMember` yielded the captured type-env `tenv` *existentially*, with
no fact that `a ∈ tenv` is clean. The capture contract supplies exactly that
fact; the call check lives *inside* `applyPFnTClosure(AtCursor)`, so the existing
`happly = .ok` premise of `Call.pfnExternMember` entails "each declared capture
resolves clean" — no new `Call` premise, no bridge surgery on the clean path.
`captures` threads like the fn-side `effects` field (decl → closure → `Call`
premise → registry match → reachability).

The key correction over the original risk analysis: typecheck population is *not*
mutually exclusive with the freed `value_shape`. The conflict only arose for the
*coupled* value-track form; making the value-track member captures **independent**
of the closure body captures (and the runtime check modulo-captures) keeps
`value_shape` free and population available.

## Completed since the curried-`max` capstone

- **Guarded dependencies + call-site regime evidence** (goal doc §"Guarded
  Dependencies"). Implemented for pfn `captures:` at the typecheck gate and
  proved at the trusted call boundary. The parser accepts guarded-clean capture
  requirements; active and inactive regime examples cover acceptance/rejection;
  `builtinMax11Guarded_callFR` / `builtinMax11GuardedSpec` prove the trusted
  boundary; and `GuardedCapturesFR.guardedCaptures_FR` proves the bare-decl
  registry-agreement shape. Applied guarded program routing remains later
  FFI/regime work because it needs a trusted guarded-value producer that returns
  the de-poisoned captured value.

- **Memory-read (`!r`) dependencies, end-to-end** (goal doc's `maxmem`
  `@20`/`@21`, the `!r2` explicit-argument half). Bang capture targets are now
  real beyond parser/typecheck: a trusted memory-read extern `@23 r : (ref int :>
  clean {}) -> (int :> clean {})` declaring `captures: { !r :> (int :> clean {})
  }` (dereferences its reference argument and returns the cell contents) carries
  a full 5-field `ExternBoundarySpec` (`ExternProofs.builtinMemDerefSpec`). Its
  relational `builtinMemDeref_callFR` is the new content, composing *two*
  load-bearing cleanness facts: the argument condition forces the reference clean
  (both runs realise `r` to a **common** logical cell, via
  `agreeValueUnder_ref_common_loc`), and the `!r` capture forces that cell's
  *contents* clean (the two reads agree, via `agreeOnClean` on the location
  side). A clean reference may point to a poisoned cell, so the capture is
  genuinely load-bearing. `MemReadCapturesFR.memReadCaptures_FR` proves the
  bare-decl registry-agreement shape and
  `MemReadCapturesFR.appliedMemReadCaptures_FR` the **applied/routed** program
  `@23 (ref 3)` — because a clean cell is trivially materialisable with `ref`,
  the memory-read path routes through the call boundary in an applied program,
  reaching the environment-capture gold standard (`appliedMaxCurried_FR`), not
  just the bare-decl level. `@23` is registered in the shared `defaultRegistry`
  (`defaultRegistry_lookup_memderef` confirms interpreter↔proof agreement), so
  `examples/extern_captures_memread.poison` runs end-to-end to `3`, while
  `examples/extern_captures_memread_poisoned.poison` is rejected at the call gate
  when the cell is poisoned. All new artifacts are axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound`); the program-FR theorems inherit
  only the FR step stack's pre-existing `native_decide` axioms.

- **Branch-join capture conjunction merge** (goal doc §"Contract Syntax and
  Variance"). When branches over capture-bearing extern closures are joined,
  their `captures:` preconditions combine by **conjunction**, not by the
  return-side join that collapses distinct predicate shapes to `noPred`. This is
  already enforced structurally by the existing closure-member set-merge:
  `joinETyps` on `parrow`s merges members with `mergePFnTClosures`, whose dedup
  (`beqPFnTClosure`, which compares `beqCaptureList`) keeps members that differ
  in their captures *distinct*; capture contracts never flow through
  `joinPredicates` (the `noPred`-collapse join); and applying a multi-member
  `parrow` (`applyClosuresThreaded`) fires *every* member's `capturesSatisfied`
  gate, so a successful application requires the conjunction of both branches'
  captures and rejects incompatible predicate shapes (no single actual can
  satisfy both a guard-closure and a guard-only requirement on the same target).
  `LeanProofs/CaptureJoinConjunction.lean` records this: the structural
  `mem_mergePFnTClosures_extern_captures` (every branch's capture contract
  survives the merge verbatim) and the operational
  `mergedParrow_apply_captures_conjunction` (applying the merged `parrow`
  requires both branches' capture gates), both axiom-clean. FR-soundness of the
  merged contract is *inherited* from the generic step theorem: `stepFR_app`
  reads the applied member's captures directly from membership in the
  function-position `parrow`'s (merged) member list
  (`ExternCallBoundaryPfnStaticSource.externMember`), and
  `TrustedRegistryAgreesWithReachable` covers it because
  `ExternDeclarationInProgram` descends into both `ite` branches. Examples:
  `extern_captures_join_memread{,_poisoned}.poison` (runnable memory-read
  dimension, accept→`3` / poisoned-cell reject) and
  `extern_captures_join_guarded{,_incompatible}.poison` (guarded non-`noPred`
  predicate dimension, compatible accept / incompatible guard-closure-vs-guard-only
  reject).

- **Representative examples and rejection coverage.** The accepted curried-`max`,
  guarded, memory-read, and branch-join examples are in place, and the negative
  path is covered by concrete rejections — `extern_captures_guarded_inactive.poison`
  (inactive regime), `extern_captures_memread_poisoned.poison` (poisoned cell),
  `extern_captures_join_memread_poisoned.poison` (poisoned cell behind a joined
  `!r`), and `extern_captures_join_guarded_incompatible.poison` (incompatible
  joined predicate shapes) — so the call gate's rejection is exercised in the
  example suite, not only implicit in proofs.

## Pre-merge status (`extern-env-deps` → `ffi`)

All pfn-side read-dependency items are implemented/proved: bare environment
reads, guarded call-time satisfaction, memory-read `!r` dependencies, and
branch-join capture conjunction merging. Nothing remains as a pfn-side
read-dependency blocker for this branch (subject to the standard gates).

## fn-side captures (`extern fn … captures:`): status

The operational/typechecking layer reaches **full parity** with the pfn side, and
the fault-robustness *proof*-layer obstruction that previously blocked a trusted
`kind = .fn` spec has been **removed** (see the design sketch below). The
remainder of this subsection records what the obstruction was and how parity was
reached operationally.

**Done (operational + typechecking + plumbing).** The `captures : List Capture`
field now lives on `FnTClosure.extern`, and captures are threaded end-to-end
through the fn paths: the fn `Decl`/`Call` (`fnExternMember`)/reachability
(`arrow_extern_*`, `externFn`)/`of_terminatesTo_externFn` variants all carry
captures, and `applyFnTClosureAtCursor`'s extern case gates on
`capturesSatisfied` at call entry (pre-effects, `unifiedEnv` hoisted above the
gate) exactly as the pfn path does. The parser accepts `captures:` on `extern fn`
alongside `effects:`. Two end-to-end interpreter examples exercise this:
`extern_fn_captures_clause.poison` (accept — `@22` `set_err` with both `effects:`
and a clean `captures: { y … }`, runs and writes `errno`) and
`extern_fn_captures_violation.poison` (negative call-gate — a poisoned captured
`bad` declared `clean` is rejected by `capturesSatisfied` at the call boundary).

**The obstruction (now removed).** Before the narrowing below, no trusted
`kind = .fn` `ExternBoundarySpec` was assemblable: a spec needs all five fields,
and two of them were *false as stated* for **any** fn declaration:

- `callFR` (`ExternCallBoundaryFR`) and `callSingle` (`ExternCallBoundarySingle`)
  quantify universally over `ExternBoundaryTyping.Call d _ entry res`. For a fn
  decl, `Call` has the extra constructor `fnRegularExternBody` (re-typechecking
  the `externFn` node), which forces `res.qualType.etyp = ETyp.arrow …` (a
  function type). Paired — as the contract requires — with a `kind = .fn`
  `ExternCallBoundaryRun`, the run forces the output `o` to the *return* type
  (e.g. `Value.num`). Both post types (`StepFRPost`, `ExternBoundarySinglePost`)
  then demand `valueHasETyp o res.qualType.etyp`, i.e. `valueHasETyp (num) (arrow
  …)`, which is false. `ExternCallFnFacts` leaves `res` unused (`_res`), so the
  two constructors constrain disjoint `entry`/`res` fields and are jointly
  satisfiable — the post is a genuine falsehood reachable from true hypotheses,
  not merely a hard proof.
- Root cause / asymmetry with pfn: a regular *pure* closure restricts its body to
  `PExpr` (the `Expr.toPExpr? body = some pbody` guard on `valueHasETyp.peClosure`,
  TypeSafety.lean:922), and `toPExpr?` excludes extern declarations — so a regular
  pfn closure can never carry a bare extern body, the pfn `Call` has only
  `pfnExternMember` (result = return type), and the obstruction never arises. The
  regular *impure* closure has no such restriction: `typecheckFn` records the body
  verbatim, so a regular `fn` closure *can* carry a bare `Expr.externFn` body, and
  the fn `Call` carries `fnRegularExternBody`. At runtime `(fn x => extern fn …)
  arg` **does** extern-dispatch — `beval` matches on the closure body's shape
  (BigStep.lean:212) and dispatches `@id`, returning its return value — while the
  `fnRegularExternBody` typing re-checks the extern node to an *arrow*. The
  universal callFR contract then conflates this type-vs-runtime-mismatched route
  with an actual extern dispatch.
- `declFR`, `declSingle`, and `operational` are *not* blocked (the declaration
  boundary's `Decl.fn` is a single constructor with no regular-body ambiguity,
  and the impl is operationally safe), but a spec is all-or-nothing.

**Remediation (delivered — see the design sketch below).** The trusted contract
was narrowed by removing `Call.fnRegularExternBody` outright, so a spec author is
no longer obligated on the regular-closure-extern-body route. Soundness is
discharged by making that route unreachable for well-typed values rather than by
a runtime consumer argument: a bare `extern fn` lambda body is rejected at
`typecheckFn`, and the value relations carry `¬ Expr.IsExternFnAst body`, so no
well-typed `Value.closure` reaches the boundary through the regular route. The
contract is therefore narrowed to real dispatch only, and a concrete
`kind = .fn` spec instance is now delivered (Checkpoint B — see "First trusted
`kind = .fn` spec" below).

## Design sketch: narrowing the trusted extern call contract (implemented)

Status: **implemented.** This records the remediation named above, which touches
the trusted boundary *and* the language's typing rules. The implementation
follows the sketch below, with one refinement discovered during the work: the
unreachability guard had to be placed on **two** value-relation inductives, not
just one (see "Guard placement" at the end of this section).

The realised end state:

- `ExternBoundaryTyping.Call` no longer has the `fnRegularExternBody` constructor;
  it has exactly `fnExternMember` and `pfnExternMember`. The trusted contracts
  `ExternCallBoundaryFR` / `ExternCallBoundarySingle` (and hence
  `ExternBoundarySpec.callFR` / `callSingle`) quantify over this narrowed `Call`,
  so they now cover **only** real extern dispatch. Public top-level FR theorem
  shapes are unchanged (they reference the contracts by name).
- `typecheckFn` (`LeanPoison/Typecheck.lean`) rejects a `fn` whose body is a bare
  `Expr.externFn`; `valueHasETyp`'s regular-closure route is kept disjoint from
  the extern route via guards on the value relations below, so no well-typed
  value takes the dropped route.
- `examples/extern_fn_bare_extern_body_reject.poison` exercises the new
  rejection; the Ott `fn_abs` rule carries the matching `not_extern_fn e` side
  condition.

### What the obstruction was

(Historical — describes the pre-narrowing state; the fixes are recorded in
"Change delivered" below.) The blocker was not merely "`callFR` is false for the
`fnRegularExternBody` route"; it traced to a typing/runtime disagreement the type
system used to admit. A regular lambda whose body is a bare extern node —
`fn x => extern fn @id …` — used to typecheck: `typecheckFn` recorded the body
verbatim as `FnTClosure.regular x (Expr.externFn …) …`, giving the lambda an
arrow whose
result is the `@id` closure type. But `beval` applies *any* `Value.closure` whose
body is an `externFn` node by **dispatching the extern**
(LeanPoison/BigStep.lean:212), returning `@id`'s validated return value (a
`Value.num`) — never a closure. Static type (arrow) and runtime result (return
value) disagreed for this program.

The pfn side never hits this: `valueHasETyp.peClosure` (TypeSafety.lean)
already carries `Expr.toPExpr? body = some pbody`, and `toPExpr?` rejects
`externPfn` bodies — i.e. a regular pure closure may not have a bare extern body.
The fn side lacked the analogous guard, which is why a trusted `kind = .fn`
spec was previously unbuildable. The narrowing below adds the missing guard
(`typecheckFn` now rejects bare extern bodies; the value relations carry
`¬ Expr.IsExternFnAst body`), restoring the symmetry.

### Correcting goal (b)

The intended split's clause (b) — "regular function-body evaluation, including a
body that produces an extern fn closure, stays covered by normal FR" — does not
hold as phrased for `fn x => extern fn @id`: that program does **not** produce a
closure at runtime; `beval` dispatches it. The achievable split:

- bodies that are **not** a bare extern node (e.g.
  `fn x => if c then extern fn @a else extern fn @b`) are genuine closures, run
  through `bevalFunctionBody`, and stay covered by normal FR — whose runtime
  witness `BevalAppSuccess.userFn` (SemanticsProperties.lean:380) **already**
  carries `hNotExternAst : ¬ Expr.IsExternFnAst body`;
- a bare extern body (`fn x => extern fn @id`) must be **rejected at typecheck**,
  restoring the invariant (already true on the pfn side) that a regular closure's
  body is never a bare extern node.

So the design completes a pre-existing semantic symmetry — it makes the typing
side agree with the runtime gate (`hNotExternAst`) that already exists — rather
than inventing new machinery.

### Change delivered: two coupled obligations

Both were necessary; neither alone keeps the repo at 0 `sorry`. (An early sketch
proposed a *separate* member-only `ExternDispatchCall` inductive and a guard on
`valueHasETyp.closure`; the delivered design is simpler on the first axis and
differently placed on the second — see "Guard placement" below.)

**Obligation 1 — narrow the trusted contract (single source of truth).** The
`fnRegularExternBody` constructor was removed directly from
`ExternBoundaryTyping.Call`, leaving exactly `fnExternMember` and
`pfnExternMember`. The contract *definitions* `ExternCallBoundaryFR` and
`ExternCallBoundarySingle` already quantify over `ExternBoundaryTyping.Call`, so
they were left textually unchanged and now cover only real dispatch; no parallel
`ExternDispatchCall` inductive was introduced. The `ExternBoundarySpec` structure
is unchanged (its fields reference the contracts by name).

**Obligation 2 — make the dropped route unreachable for well-typed values.**
Removing the constructor leaves the producers that built the `regularExternBody`
static source owing an impossible witness. To collapse them:

- `typecheckFn` (`LeanPoison/Typecheck.lean`) rejects a lambda whose body is
  `Expr.externFn` (the `Expr.isExternFnAstB` guard; bridge lemmas
  `typecheckFn_ok_eq` / `typecheckFn_ok_not_externFnAst` replace the old
  `simp [typecheckFn]; cases` inversions that the new `if` would break);
- the guard `¬ Expr.IsExternFnAst body` is added to **two** value relations —
  `deepValueQTypProperty.closure` (`LeanProofs/RegimeConsistency.lean`) and
  `agreeValueUnder.clean_internal_arrow` (`LeanProofs/FaultRobustness.lean`).

With these, the two producer sites in `StepFRApp.lean` (the masked-consumer
application case and the paired-run `stepFR_app_arrow_runtime_extern_source_*`
lemma) close by `absurd Expr.IsExternFnAst.mk _`, and the only externFn-bodied
closures reaching the boundary are genuine `FnTClosure.extern` dispatches via
`closure_extern` → `Call.fnExternMember`.

### Public top-level FR theorem shapes: unchanged

`TypeSystemEnforcesFaultRobustness` (FaultRobustnessProofs.lean:3335), `…_at`,
`FaultRobustnessSpec`, `FaultRobustnessSpecForCtx`, and `ExternBoundarySpec`
reference the contracts **by name** and never unfold `ExternCallBoundaryFR` or
match on `Call`. Narrowing the contract *definitions* leaves every public
signature byte-identical.

### File churn (as delivered)

- `ExternBoundary.lean` — removed `fnRegularExternBody` from `Call`; the two
  contract definitions were left textually unchanged (they already quantify over
  `Call`).
- `Typecheck.lean` — `typecheckFn` rejects externFn-bodied lambdas
  (language-surface change); added bridge lemmas `typecheckFn_ok_eq` /
  `typecheckFn_ok_not_externFnAst`.
- `Syntax.lean` — added `Expr.isExternFnAstB` and its correspondence lemmas.
- `RegimeConsistency.lean` — guard on `deepValueQTypProperty.closure`.
- `FaultRobustness.lean` — guard on `agreeValueUnder.clean_internal_arrow`
  (appended last so positional inversions auto-name it).
- `StepFR.lean`, `StepFRFnPfn.lean`, `JoinMemberTransport.lean` — thread the new
  guard through the ~8 `clean_internal_arrow` construction sites.
- `TypeSafety.lean` — `valueHasETyp.closure` is **not** guarded; the
  typecheck→value-typing bridge sites switch to `typecheckFn_ok_eq`.
- `StepFRApp.lean` — collapse both producer sites via the guards; remove
  `ExternCallBoundaryFnStaticSource.regularExternBody` and its ~14 inversions;
  narrow `externCallFnTypingProvider_of_selected` and the static-source plumbing
  lemmas; remove the (now-vestigial) `hregularExternBody` hypothesis from the
  fn call-boundary chain.
- `ExternProofs.lean` (six `_call_clean_shape` helpers) and
  `ExternBoundaryConstructors.lean` — drop the now-nonexistent
  `Call.fnRegularExternBody` inversion branches.
- `ExternBoundaryProofs.lean` — `of_typecheckFn` uses the bridge lemma instead of
  the old `simp [typecheckFn]; cases`.
- `examples/` + `poison-lang-spec/poison-lang.ott` +
  `doc/poison-lang-description.tex` — the negative example
  `extern_fn_bare_extern_body_reject` and positive `extern_fn_nonbare_body_accept`,
  the `not_extern_fn` side condition on the Ott `fn_abs` rule, and the prose note;
  `make test` green (116/116). Ott and doc PDFs regenerated.
- A concrete trusted `kind = .fn` spec instance plus a program-FR artifact are now
  delivered (Checkpoint B — see "First trusted `kind = .fn` spec" below).

### First trusted `kind = .fn` spec (Checkpoint B — delivered)

With the contract narrowed, the first trusted `kind = .fn` `ExternBoundarySpec`
is now built — the milestone that the obstruction above had blocked since the
captures work.

- **The extern.** `LeanPoison/ExternBuiltins.lean` adds `impureIdImpl` (`@13`,
  `impure_id n : (int) -> int`), the minimal impure extern: it returns its
  integer argument and threads memory/`nextAddr` **unchanged**. It is registered
  in `defaultInitialState` alongside the existing built-ins.
- **Why this extern first.** A no-memory-effect fn extern makes
  `ExternCallFnFacts.output_config` collapse to `cf = callConfig` exactly as on
  the pure side, so `callFR`/`callSingle` mirror `builtinAbs` modulo the
  `fnExternMember`/`ExternCallFnFacts` inversion, and `operational`'s `fn` clause
  is discharged by `nextAddr` reflexivity plus `wfValue` of the `num` result. The
  memory-effecting fn built-in `set_err` (`@22`) writes a fixed `errnoAddr` *above*
  the allocation cursor, so its `ExternOperationalSafe` is false as a universal
  statement (the `errnoAddr ∉ mem ∧ addr ≤ errnoAddr` instantiation) — it is
  therefore a deliberate follow-up, not the first spec.
- **The spec.** `ExternProofs.builtinImpureIdSpec : ExternBoundarySpec
  builtinImpureIdDecl builtinImpureIdImpl` proves all five fields
  (`builtinImpureId_{declFR,callFR,declSingle,callSingle}` and
  `builtinImpureIdImpl_operationalSafe`), mirroring the `builtinAbs*` pfn template
  with the `fn`/arrow/`closure` constructors. It is axiom-clean (`propext`,
  `Classical.choice`, `Quot.sound` only).
- **Program-FR.** `LeanProofs/FnExternFR.lean` provides the bare-declaration
  `fnExtern_FR` and the applied `appliedFnExtern_FR` (program
  `(extern fn @13 …) 7`, whose derivation routes the application through
  `builtinImpureIdSpec.callFR` — the first relational `fn` call boundary), via
  `TypeSystemEnforcesFaultRobustness_at` and a registry-agreement witness.
- **Example.** `examples/extern_fn_impure_id.poison` declares and applies `@13`
  end-to-end (`impure_id 7` returns `7`, memory unchanged).
- **Honest scope.** `@13` declares no `captures:` (`captures = []`) and has no
  effects (`effects = []`), so it exercises the `fn` call boundary and kind
  dispatch but **neither** read-dependencies **nor** memory effects. Two
  follow-ups: a captures-bearing fn spec (the Checkpoint A fn-capture machinery
  exists; mirror the pfn `builtinMax11CapturesSpec` chain) and a memory-effecting
  fn spec (breaks the `cf = callConfig` collapse).

### Verification that the boundary is not weakened

Key soundness obligation: **`regularExternBody` is unreachable for well-typed
values** — every `Value.closure x e env` admitted by the regular-member
value-typing route carries `¬ Expr.IsExternFnAst e`. Once it holds, the coverage
partition is exhaustive and disjoint:

- genuine extern dispatch (closure typed via `FnTClosure.extern`) → trusted
  boundary via `Call.fnExternMember` / `pfnExternMember`;
- application of a non-extern body → normal FR, whose witness
  `BevalAppSuccess.userFn` already requires `¬ IsExternFnAst body`, so it never
  overlaps the dispatch route;
- `fn x => extern fn @id` → rejected at typecheck, so no such value exists.

Every runtime extern dispatch (BigStep.lean:212) is then covered by exactly one
FR path; none is dropped — the narrowing removes a *dead* obligation rather than
hiding a *live* gap. The guards (`deepValueQTypProperty.closure`,
`agreeValueUnder.clean_internal_arrow`) and `userFn`'s `hNotExternAst` use the
*same* `Expr.IsExternFnAst` predicate (Syntax.lean), so the typing exclusion and
the runtime exclusion coincide.

### Risks and sequencing (as delivered)

- The two obligations were **co-delivered**: Obligation 1 alone introduces a
  `sorry` at the consumer; Obligation 2 alone breaks existing proofs.
- The `typecheckFn` restriction is an **observable language-surface change** —
  programs of shape `fn x => extern fn @id` stop typechecking — which is why this
  was a design decision, not a mechanical edit.
- The typecheck→value-typing bridge was settled first (the `typecheckFn_ok_eq` /
  `typecheckFn_ok_not_externFnAst` lemmas), then the guard was added and the
  contract narrowed, so the repo stayed at 0 `sorry` throughout.

### Guard placement (refinement discovered during implementation)

The early sketch proposed guarding `valueHasETyp.closure` and its masked mirror
`deepValueQTypProperty.closure`. Implementation showed the minimal *and*
sufficient surface is a different pair:

- `deepValueQTypProperty.closure` (`LeanProofs/RegimeConsistency.lean`) — needed
  to collapse the consumer that inverts `valueConsistentWithRegimeMasked` (the
  StepFRApp application case for an `extern fn`-bodied closure value).
- `agreeValueUnder.clean_internal_arrow` (`LeanProofs/FaultRobustness.lean`) —
  needed to collapse the **paired-run** producer
  (`stepFR_app_arrow_runtime_extern_source_from_internal_clean`), which routes
  through the clean-agreement relation, *not* through `deepValueQTypProperty`.
  Guarding only `deepValueQTypProperty.closure` leaves this producer unprovable.

`valueHasETyp.closure` is **not** guarded: it *receives* the guard by inverting
`agreeValueUnder.clean_internal_arrow` (the `JoinMemberTransport`
reconstruction), so it need not *carry* it. Guarding it instead would cascade the
new field across ~40 `agreeValueUnder` sites. The guard is appended as the last
field of `clean_internal_arrow` so positional inversions auto-name it; only the
~8 construction sites (all fed by a now-guarded `deepValueQTypProperty.closure`
inversion or the `typecheckFn` bridge) needed editing. The pfn side needs no
guard: `clean_internal_parrow` already carries `Expr.toPExpr? body = some pbody`,
structurally excluding `externPfn` bodies.

The dropped regular route is encoded downstream as `… ∨ False` in the three
`private` static-source plumbing lemmas in `StepFRApp.lean`
(`applyFnTClosure_staticSource_of_threaded_mem` and the two consumers), keeping
their call sites type-stable while making the route provably uninhabited; the
trusted `Call` relation itself is cleanly narrowed (no vestigial disjunct).

## Out of scope (this effort)

- **The "extra unlisted entry remains allowed" example.** This is useful
  documentation for the trusted-footprint model, but it is not needed to finish
  the core pfn read-dependency branch once the accepted/rejected dependency paths
  above are covered.
- **Trusted guarded-value producer and applied-program routing.** Call-time
  regime checking for guarded captures is implemented: the typechecker/call
  boundary can accept a captured value when the required regime evidence is
  active and reject it when inactive. What remains is a trusted producer extern
  that returns a guarded/de-poisoned value, plus an applied program-FR proof that
  routes `producer -> captured value -> consumer extern`. This is broader
  FFI/regime validation after this branch lands in `ffi`, not part of the
  pfn-side read-dependency mechanism itself.

## Branch merge rule

`extern-env-deps` is ready to merge into `ffi` with the standard gates green and
no new `sorry`/axioms: the pfn-side environment-read, guarded call-time
satisfaction, representative memory-read `!r`, branch-join capture conjunction,
and the first impure (`extern fn`) trusted spec + program-FR paths are all
implemented/proved.
Do not hold this branch for the trusted guarded-value producer/applied-program
routing work, a memory-effecting fn trusted spec (the no-effect `@13` spec is
delivered; an effectful one is a follow-up), or default-registry specs unrelated
to read dependencies.

## Constraints

- Repo is a **hard 0-`sorry` gate**: every checkpoint builds green with 0 sorrys.
- Build the shared spine sequentially (`Syntax → Typecheck → ExternRuntime →
  ExternBoundary → ExternProofs`); no concurrent builds of interdependent files.
- No commits without explicit user approval.
