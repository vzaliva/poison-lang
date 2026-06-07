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
read-dependency model is complete enough to match the goal document, including
branch-join capture conjunctions and memory-read dependencies. Guarded
dependencies are now implemented/proved to the same maturity level as extern
argument guards: typecheck/examples are end-to-end and the trusted call boundary
is proved. The remaining guarded-value work is a trusted producer extern plus an
applied program-FR proof that routes `producer -> captured value -> consumer`;
that is broader FFI/regime validation, not a blocker for this branch.

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

## Required before merging `extern-env-deps` to `ffi`

- **Branch-join conjunction merge for capture preconditions**
  (`JoinMemberTransport`; goal doc §"Contract Syntax and Variance"). Capture
  preconditions must combine by **conjunction** across branches (reject
  incompatible predicate shapes), not by the return-side join that collapses to
  `noPred`. Not exercised by `max` (no branches over a capture-bearing closure).
- **Memory-read (`!r`) dependencies, end-to-end** (the goal doc's `maxmem`
  `@20`/`@21` example or an equivalent). Bang targets already belong to the
  surface model and are checked at the extern call boundary against current
  memory typing. The branch should include a trusted spec / program-FR artifact
  exercising memory reads through captured reference variables and/or the
  reference-typed explicit argument, rather than leaving `!r` as parser-only or
  typechecker-only support.
- **Representative examples and rejection coverage.** The branch should keep the
  accepted curried-`max` and guarded examples and add coverage for the new
  memory-read path. At least one rejected missing/incompatible capture case
  should exist so the call gate's negative path is not only implicit in proofs.

## Out of scope (this effort)

- **fn-side captures** (`extern fn … captures:`). The `captures` field exists on
  the fn AST/closure for parity, but captures are threaded end-to-end through the
  **pfn** paths only; the `fn` reachability/`Decl`/`of_terminatesTo` variants are
  left at `[]`. No fn extern exercises captures.
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

Merge `extern-env-deps` into `ffi` only when the pfn-side `captures:` feature is
complete for environment reads, branch-join capture conjunctions, and memory-read
`!r` dependencies, with the standard gates green and no new `sorry`/axioms.
Guarded call-time satisfaction is already complete at the typecheck/trusted
call-boundary level; do not hold this branch for the trusted guarded-value
producer/applied-program routing work, fn-side captures, or default-registry
specs unrelated to read dependencies.

## Constraints

- Repo is a **hard 0-`sorry` gate**: every checkpoint builds green with 0 sorrys.
- Build the shared spine sequentially (`Syntax → Typecheck → ExternRuntime →
  ExternBoundary → ExternProofs`); no concurrent builds of interdependent files.
- No commits without explicit user approval.
