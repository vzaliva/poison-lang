# Implementation Plan: `captures:` extern read dependencies

Implements `doc/extern-env-deps.md`. Branch: `extern-env-deps`.

The driving case is curried `max`: the inner `@11` reads the captured outer
argument `a`, which the abstract extern call-boundary proof could not previously
justify as a clean dependency. That curried-`max` (all-clean) path is now
**implemented and proved end-to-end**. The remaining goal-doc surface (guarded
dependencies, memory-read dependencies, fn-side captures, branch-join merges, and
the corresponding examples) is documented below as deferred / out of scope.

## Status — curried-`max` path: DONE (end-to-end, fully proved)

Final state: `lake build` green (11464 jobs), `make test` 104/104, repo-wide
0 `sorry`, 0 warnings. Axiom status (precise): this work adds **no `sorry` and no
new axioms**. The new boundary specs and the `defaultRegistry_lookup_*`
interpreter-registry lemmas are axiom-clean (`propext`/`Classical.choice`/
`Quot.sound` only). `maxCurried_FR` / `appliedMaxCurried_FR` /
`TypeSystemEnforcesFaultRobustness` inherit the FR step stack's **pre-existing**
`native_decide` axioms (from `StepFRIte.lean` / `StepFR.lean` /
`FaultRobustnessProofs.lean`, untouched by this work) — eliminating those is a
separate, opt-in task and is not part of the `captures:` effort.

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

## Deferred (sound, not on the curried-`max` critical path)

- **Guarded dependencies + regime reconciliation** (goal doc §"Guarded
  Dependencies"). A guard active at capture time need not be active at call time.
  Supporting guarded captures needs the regime reconciliation in the
  `TrustedRegistryAgreesWithReachable` bridge (reusing the
  `closureCapturedVarsRegime`/`consistentWithRegime` transport), discharged
  per-builtin-spec. Curried `max` is all-clean, so it is unaffected.
- **Capture-check-timing divergence.** The implementation checks bare environment
  captures at the **call boundary** (inside `applyPFnTClosure`), whereas the doc
  checks them at the **declaration / nested-return site**. This is sound only for
  the **unguarded-clean** path (clean is regime-insensitive, so capture-time vs
  call-time regime cannot differ). Reconciling the two for guarded captures is the
  same work as the item above.
- **Branch-join conjunction merge for capture preconditions**
  (`JoinMemberTransport`; goal doc §"Contract Syntax and Variance"). Capture
  preconditions must combine by **conjunction** across branches (reject
  incompatible predicate shapes), not by the return-side join that collapses to
  `noPred`. Not exercised by `max` (no branches over a capture-bearing closure).
## Out of scope (this effort)

- **Memory-read (`!r`) dependencies, end-to-end** (the goal doc's
  `maxmem` `@20`/`@21` example). Bang targets parse into the AST and
  `capturesSatisfied` has the bang case, but no trusted spec or
  program-FR is built for a memory-read extern (memory deps are
  checked at the call boundary against memory typing — call-time, so
  no reconciliation needed, but the proof artifact is deliberately not
  built at this time).
- **fn-side captures** (`extern fn … captures:`). The `captures` field exists on
  the fn AST/closure for parity, but captures are threaded end-to-end through the
  **pfn** paths only; the `fn` reachability/`Decl`/`of_terminatesTo` variants are
  left at `[]`. No fn extern exercises captures.
- **Additional examples from the goal doc**: rejection of missing/incompatible
  captures, memory-read dependencies, and the "extra unlisted entry remains
  allowed" case. Only accepted-capture examples are added.
- **Dynamic §4.6 de-poisoning materialisation.** This concerns the
  guarded/poisoned scenario (materialising a de-poisoned value at runtime), not
  curried `max`, which is all-clean. The curried-`max` applied FR is complete
  without it.

## Constraints

- Repo is a **hard 0-`sorry` gate**: every checkpoint builds green with 0 sorrys.
- Build the shared spine sequentially (`Syntax → Typecheck → ExternRuntime →
  ExternBoundary → ExternProofs`); no concurrent builds of interdependent files.
- No commits without explicit user approval.
