# Implementation Plan: `captures:` extern read dependencies

Implements `doc/extern-env-deps.md`. Branch: `extern-env-deps`.

This plan is ordered **risk-first**, not layer-first. The only genuine unknown is
whether captured-dependency agreement closes the relational `@11` (inner curried
`max`) call-boundary proof. Everything else (grammar, parser, Ott, tex, examples,
typecheck enforcement) is mechanical and known-doable. So the crux proof is
validated before the surface syntax is built.

## Validated design (the crux)

`@11`'s `callFR` is the obligation that the abstract extern summary cannot
currently discharge: `@11` returns `max a b` reading captured `a`, but inverting
`ExternBoundaryTyping.Call.pfnExternMember` yields the captured type env `tenv`
*existentially*, with no fact that `a ∈ tenv` clean.

**Mechanism** (confirmed against the code):

- `ExternCallBoundaryFR` already hands the proof `BodyEntryInputsAgree`, whose
  `.agree` field is `agreeOnClean` over the **body-entry context**
  (`ctx = entry.bodyCtx`, whose `varEnv = update (ofCaptured tenv) x …`).
- If a `captures` contract pins `a` clean in that context, `agreeOnClean`
  delivers `a₀ = a₁` for free (clean ints agree across runs), exactly as the abs
  `callFR` already does for the *argument* via `builtinAbs_arg_eq_of_bodyAgree`
  → `agreeValueUnder_num_int_imp_eq`.
- The capture fact is sourced **from `happly`**: the capture check lives *inside*
  `applyPFnTClosure(AtCursor)`, so `happly = .ok` (already a premise of
  `Call.pfnExternMember`) entails "each declared capture resolves clean." No new
  `Call` premise to discharge at construction sites; no bridge surgery for the
  clean path.
- `captures` threads exactly like the existing `effects` field does on the fn
  side: decl field → closure field → `Call` premise `d.captures = captures` →
  registry match → reachability. The pfn side has no `effects` precedent, so the
  field is added fresh to `PFnTClosure.extern` and its Call/match/reachability
  handling.

## Phases (each ends green at 0 `sorry`)

- **Phase 1 — inert data.** `CaptureTarget` (`bareVar`/`memVar`), `Capture`
  (`target`, `typ`, `poison`, `pred`) in `Syntax.lean`; `captures : List Capture
  := []` on `ExternDeclaration` (structure field with default → no ripple to its
  named-field constructions). Build green.
- **Phase 2 — crux.** `captures` field on `PFnTClosure.extern` only (`max` is a
  pure extern; `FnTClosure.extern` captures deferred to Phase 4 to halve the
  ~270-site closure ripple — no fn extern uses captures yet); call-time
  capture check in `applyPFnTClosure(AtCursor)`; thread `d.captures = captures`
  through `Call.{pfn,fn}ExternMember`, the StepFRApp providers, the registry
  match, and pfn reachability; repair the ripped closure lemmas
  (`valueHasETyp.peClosure_extern`, `deepValueQTypProperty.peClosure_extern`,
  `agreeValueUnder.clean_internal_parrow_extern`, `JoinMemberTransport`); set
  `builtinMax11Decl.captures := [a :> (int :> clean {})]`; prove
  `builtinMax11_callFR`; assemble `builtinMax11Spec`. Build green.
- **Phase 3 — program-level `@10`.** `@10` decl/impl + five `ExternBoundarySpec`
  fields, with `@10.callFR` returning the capture-bearing `@11` closure (applying
  `@10` to clean `a` is what *introduces* the `captures=[a]` contract). Wire
  `max_curried` end-to-end through the trusted registry. Build green.
- **Phase 4 — surface + enforcement.** AST `captures` on `Expr.externFn/Pfn` and
  `ExternReturn.nested{Fn,Pfn}`; `parser/` grammar + `LeanPoison/Parser.lean`;
  `Typecheck.lean` enforcement (resolve + check + store + reject) populating the
  closure `captures` from the AST; `JoinMemberTransport` conjunction-merge for
  capture preconditions; `examples/`; `poison-lang.ott`; `poison-lang-description.tex`.
  Build green; `make test` green.

## Deferrals / divergences (named, so "done" is unambiguous)

- **DIVERGENCE from the doc (capture-check timing).** The doc checks *bare*
  environment captures at the **declaration / nested-return** site
  (`extern-env-deps.md` §"Intended Typechecking Meaning", §"Guarded
  Dependencies"). This plan checks them at the **call boundary** (inside
  `applyPFnTClosure`), because that is what makes `happly` carry the fact with no
  bridge surgery. This is **sound only for the unguarded-clean path**: clean is
  regime-insensitive, so capture-time vs call-time regime cannot differ for a
  clean requirement. `max` is all-clean, so it is unaffected.
- **DEFERRED — guarded captures.** A guard active at capture time need not be
  active at call time (`extern-env-deps.md` lines 330–339). Guarded capture
  support requires the `TrustedRegistryAgreesWithReachable` regime reconciliation
  and is deferred, to be discharged **per-builtin-spec** rather than as an
  abstract obligation over all reachable closures. Not on `max`'s critical path.
- **DEFERRED — `effects:`-style fn captures end-to-end.** The `captures` field is
  added to `FnTClosure.extern` for type-system parity, but no fn extern exercises
  it until Phase 4.
- **"Done" boundary.** The `@11` `callFR` lemma in isolation is **not**
  `max_curried` FR-robust. Program-level robustness needs Phase 3 (`@10`) and
  Phase 4 (AST/parser so a real program's reachable decl carries `captures=[a]`
  and the bridge matches it to the registry entry).

## Progress

- **Phase 1 — DONE (green, 0 sorry).** `CaptureTarget`/`Capture` in `Syntax.lean`;
  `ExternDeclaration.captures := []`.
- **Phase 2 plumbing — DONE (green, 0 sorry, 102/102 tests).** `captures` field
  on `PFnTClosure.extern`; combined call-time gate
  `argConditionSatisfied && capturesSatisfied` in `applyPFnTClosure(AtCursor)`;
  `d.captures = captures` premise threaded through `Call.pfnExternMember`,
  `TrustedRegistryEntryMatchesPfn`, the StepFRApp providers, and pfn reachability.
  Closure-property inductives (`valueHasETyp`/`deepValueQTypProperty`/
  `agreeValueUnder.clean_internal_parrow_extern`) fixed at `captures=[]` (no closure
  *value* carries non-empty captures; only the trusted *decl* does).
- **Phase 2 crux — DONE (green, 0 sorry, 102/102 tests).**
  `ExternProofs.builtinMax11_callFR : ExternCallBoundaryFR builtinMax11CapturesDecl
  builtinMax11Impl` is proved (axioms: only `propext`/`Classical.choice`/`Quot.sound`
  — no `sorryAx`). It uses the captured-`a` dependency: inverting
  `Call.pfnExternMember` for `builtinMax11CapturesDecl` (captures `[a]`) extracts,
  from the combined call gate, that captured `a` is a clean integer in the
  body-entry environment; body-entry `agreeOnClean` then forces `a₀ = a₁`, the
  argument gate forces `b₀ = b₁`, and `max a₀ b₀ = max a₁ b₁` discharges the
  relational `StepFRPost` conjunct.
  - **Decl-tension resolution (per advisor):** `captures=[a]` is on a *separate*
    `builtinMax11CapturesDecl`; `builtinMax11Decl` (captures `[]`) and its proven
    declFR/declSingle/callSingle/operational are untouched. The crux deliverable
    is the standalone `callFR` *lemma* — not an assembled full `ExternBoundarySpec`.
    Neither decl gets a full spec this session, and that is correct: the captures=[]
    decl cannot close callFR (that was the gap), and the captures=[a] decl's
    top-level declFR is genuinely vacuous until the AST carries captures
    (Phase 4).

- **Phase 3 — surface AST ripple DONE (green, 0 sorry, 0 warning, 102/102 tests).**
  `captures` field added to all four AST nodes (`Expr.externFn`, `Expr.externPfn`,
  `ExternReturn.nestedFn`, `ExternReturn.nestedPfn`) and threaded through the entire
  proof stack. `typecheckExternPfn` accepts a `_captures` parameter that is
  **currently unused** (the closure stores `captures=[]`); real population is
  deferred to `@10`/program-level FR, since it is not separable from generalizing
  the value track (storing non-`[]` captures breaks `valueHasETyp.peClosure_extern`).
  Per the **two-track captures discipline**:
  - **Value/typing track stays `[]`** — closure *values*, the `PFnTClosure.extern`
    member produced by `typecheckExternPfn` (forced by `valueHasETyp.peClosure_extern`'s
    `[]`-pinned `htcl`), `Decl.fn/pfn`, `ExternDeclarationInProgram`, and reachability
    are all `captures=[]`. A closure value's *body* externPfn carries a free
    existential `captures`, decoupled from the `[]` member.
  - **Runtime/Call track threads a variable `captures`** — `ExternBoundaryTyping.Call`,
    `ExternCall{Fn,Pfn}TypingProvider` (existential `captures` in the `Call`),
    `of_terminatesTo_extern{Fn,Pfn}` (via the freed `value_shape`, whose closure-body
    captures is now a free existential like `argPred`), and the `@externFn/@externPfn`
    case binders.
  - `abs @12` / `max @11` decl-spec helpers (`builtin{Abs,Max11}_decl_*`) thread
    the free value-body `captures`; their `…DeclResult`/`…ExternClosure`
    PFnTClosures stay `[]`.
  - top-level FR theorem + `builtinMax11_callFR` remain `sorryAx`-free.
- **Phase 3 — parser DONE (green, 102/102 tests).** Real `captures:` parsing wired:
  grammar (`captures_block` / `capture` rules, bare `a` → `env_name` and bang `!x`
  → `mem_name` targets) on both `extern_fn` and `extern_pfn`; `Parser.lean`
  `xmlToCaptures` (reads the `field` attr to pick `CaptureTarget.bareVar`/`.memVar`)
  and a `findExternBlock` tag-scan refactor that collapses the per-clause positional
  cases (so `effects`/`captures` are found by tag in any order, across
  fn/pfn/nestedFn/nestedPfn); `Pretty.lean` emits a `, captures: { … }` suffix
  (non-empty only). Verified by a parse→`Repr` round-trip of a program with both
  `!r1` and `a` capture targets. **Captures are still inert at typecheck** (stored
  `[]`), so they parse into the AST but do not yet affect typechecking or runtime;
  meaningful runnable examples need `@10` (the runtime nested-return validation
  currently `beqExpr`-compares captures, coupling a program's declared nested
  captures to the impl's — its relaxation/population is `@10` work).

## Findings from the `@10` / population investigation (spike, reverted green)

A controlled spike (flip `typecheckExternPfn` to *store* captures, rebuild, read
first errors) established two things that re-scope `@10`:

- **Typecheck population is unnecessary AND costly — do NOT populate.** The crux
  `builtinMax11_callFR` reads `[a]` off the hand-built trusted decl
  `builtinMax11CapturesDecl`, and the registry bridge matches it to the reachable
  closure *without comparing captures* (`TrustedRegistryEntryMatchesPfn` does not
  pin captures). So captures live on the **trusted-decl / Call track**, never
  on a
  typecheck-produced `PFnTClosure`. Populating forces generalizing the three
  value-track inductives (`valueHasETyp`/`deepValueQTypProperty`/`agreeValueUnder`
  member `[]`→`cap` — cheap, a 1-line ripple) AND re-tying the `value_shape`
  captures that was deliberately *freed* (to keep `of_terminatesTo` at `[]`), which
  breaks the abs/max11 spec unification. Population and freed-`value_shape` are
  mutually exclusive; freed-`value_shape` is load-bearing for green. Verdict:
  captures realize via trusted decls, typecheck stays `[]`.
- **`@10`'s own captures is `[]`.** Per the doc worked example, `a` is captured
  by
  the inner `@11` (from `@10`'s argument); `@10` merely *returns* the `@11`
  closure. So `@10` is a closure-returning decl, not a captures-bearing one;
  `@10.callFR`'s job is to produce an `@11` closure whose trusted decl carries
  `[a]`. The `@11` closure body itself is `[]`-captures (from `outerMaxImpl`), so
  `@10.callFR`'s closure-agreement is at `[]` and likely does **not** force
  `agreeValueUnder` generalization (only the `@11` *call* uses `[a]`, already
  proved).

## DONE — program-level FR for `max_curried` with nested `captures:` (option (b))

The program-FR connection that the earlier `@10`-spec session reported as a
design fork has been **resolved and proved**. What was once "blocked on the
two-track tension" is now `MaxCurriedFR.maxCurried_FR` (sorry-free,
axiom-clean modulo the pre-existing `native_decide`). The chosen path was
**option (b): decouple the two tracks** (the contract captures vs the runtime
body-AST captures), plus **option B for the runtime check**. Resolution, in the
order it was built (commits `dc43938`, `b631c0e`, `20a20c3`, `ed19340`,
`5583bfb`):

1. **Capture-generic FR/trust/reachability stack** (`dc43938`). The value-track
   lemmas (`valueHasETyp`/`deepValueQTypProperty`/`agreeValueUnder`) gained an
   **independent `memberCap`** parameter (the type member's captures, the gate),
   decoupled from the closure body's `cap` — value\_shape-safe (the prior spike's
   failure was the *coupled* form). `Call.pfnExternMember` gained a `bodyCaptures`
   decoupled from the contract; `ExternCallBoundaryPfnStaticSource` /
   `callBoundaryRun` / `ExternCallPfnTypingProvider` thread `memberCap`.
2. **Captures population, one value per id = source contract** (`b631c0e`).
   `typecheckExternPfn` now **stores** the source captures on the closure member,
   `applyPFnTClosureAtCursor`'s nestedPfn branch **propagates** `innerCaptures`,
   and every reachability/typing/runtime synthesis point carries it
   (`ExternDeclarationInProgram.externPfn`, `ExternDeclarationInReturn.nestedPfn_here`,
   `ExternBoundaryTyping.Decl.pfn`, `of_terminatesTo_externPfn`). So the typecheck
   population that was thought "costly / mutually exclusive with value\_shape" is
   in fact available *because* the value track is independent-member.
3. **`@10` `[a]` path + runtime option B** (`20a20c3`). `builtinMax10RetSpec`
   nests `@11` with `captures [a]`; the `@10` call produces the `@11` closure with
   type member `[a]` (the gate). `validateExternReturn` now compares a nested
   return's produced closure **modulo captures** (`exprBodyCaptures`): the body-AST
   captures is the runtime shape, the contract is enforced separately at the call
   gate — so the inner closure's body need not carry the declared captures. This
   is gated to captures-bearing nested returns (`captures = []` ⇒ byte-identical;
   no regression). The nested-captures example now runs.
4. **`builtinMax11CapturesSpec`** (`ed19340`): the full 5-field
   `ExternBoundarySpec` for the capture-bearing `@11` decl.
5. **`MaxCurriedFR.maxCurried_FR`** (`5583bfb`): the registry
   `[⟨builtinMax10Decl, …⟩, ⟨builtinMax11CapturesDecl, …⟩]` agrees with the
   reachable decls (`@10` `captures []`, `@11` `captures [a]` via `nestedPfn_here`),
   discharging `TrustedRegistryAgreesWithReachable`; composing with
   `TypeSystemEnforcesFaultRobustness_at` yields program-level FR.

**Scope of `maxCurried_FR` (honest framing).** `maxCurriedProg` is the `@10`
declaration node (mirroring the `openProg` template), not the applied
`(m 7) 2`. So `maxCurried_FR` proves that the **registry-agreement obstruction is
removed** — the capture-bearing `@11` decl is now both *reachable* and the
*FR-capable* registry entry (the `rfl` matching `[a]` to `builtinMax11CapturesDecl`
is the non-trivial content; swapping in the `[]` decl fails to compile). The
captured-`a` cleanness (`builtinMax11_callFR`) is reachable but not *exercised*
by this bare-declaration program — dynamic end-to-end materialisation is the
separate, larger §4.6 work, exactly as the `open_empty_context_FR_instantiable`
template notes for its own case.

## Known incompleteness (recorded so it isn't a surprise)

- **fn-side asymmetry.** Captures are threaded through the **pfn** reachability,
  `Decl`, and `of_terminatesTo` paths; the **fn** variants (`extern fn … captures:`)
  are intentionally left at `[]` (the curried-`max` motivating case is pure).
- The Ott `extern_tcl` / `extern_ptcl` closure forms **elide `CSL` for
  presentation**; the implementation carries it on the closure member (see the
  updated comment at the `extern_fn` typing rule and the description prose).

## Constraints

- Repo is a **hard 0-`sorry` gate**: every checkpoint builds green with 0 sorrys.
- Build the shared spine sequentially (`Syntax → Typecheck → ExternRuntime →
  ExternBoundary → ExternProofs`); no concurrent builds of interdependent files.
- No commits without explicit user approval.
