# Extern argument conditions — implementation plan

Status: **IMPLEMENTED** (all phases complete). The selected design in
[`extern-argument-conditions.md`](extern-argument-conditions.md) is fully
realised: parser/AST/typechecker/pretty/runtime, Ott spec + narrative docs,
executable examples (incl. a `sqrt`-style positive example and a precondition
violation), and the full FR proof tree. Verification: `lake build` succeeds
(11461 jobs), the repo is **0-`sorry`** and warning-free, `make test` passes
(101/0), the top-level `TypeSystemEnforcesFaultRobustness` statement is unchanged
and rests on the pre-existing axiom baseline. This file is the engineering plan
that drove the work (kept for provenance).

## Decisions fixed before implementation

1. **Unsatisfied precondition ⇒ reject at typecheck time** (not conservative
   re-typing). Every *successful* extern call has discharged its declared
   precondition, so the boundary proof may treat satisfaction as a clean
   implication rather than a case split. The doc language is tightened from
   "a failing or conservatively-typed call" to "a failing call" for v1.

2. **Representation split** (forced by the mutual-block structure of
   `Syntax.lean`):
   - **AST** carries the precondition as a *symbolic surface triple*
     `Typ → Bool → SyntaxPredicate`, mirroring `ExternReturn.simple`. A literal
     `QTyp` on an `Expr` constructor would form the cycle
     `Expr → QTyp → ETyp → FnTClosure → Expr` and the parser cannot synthesise
     a concrete `QTyp` (tags/locs are allocated only at typecheck time).
   - **Typing closures** (`FnTClosure.extern` / `PFnTClosure.extern`) gain a
     concrete `QTyp` precondition field — the home consulted at the call site.
   - **Proof summary** (`ExternDeclaration`) gains `argQTyp : QTyp`
     *alongside* the existing `typ : Typ` (keep `typ` so `valueMatchesTyp` and
     the reachability `…MatchesFn/Pfn` predicates are untouched).
   - The `ETyp.arrow` / `ETyp.parrow` domain stays a bare `Typ` (shared with
     native `fn`/`pfn`); the precondition rides on the closure, not the arrow.

3. **Conservative satisfaction relation** `argConditionSatisfied declared actual R`:
   1. base runtime types match (`etyp` signature);
   2. declared **clean** ⇒ actual **clean under regime `R`**
      (`actual.poison = false`, or `actual.pred` is a guard whose tag is active
      in `R`);
   3. declared **no predicate** ⇒ no predicate match required;
   4. declared **predicate** ⇒ actual carries the **same predicate shape**
      (guard *body* equal modulo tag and binder, via `PExpr.equalWithEnvs`);
      **no** general logical implication.
   - In the typechecker this is a `Bool` helper that `throw`s on failure,
     applied in all four extern/simple application branches (cursor and
     non-cursor × fn/pfn) *before* the declared (clean) result is produced.

4. **Clean-with-predicate is legal in argument position only.** The doc's
   motivating form `(int :> clean { 1, v => v >= 0 })` is clean *and* predicated.
   The existing "clean types cannot have predicates" guard
   (`Parser.lean` `xmlToQTyp`, `Typecheck.lean` `surfaceSpecToQTyp`, Ott
   `extern_wf`) must be **scoped to return/value/effect** positions; argument
   `QTyp`s skip it.

5. **Examples rewrite is per-call, not blanket.** Because the grammar now forces
   a `qtyp` on every extern argument and the typechecker rejects unsatisfied
   preconditions:
   - call passes a **clean** value (literal/clean computation) ⇒
     `(int :> clean {})`;
   - call passes a **poisoned/derived** value ⇒ `(int :> poisoned {})` — the
     explicit "accepts any int, no precondition" form (declared-poisoned skips
     the cleanness clause; `noPred` skips the match clause).
   Blanket `clean {}` would flip poison-propagation `.output`/`.fail` tests into
   vacuous parse/reject failures. `(int :> poisoned {})` is the documented
   "untrusted / no real precondition" convention.

6. **`abs` (@12) / `max` (@10,@11) become honest, not removed.** Declared with
   `(int :> clean {})` they only accept clean arguments; their existing
   call sites pass clean values, so `.output` is preserved and the
   dirty-input dishonesty is now a typecheck rejection. They remain outside any
   trusted registry instantiation (FR not derived), unchanged from today.

## Scope decisions (resolved by the user, 2026-06-02)

- **A — Proof-side depth: CONDITIONED (doc-faithful).** Add the satisfaction
  hypothesis to the **trusted-spec call obligation** (`ExternCallBoundaryFR` /
  `ExternCallBoundarySingle`), and discharge it in `StepFRApp` from the
  typechecker's enforcement. For the only trusted spec
  (`PureUnaryCleanIntSpec`, clean-int) this is the **clean-flag inversion only**;
  the predicate-shape clause stays typechecker-only (sqrt is untrusted), so it
  cannot force a proof `sorry`.
- **B — Nested/curried preconditions: ENFORCE AT EVERY CURRIED LEVEL.** The
  satisfaction check fires at every extern application against the applied
  closure's `argQTyp` (uniform across simple- and nested-return branches in the
  four typechecker apply functions, and across all nine Ott application rules).

## Phased implementation (green-keeping; high-risk first within each phase)

The repository builds the whole transitive closure with `lake`; **no concurrent
builds**. Per-operator FR files are independent, but the extern change lives in
shared modules, so the proof phase is sequential.

- **Phase 0 — Author the `sqrt` positive example first** as the integration
  target. Uses the `--extern-regime "<id>=true"` + downstream `fd >= 0` check
  pattern (cf. `examples/extern-regime-open.poison`) to produce an argument that
  is clean-under-regime *and* carries guard `v >= 0`, satisfying a
  `(int :> clean { 1, v => v >= 0 })` precondition. Pin down the predicate-shape
  comparison (store declared arg as a concrete `QTyp`; compare guard *bodies*
  modulo tag/binder).
- **Phase 1 — `Syntax.lean`.** AST triple on `externFn`/`externPfn` /
  `nestedFn`/`nestedPfn`; `QTyp` field on `FnTClosure.extern`/`PFnTClosure.extern`;
  update `beqExpr`/`beqExternReturn`/`beqFnTClosure`/`beqPFnTClosure`,
  `IsExternFnAst`/`IsExternPfnAst`.
- **Phase 2 — Parser.** `grammar.js` lines 220/235 `paren_type → qtyp`
  (nested covered automatically); `make parser`; `Parser.lean` six arg sites
  `paren_type → qtyp` via an **arg-permitting** `xmlToQTyp` (skips the
  clean-pred guard for arguments only).
- **Phase 3 — `Typecheck.lean`.** `typecheckExternFn`/`Pfn` accept the surface
  triple, resolve it to a concrete arg `QTyp`, store on the closure; keep
  `ETyp.arrow (QTyp.toTyp argQt) …`. Add `argConditionSatisfied` (+ a
  regime-clean helper); gate the four extern/simple branches with a `throw` on
  failure. Thread the declared inner arg `QTyp` into nested inner-`tcl` rebuilds.
- **Phase 4 — `Pretty.lean`.** One shared `qtypSurfaceInline` helper; four arg
  render sites (+ closure render sites now that closures carry the QTyp);
  refactor the two return sites onto the same helper.
- **Phase 5 — Examples + goldens.** Per-call rewrite rule (§5 above) across the
  ~25 break-set files; honest `abs`/`max`; add `sqrt` positive (Phase 0) and an
  `extern_arg_precond_violation` `.fail`; `make parser` then
  `./scripts/update-tests.sh`; review every diff for silent parse-error `.fail`s.
- **Phase 6 — Ott + narrative docs.** `poison-lang.ott`: arg `ST → Q` on the
  four productions; `Q` field on `extern_tcl`/`extern_ptcl`; new regime-aware
  `satisfiesArgCond` formula schema (abstract, like `<:`); add the premise to
  the nine application rules after `TM` allocation + the `x ↦ …` substitution;
  keep `extern_spec_wf` scoped to returns/effects. Update
  `doc/poison-lang-description.tex` arg examples and add an
  argument-precondition subsection.
- **Phase 7 — Proofs.** Per decision **A** (conditioned). `ExternDeclaration.argQTyp` field +
  ~14 literal sites; reconstruct from the closure member at
  `arrow_extern_member`/`parrow_extern_member` and the `argTyp = st1` sites;
  define `ArgConditionSatisfied` as an inductive `Prop`; update
  `PureUnaryCleanIntSpec`. Keep `builtinAbs_cleanPost_obstruction` and
  `ExternTypingAssumptions` untouched. **Hard gate: repo stays 0-`sorry`.**
- **Phase 8 — Close out.** Tighten `extern-argument-conditions.md` wording to
  "a failing call"; `make test`; `lake build`; confirm 0-`sorry` and no new
  warnings; update `extern-poison.md` status note.

## Hard invariants / regression gates

- Repository is currently **0 `sorry`** (verified repo-wide). No new `sorry`.
- Keep cursor and non-cursor extern application branches byte-for-byte parallel.
- Do not touch the `ETyp.arrow`/`parrow` domain `Typ` (native `fn`/`pfn`).
- Return / `extern val` / effect `QTyp` semantics are **unchanged**: return
  predicates stay output de-poisoning markers, never caller preconditions.
- Per-operator FR file independence (`StepFR*` files don't import each other).
