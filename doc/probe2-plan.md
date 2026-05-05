# Probe 2 Plan: Boundary Contracts for FFI Dispatch

## Status

**Probe 2 has not been started.** This document records the planning and a vertical-slice spike that demonstrated the boundary-contract infrastructure is **not** required to clean up the six app-proof gaps Probe 1 left behind. Those gaps were discharged as part of Probe 1 cleanup, not as Probe 2 acceptance.

The real Probe 2 work — `ExternBoundarySpec`, `TrustedRegistry`, `StepFRPost`, `ExternCallEntry`, `ExternCallBoundaryRun`, `TrustedRegistryAgreesWithProgram`, and the registry-relative top-level theorem — remains future work. It is on the critical path for Probes 4–5 (concrete `abs` driver, `@10`/`@11` curried `max`) where extern dispatch becomes reachable.

## What the Spike Demonstrated

Probe 1 added `valueHasETyp.{closure,peClosure}_extern` constructors. Lean's exhaustivity check then forced six new `closure_extern` / `peClosure_extern` arms in `LeanProofs/StepFRApp.lean` — initially stubbed with `sorry` and intended to be the discharge target for Probe 2's boundary contracts.

The vertical slice tested whether those discharges actually need the boundary-contract layer. They do not. All six closed via local-hypothesis vacuity arguments using inputs that `terminatesTo_app_inv'` and `terminatesTo_preserves_registry` already supply.

| Site (original line) | Lemma | Closure kind | Vacuity argument |
|---|---|---|---|
| 2342 | `stepFRSingleRunFinalCleanPcTrue_app_arrow_parametric_maskedReg` | `closure_extern` | empty-registry → `beval` on `Expr.externFn` fails |
| 2976 | `stepFRSingleRunFinalCleanPcTrue_app_parrow_parametric_maskedReg` | `peClosure_extern` | `Expr.toPExpr? body ≠ none` from `_htoPExpr_body` becomes `none ≠ none` |
| 3622 | `stepFR_app` (arrow case, side 0) | `closure_extern` | empty-registry chain via `terminatesTo_preserves_registry` |
| 3627 | `stepFR_app` (arrow case, side 1) | `closure_extern` | empty-registry chain via `terminatesTo_preserves_registry` |
| 6299 | `stepFR_app` (parrow case, side 0) | `peClosure_extern` | `Expr.toPExpr?` mismatch via `htoP₀` |
| 6304 | `stepFR_app` (parrow case, side 1) | `peClosure_extern` | `Expr.toPExpr?` mismatch via `htoP₁` |

Two distinct patterns:

**Parrow vacuity (3 sites, ~1 line each).** `peClosure_extern` constructor unifies `body = Expr.externPfn id y argTyp retSpec`. `terminatesTo_app_inv'`'s peClosure case carries `Expr.toPExpr? body ≠ none` because the runtime requires the body to be PExpr-convertible to enter the pure-call branch. `Expr.toPExpr?` returns `none` for `externPfn` (default `_ => none` fallthrough at `LeanPoison/Syntax.lean:446`). So the precondition is contradictory.

**Arrow vacuity (3 sites, ~9–14 lines each).** `closure_extern` constructor unifies `body = Expr.externFn id y argTyp retSpec eff`. `cinit.registry = emptyExternRegistry` by default `Config.mk`. `terminatesTo_preserves_registry` propagates this through `e2` and `e1` evaluations to `c₁.registry`. Then `terminatesTo body { c₁ with … }` requires `beval` on `Expr.externFn` under empty registry to succeed, but the runtime returns `runtimeError` when `config.registry.get? id = none` (`LeanPoison/BigStep.lean:204`). Contradiction.

## Why This Was the Right Reframing

The six sorries were structurally unreachable from the existing inversion-lemma preconditions under the current empty-registry FR convention. They were never about *how* to handle extern dispatch correctly — only about handling a case Lean's exhaustivity check forced once the new constructors landed.

Cleaning them up:
- Required no new architecture.
- Required no new `sorry` or `axiom`.
- Required no Phase F extensions to `deepValueQTypProperty` / `agreeValueUnder`.
- Belongs with the Probe 1 commit because they are what makes the Probe 1 code proof-clean.

## When the Vacuity Discharges Become Unsound

The arrow vacuity arguments rely on `cinit.registry = emptyExternRegistry`. If Probe 2's eventual `TrustedRegistry` work makes the initial registry non-empty, those three discharges (lines 2342, 3627, 3632 post-cleanup) become unsound and must be replaced with real boundary-contract invocations.

The parrow vacuity argument relies on `Expr.toPExpr?` returning `none` for `externPfn`, which is a property of the language definition and remains sound regardless of registry policy. Those three discharges (lines 2976, 6304, 6309 post-cleanup) stay valid under any registry.

## Future Probe 2 Scope

When Probe 2 actually starts (driven by the need to support concrete drivers in Probes 4–5), the work to do is exactly what `doc/ffi-axioms.md` already describes:

1. Factor `StepFRPost` out of the existing `StepFR` conclusion shape.
2. Define `ExternCallEntry`, `ExternCallBoundaryRun.{fn,pfn}`, `ExternCallBoundarySingle.{fn,pfn}`, `ExternCallBoundaryFR.{fn,pfn}`.
3. Define `TrustedRegistry`, `TrustedExternEntry`, `ExternBoundarySpec`, `TrustedRegistryAgreesWithProgram`.
4. Thread `TrustedRegistry` through `FaultRobustnessSpec` so the top-level theorem becomes registry-relative.
5. Replace the three arrow vacuity discharges in `StepFRApp.lean` with real boundary-contract invocations once the registry is non-empty.

None of this is on the critical path for Probe 1 cleanup. It is the right design when concrete extern drivers need to be plugged in.

## Files Changed by the Vertical Slice

- `/work/LeanProofs/StepFRApp.lean` — six `sorry` lines replaced with vacuity proofs (one-liner for parrow, ~9–14 lines for arrow).

The interim `LeanProofs/ExternBoundary.lean` written and discarded during the spike has been removed; only the discharges remain in the final code state.
