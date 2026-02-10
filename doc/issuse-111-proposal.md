# Issue #111 proposal (brief)

- Reference: `https://github.com/vzaliva/poison-lang/issues/111`
- Related follow-up: `https://github.com/vzaliva/poison-lang/issues/113`

## Thesis

This is an `app` typing-rule deficiency (likely a leftover from incomplete
function-poison integration). `assign` and FR-proof failures are downstream
effects, not the root cause.

## Historical context

The historical `doc/function-poison.md` design (in git history) set this intent:

- internal arrow poison controls closure reliability/agreement,
- dirty internal poison permits permissive closure agreement.

But `typecheckApp` still computes final result poison in a way that can remain
clean for non-function results when body typing is `pc`-insensitive (e.g.
literals), even with dirty function poison.

Notably, function-poison integration commits (including `574d28b`) changed
`LeanProofs/*` and docs, but did not change `LeanPoison/Typecheck.lean` app
result-poison logic or Ott app typing. That strongly suggests a historical
leftover in app typing, not an intentional assign/proof-only design.

## Root cause (short)

1. `StepFR` requires result agreement when result type is clean-under-regime.
2. For dirty internal arrow poison, function agreement can be permissive.
3. App typing can still produce a clean non-function result despite dirty
   function provenance/selection.
4. Runtime may execute different closures across runs (`3` vs `4`).

Contradiction follows in `stepFR_app`, and `stepFR_assign` fails downstream when
those divergent values are written.

So `assign` is not root cause; it only exposes the `app` mismatch.

## Proposed fix (only)

Update application typing to conservatively taint app results by function poison.

For arrow/parrow application, final result poison should include:

- caller `pc`,
- function internal poison `p`,
- body/result poison from closure typing,
- function outer poison `p1`.

Practical implementation direction:

- choose **Option A** (localized tainting in closure application helpers):
  apply taint inside `applyFnTClosure` and `applyPFnTClosure`, where `p` and
  `p1` are directly in scope.
- apply this uniformly to regular and extern closure branches.
- keep `joinTypeResults` unchanged (it does not know `p`/`p1`).
- for each closure alternative result `r`, return poison:
  `joinPoison p1 (joinPoison p r.qualType.poison)`.
  Then `joinTypeResults` still contributes caller `pc` via its existing final
  `joinPoison ctx.pc ...`.
- net effect at app level: final poison includes `pc`, `p`, `p1`, and joined
  body/result poison.

Reason `p1` is required (not optional):

- with poisoned function provenance (`p1 = true`) but clean internal poison
  (`p = false`), two runs may still pick different closures and diverge; `p`-only
  tainting would miss this case.

Minimal counterexample shape:

```poison
let c  = extern val : (int :> poisoned {...}) in
let f1 = fn u : unit => 3 : int in
let f2 = fn u : unit => 4 : int in
let g  = if c > 0 then f1 else f2 in
g unit
```

In this shape, `g` can have `p1 = true` (provenance taint) while internal poison
at the selected closure type is clean; `p`-only tainting is insufficient.

## Impacted artifacts

- `LeanPoison/Typecheck.lean` (`typecheckApp` result poison join)
- `poison-lang-spec/poison-lang.ott` (`app_fn_*` / `app_pfn_*` conclusions)
- `doc/poison-lang-description.tex` (function-application poison narrative/examples)

## Why this fix

- aligns with function-poison design intent: dirty function behavior should not
  yield clean-observable outputs by typing alone,
- removes the clean-result trigger in the `#111` witness,
- addresses both app-only and assignment-derived counterexamples at source.

## Scope and non-goals

- This proposal does not change `assign` typing rules.
- This proposal does not redefine FR obligations.
- This proposal does not rely on literal typing changes.
- This proposal does not settle predicate-based de-poisoning policy for app
  results when function provenance is poisoned (`p1 = true`) (tracked in `#113`).

## Validation

1. `lake build`
2. `make test`
3. Re-run `#111` witnesses and confirm app result type is dirty in the critical
   case (no clean-result agreement obligation triggered).
