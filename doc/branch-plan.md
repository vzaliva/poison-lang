# Mode 3 Branch Plan

This is the working plan for the current branch.

Background analysis, counterexamples, and discarded alternatives live in
`doc/mode3-proof-lessons.md`.

## 1. Approach A

We adopt the strong form of Approach A.

If `matchGuard` succeeds but `R.lookup? k = none`, the type system should not
create any branch-local tag fact.  The unknown-regime case should therefore
fall through to ordinary conservative `if` typing.

Concretely:

- no branch-local `tagEnv[k := ...]` updates;
- no branch-local `regime[k := ...]` updates;
- no branch-local de-poisoning of either the checked carrier or linked
  same-tag carriers;
- no branch-local false-side regime assertions for `guardClosure` entries.

Modes 1 and 2 remain unchanged.  The repair is local to the `R(k) = none`
case.

Semantic effect:

- preserved: regime-known conditional reasoning (`R.lookup? k = some true` /
  `some false`);
- removed: regime-unknown conditional reasoning.

## 2. Plan

### 2.1. Update the Ott Rules / Spec Story

Update the Ott/spec/documentation description so the unknown-regime case is no
longer a branch-local de-poisoning rule.

Suggested concrete rule change:

- introduce an Ott helper meta-function, e.g.
  `if_guard_case e G S R = c`, where `c` ranges over
  `std | true_case | false_case`;
- keep `if_depoison_fn_R_true` / `if_depoison_fn_R_false`,
  `if_depoison_pfn_R_true` / `if_depoison_pfn_R_false`,
  `if_depoison_ref_R_true` / `if_depoison_ref_R_false`,
  and `if_depoison_R_true` / `if_depoison_R_false` unchanged;
- remove the four current unknown-regime rules
  `if_depoison_fn_R_unknown`, `if_depoison_pfn_R_unknown`,
  `if_depoison_ref_R_unknown`, and `if_depoison_R_unknown`;
- make the `*_R_true` and `*_R_false` rules dispatch on
  `if_guard_case e1 G S R = true_case` / `false_case` instead of carrying the
  raw `match_guard` and `R(k)` premises directly;
- make the `if_std_*` rules dispatch on `if_guard_case e1 G S R = std`;
- define `if_guard_case` so it mirrors the Lean `typecheckIf` split:
  `std` when no guard matches, `std` when a guard matches but `R(k) = none`,
  `true_case` when a guard matches and `R(k) = true`, and `false_case` when a
  guard matches and `R(k) = false`.

Concretely, the merged fallback family should still have the same branch shape
as:

- `if_std_fn` for impure function results;
- `if_std_pfn` for pure function results;
- `if_std_ref` for reference results;
- `if_std` for the general non-reference case.

For the general non-reference case, the intended replacement shape is:

```text
if_guard_case e1 G S R = std
pure ; R ; pc ; G ; S ; L |- e1 : bool :> p1 { P1 } -| G ; L ; R
pm ; R ; join pc p1 ; G ; S ; L |- e2 : T :> p2 { P2 } -| G2 ; L2 ; R2
pm ; R ; join pc p1 ; G ; S ; L |- e3 : T :> p3 { P3 } -| G3 ; L3 ; R3
----------------------------------  :: if_std
pm ; R ; pc ; G ; S ; L |- if e1 then e2 else e3 : T :> join pc join p1 join p2 p3 { no_pred } -| JoinGStrong G2 G3 ; JoinL L2 L3 ; JoinR R2 R3
```

The function and reference variants should be changed analogously.

The intended reading is:

- the helper determines whether the conditional is in the known-true,
  known-false, or standard case;
- the standard case now covers both "no matching guard" and
  "matching guard but regime-unknown";
- therefore no branch-local tag fact is introduced in the standard case;
- the conditional is typed conservatively.

### 2.2. Change `typecheckIf`

`typecheckIf` is the Lean implementation point of the Ott `if` rules, so once
the Ott story is changed, this is the corresponding code change.

Replace the current `R.lookup? k = none` branch in `typecheckIf` with the same
conservative typing pattern used by mode 4.

In particular:

- keep the current `matchGuard` / `R.lookup?` control-flow order;
- when `R.lookup? k = none`, do not build branch-local contexts carrying a
  remembered tag fact;
- instead, reuse the ordinary conservative `if` branch typing logic.

### 2.3. Update Documentation

Update the language description in `doc/poison-lang-description.tex` so it
matches the new merged `if_std` / `if_guard_case` story and no longer presents
regime-unknown guarded conditionals as a separate branch-local de-poisoning
mechanism.

### 2.4. Simplify the FR Proofs

After the typechecker change, remove the special mode-3 proof burden instead of
repairing it.

Concretely:

- rename the proof-side mode prefixes to match the Ott split:
  `mode1 -> true`, `mode2 -> false`, `mode3/mode4 -> std` where appropriate;
- `stepFR_ite_mode3` should disappear or reduce to the same `std` proof path
  as the ordinary conservative `if` case;
- `stepFRSingleRun_ite_mode3_maskedReg` should likewise disappear or become a
  trivial delegation into the `std` single-run proof;
- any mode-3-specific masked transport that only supports the old unknown-
  regime rule should be removed if it becomes dead code.

### 2.5. Verify

- Lean code should compile without warnings;
- run the Lean build;
- make sure the Ott/spec and documentation also compile;
- run the unit tests;
- if expected test outputs need updating, do that only after checking
  carefully that the observed differences are intended consequences of the
  change rather than regressions;
- allow temporary mode-3 `sorry`s while the refactor is in flight, but the
  final goal is to end with zero `sorry`s and no warnings;
- update this plan if the implementation path changes.
