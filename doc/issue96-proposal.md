# Issue #96 proposal

Reference: `https://github.com/vzaliva/poison-lang/issues/96`.

## Summary

`stepFR_assign` is currently false because runtime assignment updates **one concrete address**, while typing assignment to a **non-singleton locset** performs a weak update to **every logical location in the locset**; if that weak update preserves a guard-tag predicate whose tag is `true` in the regime `R`, then those locations become *clean-under-R* and `agreeOnClean` demands cross-run equality on them, which can fail when the two runs update different concrete addresses.

## Proposed fix (simple, deref-symmetric)

Make **assignment through a poisoned reference** erase predicates on the written cell(s), mirroring `deref_poisoned` (where reading via a poisoned reference returns `no_pred` to prevent later de-poisoning). Concretely: if the LHS reference `e1` typechecks with poison `p₁ = true`, then the heap cell update performed by assignment stores predicate `no_pred` (not `P₂` / merged `P₄`), while still setting the stored poison as before (`pc ⊔ p₁ ⊔ p₂`, plus any existing poison joined for weak updates).

This prevents a weak update through an untrusted reference from (re-)introducing guard tags that would make post-context locations clean-under-R, eliminating the spurious `agreeOnClean` obligations that break `StepFR`.

## Proposed Ott rule changes

Make the existing assignment rules explicitly a **clean-reference** case (to avoid overlap/ambiguity once we add poisoned-reference variants). This mirrors the dereference split between `deref_poisoned` (requires a poisoned reference) and the other deref rules (require a clean reference).

Then add poisoned-reference variants of the assignment rules. These new rules are symmetric to `deref_poisoned` in that they erase predicates to `no_pred` when the reference itself is poisoned.

### Singleton (strong update) through clean ref (existing rule, made explicit)

```ott
pm ; R ; pc ; G ; S ; L |- e1 : ref int @ { l } :> clean { P1 } -| G1 ; L1
pm ; R ; pc ; G1 ; S ; L1 |- e2 : int :> p2 { P2 } -| G2 ; L2
invalidate_deps L2 { l } = L3
----------------------- :: assign_singleton
pm ; R ; pc ; G ; S ; L |- e1 := e2 : unit :> join pc clean { no_pred } -|
  G2[l |-> int :> join pc join clean p2 { P2 }] ; L3
```

### Non-singleton (weak update) through clean ref (existing rule, made explicit)

```ott
pm ; R ; pc ; G ; S ; L |- e1 : ref int @ LS0 :> clean { P1 } -| G1 ; L1
pm ; R ; pc ; G1 ; S ; L1 |- e2 : int :> p2 { P2 } -| G2 ; L2
invalidate_deps L2 LS0 = L3
JoinPoisons G2 LS0 = p3
MergePreds G2 LS0 = P3
JoinP P2 P3 = P4
----------------------- :: assign_locset
pm ; R ; pc ; G ; S ; L |- e1 := e2 : unit :> join pc clean { no_pred } -|
  G2[LS0 |-> int :> join p3 join pc join clean p2 { P4 }] ; L3
```

### Singleton (strong update) through poisoned ref

```ott
pm ; R ; pc ; G ; S ; L |- e1 : ref int @ { l } :> poisoned { P1 } -| G1 ; L1
pm ; R ; pc ; G1 ; S ; L1 |- e2 : int :> p2 { P2 } -| G2 ; L2
invalidate_deps L2 { l } = L3
----------------------- :: assign_singleton_poisoned_ref
pm ; R ; pc ; G ; S ; L |- e1 := e2 : unit :> join pc poisoned { no_pred } -|
  G2[l |-> int :> join pc join poisoned p2 { no_pred }] ; L3
```

### Non-singleton (weak update) through poisoned ref

```ott
pm ; R ; pc ; G ; S ; L |- e1 : ref int @ LS0 :> poisoned { P1 } -| G1 ; L1
pm ; R ; pc ; G1 ; S ; L1 |- e2 : int :> p2 { P2 } -| G2 ; L2
invalidate_deps L2 LS0 = L3
JoinPoisons G2 LS0 = p3
----------------------- :: assign_locset_poisoned_ref
pm ; R ; pc ; G ; S ; L |- e1 := e2 : unit :> join pc poisoned { no_pred } -|
  G2[LS0 |-> int :> join p3 join pc join poisoned p2 { no_pred }] ; L3
```

## Expected code/spec changes

- **Ott spec (`poison-lang-spec/poison-lang.ott`)**: make `assign_singleton` / `assign_locset` explicitly require a clean LHS reference (as above), and add `assign_singleton_poisoned_ref` / `assign_locset_poisoned_ref`.
- **Lean typechecker (`LeanPoison/Typecheck.lean`)**: implement the above Ott rules in `typecheckAssign` by overriding the stored predicate to `Predicate.noPred` when the LHS reference poison is `true` (and in the non-singleton case avoid merging/preserving predicates in `updateLocsetWeak` for this write).
- **Proofs (`LeanProofs/FaultRobustnessProofs.lean`)**: with the post-context no longer making the entire locset clean-under-R via guard predicates, `stepFR_assign` should become provable under the existing `agreeOnClean` definition.
