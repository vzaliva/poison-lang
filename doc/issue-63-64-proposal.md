# Proposal: Merged Typing Closures for Conditional Joins (Issue #63)

## 1. Aim and context

GitHub issue [#63](https://github.com/vzaliva/poison-lang/issues/63) points out that at `if` joins the type system currently chooses a single typing closure, even though at runtime multiple closures are possible.

This proposal introduces **merged typing closures** to resolve the unsoundness and inflexibility identified in Issue #63. Conditionals use merged closures at their joins, and application types **all possible closures** before conservatively joining results. The change is local to the typing and proof infrastructure: it does not affect the operational semantics of Poison programmes, but it restores a coherent higher-order story for de-poisoning and alias analysis across conditional control flow.

**Note on Issue #64:** While-loops do not require special handling for merged closures because (1) while loops always return `unit`, not function types, and (2) arrow types are not stored in the memory environment `Γ`. Therefore, Issue #64 is a non-issue.

We assume the reader is familiar with the existing typing rules and big-step semantics; this proposal only describes what changes.

## 2. Background

The existing system already has:

- enriched arrow types `ST₁ -> ST₂ # p typing_closure tcl` / `typing_pclosure ptcl` with typing closures, and
- flow-insensitive joins for `if` and `while` that combine `pc`, memory and tag environments.

We keep all of that structure; the only change is that the **closure component** of arrow types becomes a non-empty set of alternatives rather than a single closure.

## 3. Core idea: arrow types with non-empty closure sets

### 3.1 Arrow representation

We extend arrow types so that the closure component is **always** a non-empty finite set of alternatives:

- For impure functions:
  `ST₁ -> ST₂ # p typing_closures {tcl₁, …, tclₙ}`   where n ≥ 1
  where each `tclᵢ : FnTClosure` has the same interface `(ST₁, ST₂)`.
- For pure functions:
  an analogous `typing_pclosures {ptcl₁, …, ptclₙ}` over `PFnTClosure`.

Arrow types at joins therefore never "pick" a single distinguished closure; they instead carry the **flow-insensitive set of all closures** that might arise along any path or iteration.

### 3.2 Normalisation

We conceptually work with sets, but in an implementation this would be represented by some finite container equipped with:

- insertion of closures using the existing closure equality / `BEq` instances, and
- a normal form that guarantees no duplicates.

Every function-valued `ETyp` thus has the uniform shape

- `ST₁ -> ST₂ # p typing_closures {tcl₁, …, tclₙ}`

for some `n ≥ 1`, and all control-flow joins simply operate on the set component by taking unions.

### 3.3 Signature compatibility

Two enriched types are *signature-compatible* (written `T₁ ≈ T₂`) when they have the same shape, ignoring poisons and closures:

- Base types: `int ≈ int`, `bool ≈ bool`, `unit ≈ unit`, `string ≈ string`.
- Reference types: `ref T₁ @ l₁ ≈ ref T₂ @ l₂` iff `T₁ ≈ T₂` and `l₁ = l₂`.
- Arrow types (impure): `(ST₁ -> ST₂ # p₁ typing_closures C₁) ≈ (ST₁' -> ST₂' # p₂ typing_closures C₂)` iff `ST₁ = ST₁'` and `ST₂ = ST₂'`.
- Pure arrow types: `(ST₁ -> ST₂ # p₁ typing_pclosures C₁) ≈ (ST₁' -> ST₂' # p₂ typing_pclosures C₂)` iff `ST₁ = ST₁'` and `ST₂ = ST₂'`.
- Impure and pure arrow types are **not** signature-compatible with each other, even if their surface types match.
- All other combinations are incompatible.

Note that for arrow types, only the surface types (`ST₁`, `ST₂`) must match; poisons and closure sets may differ (and will be joined at the merge). Since surface types (`ST`) do not carry poison or closure information, this comparison is straightforward even when `ST₁` or `ST₂` are themselves arrow types.

## 4. Conditionals returning functions (Issue #63)

Issue #63 describes the current `if` typing in detail; here we only state the revised rule.

The new `if` typing rule for function results is:

- **Guard handling:** unchanged (same `if_depoison`/`if_std` structure and `pc` / predicate updates).
- **Interface compatibility:** require that the branch result types are signature-compatible (`T₂ ≈ T₃`).
- **Function poison at the join:** Suppose branch 2 produces qualified type `T₂ :> p₂` and branch 3 produces `T₃ :> p₃`, where `T₂ = ST₁ -> ST₂ # p₂ᵃ typing_closures C₂` and `T₃ = ST₁ -> ST₂ # p₃ᵃ typing_closures C₃`. Function types carry two poison flags:
  - The *arrow-internal poison* (`p₂ᵃ`, `p₃ᵃ`) captures the `pc` at function definition time.
  - The *outer qualified-type poison* (`p₂`, `p₃`) reflects how the function value was computed in the branch.
  
  At the join, both are joined: the result arrow type has internal poison `p₂ᵃ ⊔ p₃ᵃ`, and the outer qualified-type poison is `p₂ ⊔ p₃`.
- **Closure set at the join:** the joined arrow type carries the union `C₂ ∪ C₃` as its closure component:
  - Result: `(ST₁ -> ST₂ # (p₂ᵃ ⊔ p₃ᵃ) typing_closures (C₂ ∪ C₃)) :> (p₂ ⊔ p₃)` (or `parrow` for pure functions).
- **Environments and predicates:** join memory/tag environments as today. Since predicates are only meaningful for basic types (de-poisoning does not apply to functions), the result predicate for function types is always `no_pred`.

For non-function result types, the existing `if` typing rules are unchanged.

## 5. Application of closure sets

### 6.1 Typing rule

If the closure set is empty, the application is ill-typed. While empty sets cannot arise in practice (sets are formed by singletons and unions), handling this case explicitly avoids the need to maintain a non-emptiness invariant in proofs.

For an expression `e₁ e₂` where `e₁` has a function type with closure set:

- `ST₁ -> ST₂ # p_join typing_closures C`

the application rule:

1. Types `e₂` to obtain qualified type `Q` for the argument and updated environments (`Γ₀`, `L₀`).
2. For each alternative closure `tclᵢ` in the set, **independently** (each starting from the same `Γ₀`, `L₀`):
   - re-types the body under:
     - the actual argument `Q`,
     - the input memory and tag environments (`Γ₀`, `L₀`),
     - the captured variable environment of `tclᵢ`;
   - obtains a result `Qᵢ` with updated environments (`Γᵢ`, `Lᵢ`).
3. Requires the result enriched types `Tᵢ` to be **signature-compatible** across all alternatives (same surface result type, and if they are themselves function types, same `ST₁`, `ST₂` and same purity).
4. Joins all outputs:
   - memory environments: `Γ' = Γ₁ ⊔ Γ₂ ⊔ ... ⊔ Γₙ` (using existing `JoinG`),
   - tag environments: `L' = L₁ ⊔ L₂ ⊔ ... ⊔ Lₙ` (using agreement-only join),
   - poisons for the result (across alternatives and with caller `pc`),
   - predicates: for non-function results, use agreement-only policy (keep predicate if all `Qᵢ` agree, otherwise `no_pred`); for function results, always use `no_pred` (predicates are only meaningful for basic types).
5. If the result is a function, constructs a **new closure set** from the closures returned by each alternative, again deduplicated.

The existing single-closure case is recovered as the special case where `C` is a singleton.

### 5.2 Predicate merging policy

When combining predicates (at control flow joins, dereference through location sets, or guard matching), use the following merge rule:

1. **Exact match:** If `P₁ = P₂` (same tag and closure), preserve the predicate.
2. **Tag match:** If both have the same tag `k` but different closures, use `guard k` (losing the closure).
3. **Otherwise:** Use `no_pred`.

This agreement-only policy ensures that predicates are only preserved when they are identical, or when they share the same guard tag (in which case the more general `guardOnly` form is used). This prevents information loss from asymmetric predicate handling and ensures conservative de-poisoning behaviour.

### 5.3 Strictness

If any alternative closure is ill-typed at application (e.g., argument type mismatch), the entire application is rejected. This strict policy is easy to reason about and ensures no silent dropping of alternatives.

## 6. Spec, documentation, and implementation plan

### 6.1 Ott specification

- Extend the grammar of function types to admit merged typing closures:
  - either by adding explicit "merged closure" constructors,
  - or by treating the typing-closure component as a non-empty list.
- Update `if_depoison` / `if_std` rules:
  - when branches produce functions with equal `(ST₁, ST₂)`, set:
    - arrow poison to the join of branch poisons,
    - closure to the merged closure over branch closures.
- Extend `app_fn` / `app_pfn` rules to:
  - type all alternatives in a merged closure,
  - require result signature compatibility,
  - join poisons, environments, and predicates,
  - construct merged closures for function results.

### 6.2 Documentation (`poison-lang-description.tex`)

- Add a subsection explaining:
  - typing closures and their role in higher-order reasoning,
  - merged closures as abstract sets of alternatives at conditional joins.
- Describe application of merged closures, including:
  - the map–join structure over alternatives,
  - the conservative treatment of predicates and logical information.
- Provide worked examples:
  - an `if` returning functions with different captured environments.

### 6.3 Lean implementation

In `LeanPoison/Poison.lean`:

- Introduce a merged-closure representation (`MergedFnTClosure`, `MergedPFnTClosure`, or similar).
- Provide:
  - constructors from single closures,
  - a `mergeClosures` operation that flattens and deduplicates,
  - equality / `BEq` instances as needed.

In `LeanPoison/Typecheck.lean`:

- Extend `ETyp` to carry merged closures in the function cases, or introduce a small wrapper type.
- Update `typecheckIf`:
  - after typing branches and checking interface compatibility, construct:
    - joined function poison,
    - merged closure over branch closures,
    - joined environments and predicates.
- Extend `typecheckApp`:
  - add cases for merged closures following Section 6,
  - keep the single-closure path as an optimised special case.

In `LeanProofs/`:

- Update proofs to account for merged closures in typing derivations.
- The top-level theorem formulations (Preservation, Progress, Non-interference) remain unchanged; only the internal proof structure requires adjustment to handle closure sets.



