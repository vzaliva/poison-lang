# Proposal: Merged Typing Closures for Branch and Loop Joins (Issues #63 and #64)

## 1. Aim and context

GitHub issues [#63](https://github.com/vzaliva/poison-lang/issues/63) and [#64](https://github.com/vzaliva/poison-lang/issues/64) both point out that at `if` and `while` joins the type system currently chooses a single typing closure, even though at runtime multiple closures are possible.

This document proposes a unified change to the internal function type representation and typing rules so that joins record **all** closures that may arise, and application systematically considers all of them.

We assume the reader is familiar with the existing typing rules and big-step semantics; this proposal only describes what changes.

## 2. Background (very brief)

The existing system already has:

- enriched arrow types `ST1 -> ST2 # p typing_closure tcl` / `typing_pclosure ptcl` with typing closures, and
- flow-insensitive joins for `if` and `while` that combine pc, memory and tag environments.

We keep all of that structure; the only change is that the **closure component** of arrow types becomes a non-empty set of alternatives rather than a single closure.

## 3. Core idea: arrow types with non-empty closure sets

### 3.1 Arrow representation

We extend arrow types so that the closure component is **always** a non-empty finite set of alternatives:

- For impure functions:
  `ST1 -> ST2 # p typing_closures {tcl1, ..., tcln}`   where n ≥ 1
  where each `tclᵢ : FnTClosure` has the same interface `(ST₁, ST₂)`.
- For pure functions:
  an analogous `typing_pclosures {ptcl_1, \dots, ptcl_n}` over `PFnTClosure`.

Arrow types at joins therefore never “pick” a single distinguished closure; they instead carry the **flow-insensitive set of all closures** that might arise along any path or iteration.

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

Note that for arrow types, only the surface types `ST₁` and `ST₂` must match; poisons and closure sets may differ (and will be joined at the merge). Since surface types (`Typ`) are simple and do not carry poison or closure information, this comparison is straightforward even when `ST₁` or `ST₂` are themselves arrow types.

## 4. Conditionals returning functions (Issue #63)

Issue #63 describes the current `if` typing in detail; here we only state the revised rule.

The new `if` typing rule for function results is:

- **Guard handling:** unchanged (same `if_depoison`/`if_std` structure and pc / predicate updates).
- **Interface compatibility:** require only that both branches produce function types with **identical surface interface** `(ST₁, ST₂)`; do not require closure or poison equality.
- **Function poison at the join:** Suppose branch 2 produces qualified type `(ST₁ -> ST₂ # p₂ᵃ typing_closure tcl₂) :> p₂` and branch 3 produces `(ST₁ -> ST₂ # p₃ᵃ typing_closure tcl₃) :> p₃`. Function types carry two poison flags:
  - The *arrow-internal poison* (`p₂ᵃ`, `p₃ᵃ`) captures the `pc` at function definition time.
  - The *outer qualified-type poison* (`p₂`, `p₃`) reflects how the function value was computed in the branch.
  
  At the join, both are joined: the result arrow type has internal poison `p₂ᵃ ⊔ p₃ᵃ`, and the outer qualified-type poison is `p₂ ⊔ p₃`.
- **Closure set at the join:** the joined arrow type carries the union `{tcl₂} ∪ {tcl₃}` (or more generally `C₂ ∪ C₃` if branches already have closure sets) as its closure component:
  - Result: `(ST₁ -> ST₂ # (p₂ᵃ ⊔ p₃ᵃ) typing_closures (C₂ ∪ C₃)) :> (p₂ ⊔ p₃)` (or `parrow` with the corresponding set of `PFnTClosure`s).
- **Environments and predicates:** join memory/tag environments as today. Since predicates are only meaningful for basic types (de-poisoning does not apply to functions), the result predicate for function types is always `no_pred`.

For non-function result types, the existing `if` typing rules are unchanged.

## 5. While-loop joins (Issue #64)

Issue #64 is the loop analogue of Issue #63; we again only describe the changed behaviour.

### 5.1 Closure sets at loop back-edges and exit

The proposal is to mirror the conditional design:

- **Within the loop body:**
  - when typing `e₂`, any nested conditionals that return functions already use closure sets (Section 4), so body results are closure-precise.
- **At the back-edge join (inside `runWhileFixpoint`):**
  - when joining `Γ` and `ℒ` from the body with the incoming context:
    - for function-typed entries with the same interface but different closure sets, take the **set union** of closures from each side;
    - join function poisons as usual.
  - this ensures that variables that can hold function values across iterations are typed with closure sets representing **all closures that any iteration could produce**.
- **At loop exit:**
  - the final `TypeResult`’s memory and tag environments, after fixpoint, may still contain function-typed entries with non-empty closure sets;
  - any post-loop uses of these functions (e.g. applications or returns) then see exactly the same closure-set semantics as in the conditional case.

In effect, `runWhileFixpoint` is extended so that its environment join for function entries respects the closure-set abstraction rather than silently discarding or overwriting alternatives.

From the closure-set point of view, `runWhileFixpoint` is computing a **fixpoint over closure sets as well as over pc/Γ/ℒ**: at each iteration, the closure set for a function-typed binding may grow as new alternatives are discovered, and the fixpoint is reached exactly when no new closures are added anywhere. Since there are only finitely many syntactic closures in the programme and we deduplicate, this closure-level fixpoint terminates together with the existing fixpoint on environments.

### 5.2 Guard-based de-poisoning in loops

Loop rules already support predicate-based de-poisoning via:

- matching guards in `while_depoison`,
- tracking a guard tag across iterations in `ℒ`,
- and an “agreement-only” policy at the back-edge.

With merged closures, the same principles apply: predicates on function-typed bindings are always `no_pred` (since de-poisoning applies only to basic types), while predicates on basic-typed bindings follow the existing agreement-only policy.

## 6. Application of closure lists

### 6.1 Typing rule

Application typing over non-empty closure sets is shared between Issues #63 and #64.

For an expression `e₁ e₂` where `e₁` has a function type with closure set:

- `ST₁ -> ST₂ # p_join typing_closures C`

the application rule:

1. Types `e₂` to obtain `QTyp` for the argument and updated environments (`G₀`, `L₀`).
2. For each alternative closure `tclᵢ` in the set, **independently** (each starting from the same `G₀`, `L₀`):
   - re-types the body under:
     - the actual argument `QTyp`,
     - the input memory and tag environments (`G₀`, `L₀`),
     - the captured variable environment of `tclᵢ`;
   - obtains a result `QTᵢ` with updated environments (`Gᵢ`, `Lᵢ`).
3. Requires the result `ETyp`s to be **signature-compatible** across all alternatives (same surface result type, and if they are themselves function types, same `ST₁`, `ST₂` and same purity).
4. Joins all outputs:
   - memory environments: `G' = G₁ ⊔ G₂ ⊔ ... ⊔ Gₙ` (using existing `JoinG`),
   - tag environments: `L' = L₁ ⊔ L₂ ⊔ ... ⊔ Lₙ` (using agreement-only join),
   - poisons for the result (across alternatives and with caller pc),
   - predicates: for non-function results, use agreement-only policy (keep predicate if all `QTᵢ` agree, otherwise `no_pred`); for function results, always use `no_pred` (predicates are only meaningful for basic types).
5. If the result is a function, constructs a **new closure set** from the closures returned by each alternative, again deduplicated.

The existing single-closure case is recovered as the special case where `C` is a singleton.

### 6.2 Strictness vs filtering

As discussed in Issue #63, there are two possible policies if some alternatives fail to type for a given argument:

- **Strict policy (recommended initial choice):**
  - if any alternative is ill-typed at application, the entire application is rejected.
  - This is easy to reason about and matches a “no silent path dropping” philosophy.
- **Filtering policy (future extension):**
  - ill-typed alternatives are discarded; the application is typed over the remaining ones, provided the set is non-empty.
  - This may increase expressiveness but complicates reasoning and error reporting.

The design here adopts the **strict policy** initially, with the option to revisit filtering once there is implementation experience.

## 7. Spec, documentation, and implementation plan

### 7.1 Ott specification

- Extend the grammar of function types to admit merged typing closures:
  - either by adding explicit “merged closure” constructors,
  - or by treating the typing-closure component as a non-empty list.
- Update `if_depoison` / `if_std` rules:
  - when branches produce functions with equal `(ST₁, ST₂)`, set:
    - arrow poison to the join of branch poisons,
    - closure to the merged closure over branch closures.
- Update `while_depoison` / `while_std` rules and the back-edge recurrence:
  - when joining environments, define the combination of function-typed entries to merge closures as above.
- Extend `app_fn` / `app_pfn` rules to:
  - type all alternatives in a merged closure,
  - require result signature compatibility,
  - join poisons, environments, and predicates,
  - construct merged closures for function results.

### 7.2 Documentation (`poison-lang-description.tex`)

- Add a subsection explaining:
  - typing closures and their role in higher-order reasoning,
  - merged closures as abstract sets of alternatives at joins,
  - how conditionals and loops use merged closures at branch, back-edge, and exit joins.
- Describe application of merged closures, including:
  - the map–join structure over alternatives,
  - the conservative treatment of predicates and logical information.
- Provide worked examples:
  - an `if` returning functions with different captured environments,
  - a loop that accumulates higher-order values, later applied outside the loop.

### 7.3 Lean implementation

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
- Update `runWhileFixpoint` / `typecheckWhileDepoison` / `typecheckWhileStd`:
  - in the environment join, treat function entries specially by merging their closures instead of overwriting them.
- Extend `typecheckApp`:
  - add cases for merged closures following Section 6,
  - keep the single-closure path as an optimised special case.

In `LeanProofs/`:

- Update proofs to account for merged closures in typing derivations.
- The top-level theorem formulations (Preservation, Progress, Non-interference) remain unchanged; only the internal proof structure requires adjustment to handle closure sets.

## 8. Summary

This proposal introduces **merged typing closures** as a unifying abstraction to resolve the unsoundness and inflexibility identified in Issues #63 and #64. Conditionals and while-loops both use merged closures at their joins, and application types **all possible closures** before conservatively joining results. The change is local to the typing and proof infrastructure: it does not affect the operational semantics of Poison programmes, but it restores a coherent higher-order story for de-poisoning and alias analysis across complex control flow.


