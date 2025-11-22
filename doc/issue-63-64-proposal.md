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
  \[
    ST_1 \to ST_2 \; \#\; p \;\texttt{typing\_closures}\; \{tcl_1, \dots, tcl_n\}, \quad n \ge 1,
  \]
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

## 4. Conditionals returning functions (Issue #63)

Issue #63 describes the current `if` typing in detail; here we only state the revised rule.

The new `if` typing rule for function results is:

- **Guard handling:** unchanged (same `if_depoison`/`if_std` structure and pc / predicate updates).
- **Interface compatibility:** require only that both branches produce function types with **identical surface interface** `(ST₁, ST₂)`; do not require closure or poison equality.
- **Function poison at the join:** define
  \[
    p_{\text{join}} := p_2 \sqcup p_3,
  \]
  the join of branch function poisons.
- **Closure set at the join:** if branches have closure sets `C₂` and `C₃`, the joined arrow type carries the union `C₂ ∪ C₃` as its closure component:
  - `ETyp.arrow ST₁ ST₂ p_join typing_closures (C₂ ∪ C₃)` (or `parrow` with the corresponding set of `PFnTClosure`s).
- **Environments and predicates:** join memory/tag environments as today; result predicates continue to use the existing “agreement-only” policy (keep only when all branch results agree, otherwise use `no_pred`).

For non-function result types, the existing `if` typing rules are unchanged.

## 5. While-loop joins (Issue #64)

Issue #64 is the loop analogue of Issue #63; we again only describe the changed behaviour.

### 5.1 Closure sets at loop back-edges and exit

The proposal is to mirror the conditional design:

-- **Within the loop body:**
  - when typing `e₂`, any nested conditionals that return functions already use closure sets (Section 4), so body results are closure-precise.
-- **At the back-edge join (inside `runWhileFixpoint`):**
  - when joining `Γ` and `ℒ` from the body with the incoming context:
    - for function-typed entries with the same interface but different closure sets, take the **set union** of closures from each side;
    - join function poisons as usual.
  - this ensures that variables that can hold function values across iterations are typed with closure sets representing **all closures that any iteration could produce**.
-- **At loop exit:**
  - the final `TypeResult`’s memory and tag environments, after fixpoint, may still contain function-typed entries with non-empty closure sets;
  - any post-loop uses of these functions (e.g. applications or returns) then see exactly the same closure-set semantics as in the conditional case.

In effect, `runWhileFixpoint` is extended so that its environment join for function entries respects the closure-set abstraction rather than silently discarding or overwriting alternatives.

From the closure-set point of view, `runWhileFixpoint` is computing a **fixpoint over closure sets as well as over pc/Γ/ℒ**: at each iteration, the closure set for a function-typed binding may grow as new alternatives are discovered, and the fixpoint is reached exactly when no new closures are added anywhere. Since there are only finitely many syntactic closures in the programme and we deduplicate, this closure-level fixpoint terminates together with the existing fixpoint on environments.

### 5.3 Guard-based de-poisoning in loops

Loop rules already support predicate-based de-poisoning via:

- matching guards in `while_depoison`,
- tracking a guard tag across iterations in `ℒ`,
- and an “agreement-only” policy at the back-edge.

With merged closures:

- predicates in function results after the loop are preserved only when **all alternatives agree** (both across branches inside the loop body and across iterations);
- if different iterations or branches justify different predicates for the same function value, the join drops to `no_pred`, matching the existing conservative philosophy.

This ensures that higher-order de-poisoning through loop-produced functions remains sound and is only as permissive as can be justified uniformly across all paths and iterations.

## 6. Application of closure lists

### 6.1 Typing rule

Application typing over non-empty closure sets is shared between Issues #63 and #64.

For an expression `e₁ e₂` where `e₁` has a function type with closure set:

- `ST₁ -> ST₂ # p_join typing_closures C`

the application rule:

1. Types `e₂` to obtain `QTyp` for the argument and updated environments.
2. For each alternative closure `tclᵢ` in the set:
   - re-types the body under:
     - the actual argument `QTyp`,
     - the current memory and tag environments,
     - the captured environment of `tclᵢ`;
   - obtains a result enriched type `QTᵢ` with `ETyp` and updated environments.
3. Requires the result `ETyp`s to be **signature-compatible** across all alternatives (same surface result type, and if they are themselves function types, same `ST₁`, `ST₂` there too).
4. Joins:
   - function poisons for the result (across alternatives and with caller pc),
   - memory and tag environments (using existing joins),
   - predicates using an “agreement-only” policy:
     - if all `QTᵢ` have the same predicate, keep it;
     - otherwise use `no_pred`.
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

- Adjust Preservation and Progress proofs to reason over merged closures:
  - for conditionals, show that the merged closure over branch closures suffices to cover both runtime possibilities;
  - for loops, use induction over the fixpoint iteration and the merged-closure invariant at the back-edge.
- Ensure that Non-interference treats merged closures as finite joins of alternatives, using the same per-alternative reasoning pattern as for other joins.

## 8. Summary

This proposal introduces **merged typing closures** as a unifying abstraction to resolve the unsoundness and inflexibility identified in Issues #63 and #64. Conditionals and while-loops both use merged closures at their joins, and application types **all possible closures** before conservatively joining results. The change is local to the typing and proof infrastructure: it does not affect the operational semantics of Poison programmes, but it restores a coherent higher-order story for de-poisoning and alias analysis across complex control flow.


