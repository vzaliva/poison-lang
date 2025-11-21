# Proposal: Logical Locations and Location-Set Types for Flow-Insensitive Poison Analysis

## 1. Aim and context

The current type system uses **concrete locations** in types (e.g. `ref T @ l`) and a **flow-insensitive join** over branches and loops. This leads to two related problems:

1. **Static vs runtime mismatch:** the typing context may mention locations that are not actually allocated in a given execution path, which breaks the current "heap instantiates context" invariant and complicates the non-interference proof.

2. **Join ambiguity for existing references:** even when no new allocation happens, joins such as

```poison
   let a = ref 0 in
   let b = ref 1 in
   if c then a else b
```

require a single type for the `if` expression, but branches refer to different locations (`a` vs `b`), making the result type ambiguous if we insist on a single `@ l`.

At the same time, simply “forgetting” location information at joins (e.g. dropping `@ l`) would sacrifice too much precision for tracking aliasing and poison propagation.

This proposal sketches a higher-level design that:

* Replaces **concrete locations in types** by **logical (abstract) locations**.
* Generalises reference types to carry **sets of possible locations**.
* Adapts the semantic invariants and non-interference property to work with these logical locations and sets, without requiring literal equality between type-checker locations and runtime addresses.

The goal is to preserve the current flow-insensitive flavour and precision of poison tracking, while repairing the soundness and non-interference story.

## 2. Core idea

### 2.1 Logical memory locations

Instead of writing `ref T @ 0`, `ref T @ 1`, etc. with concrete addresses in types, we introduce **logical (abstract) locations**:

Let `Λ` be a countably infinite set of logical location symbols `{α, β, γ, ...}`.

* Each allocation in the typing derivation introduces a fresh logical location symbol from `Λ`.
* Types for references become `ref T @ {α}` (singleton set), where `α` is **not** a runtime address but a logical name.
* The typing judgment uses:

  * `Γ : Λ ⇀ QTyp` - logical memory typing environment, representing the qualified type (type, poison status, and predicate) of each logical cell.
  * `σ : Var ⇀ QTyp` - variable typing environment.

At runtime, we still allocate **concrete addresses** `ℓ ∈ Addr`. We relate logical locations to concrete addresses via a **realisation map**:

* For each run we maintain a partial map `ρ : Λ ⇀ Addr`.
* When a `new` executes along some path and the type system predicted a fresh logical `α`, we extend `ρ(α)` with the fresh concrete address `ℓ`.

This decouples typing from the exact heap layout: types talk about `α`, `β`, …; each run separately realises some of them as concrete addresses, possibly different across runs. Logical locations that arise only on paths not taken in a particular execution simply remain unrealised in that run.

### 2.2 Sets of possible logical locations

To handle joins like:

```poison
let a = ref 0 in      (* a : ref int @ {α} *)
let b = ref 1 in      (* b : ref int @ {β} *)
if c then a else b
```

we generalise reference types to carry **sets** of logical locations:

* Base case: `a : ref int @ {α}`, `b : ref int @ {β}`.
* Join case: `if c then a else b : ref int @ {α, β}`.

Intuitively, `ref T @ S` means “a pointer to *one of* the locations in `S`, each of which is a cell of type `T`”. We do not try to pick a single distinguished location at the join; we explicitly record that both `α` and `β` are possible targets.

This preserves:

* Alias information: two variables with overlapping sets `S₁, S₂` may alias if `S₁ ∩ S₂ ≠ ∅`.
* Poison tracking at the level of locations: if any `α ∈ S` becomes poisoned, the analysis can conservatively treat `ref T @ S` as pointing to a (potentially) poisoned cell.

Conceptually, this is a standard abstract-interpretation move: sets of abstract addresses over-approximate possible aliasing and reachability in a flow-insensitive way.

### 2.3 Heap and world invariants

For each run we have:

* A concrete heap `μ : Addr ⇀ Value`.
* A realisation map `ρ : Λ ⇀ Addr`.
* A logical memory typing environment `Γ : Λ ⇀ QTyp`.

We say that a run **realises** a typing context (with logical memory typing `Γ` and variable typing `σ`) if:

1. For every logical `α` with `ρ(α) = ℓ` defined, the heap has a cell `μ(ℓ)` whose qualified type (type, poison status, and predicate) matches `Γ(α)`.
2. Dereferences and updates through values of type `ref T @ S` only ever use concrete addresses `ℓ = ρ(α)` for some `α ∈ S`.
3. Logical locations may exist in `Γ` without a corresponding `ρ(α)` (paths not taken); they are simply unused ghosts in that run and do not affect observable behaviour.

## 3. Impact on typing rules (high-level)

### 3.1 Allocation

The `ref` typing rule changes to allocate a fresh logical location `α` instead of a concrete address `l`, producing type `ref T @ {α}` and extending `Γ[α ↦ Q]`. 

At runtime, the big-step rule `b_ref` chooses a fresh concrete `ℓ`, and the realisation map is extended `ρ(α) := ℓ`.

### 3.2 Conditionals and joins

At joins, we now combine **types, location sets, and predicates**:

* If both branches have `ref T @ S₁` and `ref T @ S₂` respectively, the joined type is `ref T @ (S₁ ∪ S₂)`.
* Qualified types of each logical location are joined pointwise in the logical memory typing `Γ`:
  - Types must match (enforced by typing rules)
  - Poison status is joined conservatively (typically `p₁ ⊔ p₂`)
  - Predicates are joined (see Section 3.5 for predicate join semantics)

In particular:

```poison
let a = ref 0 in      (* a : ref int @ {α} *)
let b = ref 1 in      (* b : ref int @ {β} *)
if c then a else b    (* : ref int @ {α, β} *)
```

No new logical locations are introduced at the `if`; we just merge the sets. The runtime may only realise some subset of `{α, β}` in a given execution, depending on which allocations occurred.

This preserves the ability to track poison on both `α` and `β` across the whole program, and to reason that the result of the `if` may refer to either cell.

**Arrow types and references:** Arrow types `ST1 -> ST2` in the current system use surface types for parameter and return types, which include `ref ST` but not location annotations. With logical locations:
TODO: review this section
- Function bodies are re-typechecked at application time (per existing Ott rules `app_fn` and `app_pfn`), so each call allocates fresh logical locations for any `ref` expressions in the body.
- If a function returns a reference type `ref T @ {α}`, each call produces a distinct logical location `α₁, α₂, ...` in `Γ`.
- Joins of function results follow the same location-set rules: `(if c then f x else g y) : ref T @ S` where `S` is the union of locations from both branches.
- The typing closure mechanism ensures location freshness is maintained across multiple applications.

### 3.3 Loops

Loops are treated similarly to conditionals via a standard fixpoint construction over:

* The logical memory typing `Γ`.
* The per-expression types containing location sets.

At each iteration in the analysis, we:

* Extend `Γ` with any new logical locations created by the body.
* Join poison statuses and location sets.

The fixpoint `Γ*` is then used as the loop's post-environment. At runtime, only zero or finitely many of the corresponding logical locations may be realised, depending on the number of actual iterations; the unrealised ones remain ghosts.

**Termination of fixpoint iteration:** The fixpoint is guaranteed to terminate because:
TODO: review this section
1. Each iteration can add only finitely many fresh logical locations (bounded by allocation sites in the loop body).
2. Location sets and poison statuses form finite lattices with finite ascending chains.
3. The iteration reaches a fixpoint when no new logical locations are introduced and all poison statuses stabilise.

In practice, simple loops reach fixpoint in one or two iterations; loops with
complex allocation patterns may require more iterations but remain bounded by
the syntactic structure of the program.

### 3.4 Dereference and assignment

Dereference:

* **Typing level**: Given `ref T @ S`, the typing rule looks up all `Γ(α)` for `α ∈ S`, ensuring types match and computing the result's poison status and predicate.
* **Conservative poison**: The result is poisoned if **any** `α ∈ S` has poisoned status in `Γ`, preserving the "taint everything that might be tainted" philosophy.
* **Predicate handling**: Result predicate depends on agreement across location set (see Section 3.5 for detailed semantics).
* **Runtime level**: The big-step rule `b_deref` reads from a single concrete heap cell; the type system's conservative approximation ensures soundness.

Assignment:

* The typing rule for assignment through `ref T @ S` updates `Γ` for **all** logical locations `α ∈ S`, storing the assigned value's qualified type (including predicate).
* This is a typing-level operation: `Γ[α₁ ↦ Q][α₂ ↦ Q]...` for all `α ∈ S`.
* At runtime, the big-step rule `b_assign` updates only the concrete heap cell(s) that are actually accessed.
* This is conservative but sound: if a pointer might alias several logical locations, the type system treats them all as potentially affected.

### 3.5 Guards and depoisoning (critical design point)

**This section requires detailed design and is a blocker for implementation.**

The Poison language's key feature is **depoisoning via predicates** (e.g., `guard(x > 0)` depoisoning values or locations). The interaction between guards, location sets, and qualified types is central to the language's utility but remains underspecified.

#### Qualified Types in Logical Memory

Since `Γ : Λ ⇀ QTyp`, each logical location `α` stores a complete qualified type `T :> p {P}` including:
- Base type `T`
- Poison status `p`
- Predicate `P` (which may be `guard k pred_closure ...`, `guard k`, or `no_pred`)

This raises several design questions when working with location sets:

#### Key Questions to Resolve

1. **Predicate join semantics:** When joining `Γ(α) = T :> p₁ {P₁}` and `Γ(β) = T :> p₂ {P₂}` at control flow merge points:
   - If `P₁ = P₂` (same guard tag and closure), preserve the predicate?
   - If predicates differ, use `no_pred` (conservative)?
   - If one has `guard k pred_closure` and other has `guard k` (same tag), use `guard k`?
   - Current system (Section 3.2) uses conservative join similar to the existing `joinMemEnvs`

2. **Dereference predicate selection:** Given `ref T @ {α, β}` where `Γ(α)` and `Γ(β)` have different predicates:
   - Use `no_pred` (most conservative)?
   - Require all predicates in the set to agree?
   - Create a disjunction of predicates?
   - Use guard-only if tags agree but closures differ?

3. **Guard matching with location sets:** Current `matchGuard` looks for predicates in variables and dereferenced locations. With location sets:
   - Does `matchGuard` need to handle the case where a reference points to multiple locations with different predicates?
   - Should matching fail if predicates in the set disagree?
   - Can matching succeed if some (but not all) locations in a set have matching predicates?

4. **Depoisoning scope:** When a guard executes on a value of type `ref T @ {α, β}`:
   - Does the guard depoison all locations in the set `{α, β}`?
   - Only the locations whose predicates match?
   - Only the specific location accessed at runtime (unknowable statically)?

5. **Partial depoisoning:** Can guards selectively depoison a subset of locations in a set? For example:
   ```poison
   (* Suppose Γ(α) has predicate "guard k1 (x >= 0)" and Γ(β) has "guard k2 (x >= 10)" *)
   let c = if ... then a else b;  (* c : ref int @ {α, β} *)
   if !c >= 0 then ...             (* matches k1 but not k2: depoisons only α? *)
   ```
   Should the dereference in the then-branch be treated as clean (α depoisoned), poisoned (β still poisoned), or require both guards to match?

6. **Assignment predicate update:** When assigning through `ref T @ S`, all realised locations in `S` are updated. Should they:
   - All receive the same predicate from the assigned value?
   - Preserve their individual predicates?
   - Use conservative `no_pred`?

7. **Alias-aware depoisoning:** If two variables have overlapping location sets, does a guard on one affect the other? For example:
   ```poison
   (* x : ref int @ {α, β}, y : ref int @ {β, γ} - they share β *)
   if !x >= 0 then ...  (* guard matches predicate on x *)
   ```
   Should location `β` be depoisoned for both `x` and `y`, or only for `x`? Does the guard apply to all locations in `x`'s set, and does that transitively affect `y`?

#### Placeholder Approaches (to be refined)

**Option A: Conservative predicate erasure**
- At joins: use `no_pred` unless predicates are identical
- At dereference: use `no_pred` for location sets with multiple elements
- Guards only match singleton location sets `{α}`
- **Pro:** Simple, sound, maintains current precision for non-aliasing cases
- **Con:** May lose precision in presence of location set merging

**Option B: Guard-tag preservation**
- At joins: preserve guard tag if tags match, even if closures differ (downgrade to `guard k`)
- At dereference: use `guard k` if all locations in set have same tag `k`
- Guards can match on tag agreement
- **Pro:** More permissive, allows depoisoning in more cases
- **Con:** More complex, may be unsound if guard-only semantics are unclear

**Option C: Predicate sets**
- Track all predicates from all locations: `ref T @ S` has type `T :> p {P₁, P₂, ...}`
- Dereference is poisoned if any location's predicate fails
- Guards must satisfy all predicates to depoison
- **Pro:** Maximum precision
- **Con:** Significant complexity in type system and proofs

## 4. Impact on non-interference

The existing non-interference property (parameterised by guard regimes, critical inputs, and observable specifications) remains fundamentally unchanged. The adaptation to logical locations requires only one addition: **realisation maps**.

TODO: explore Kripke worlds relation

### 4.1 Adding realisation maps

The non-interference property compares two runs. With logical locations, each run maintains its own **realisation map** `ρ₁, ρ₂ : Λ ⇀ Addr` linking logical locations to concrete heap addresses.

**Key modification:** Where the existing formulation compares heap cells directly (`μ₁[ℓ]` vs `μ₂[ℓ]` for concrete location `ℓ`), the adapted formulation compares via realisation maps: `μ₁[ρ₁(α)]` vs `μ₂[ρ₂(α)]` for logical location `α`.

**Key insight:** The two runs may have different realisation maps. One run might realise `α` at address `0x100` whilst the other realises it at `0x200`, or one run might realise `α` whilst the other does not (branch-dependent allocation). Non-interference does not require identical realisation—only that observable outputs agree.

### 4.2 Location sets and indistinguishability

For reference values of type `ref T @ S`:
- In each run, the value is a concrete address `ℓᵢ` such that `ℓᵢ = ρᵢ(α)` for some `α ∈ S`.
- The *choice* of `α` may differ between runs, as long as both choices are permitted by `S`.
- Observable locations store indistinguishable values (respecting the guard regime).

Example:
```poison
let a = ref 0 in      (* a : ref int @ {α} *)
let b = ref 1 in      (* b : ref int @ {β} *)
if c then a else b    (* : ref int @ {α, β} *)
```

If `c` evaluates differently in the two runs, one might return a pointer to `α`, the other to `β`. Non-interference permits this, provided both choices are in `{α, β}` and observable outputs remain indistinguishable.

### 4.3 Ghost locations

Logical locations that are never realised in a run (allocation on an untaken branch) are **ghost locations**:
- They appear in `Γ` but have no `ρ(α)` entry.
- No heap cell corresponds to them; no pointer can reference them.
- They do not affect observable behaviour.

The proof must show that unrealised locations do not break indistinguishability. Since they are ghosts, they contribute no observable effects.

**Monotonicity:** Realisation maps grow monotonically: once `ρ(α) = ℓ` is established, it remains fixed throughout evaluation, ensuring stable correspondence between logical and concrete locations.


