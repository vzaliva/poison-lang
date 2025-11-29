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

### Terminology and notation

This proposal distinguishes two kinds of heap identifiers:

| Concept | OTT | Lean | Description |
|---------|-----|------|-------------|
| Logical location | `l` | `Location` | Abstract name assigned by the typechecker |
| Concrete address | `a` | `Address` | Physical heap address assigned at runtime |

**OTT migration note:** The current OTT uses `l` for concrete addresses. Implementation requires renaming the existing `location, l` metavar to `address, a`, then introducing a new `location, l` metavar for logical locations.

We use `S` for sets of logical locations (e.g., `{l₁, l₂}`), `ρ` for the realisation map (`l ⇀ a`), and `Γ` for the logical memory typing environment (`l ⇀ Q`).

### 2.1 Logical memory locations

Instead of writing `ref T @ 0`, `ref T @ 1`, etc. with concrete addresses in types, we introduce **logical (abstract) locations**.

* Each allocation in the typing derivation introduces a fresh logical location `l`.
* Types for references become `ref T @ {l}` (singleton set), where `l` is **not** a runtime address but a logical name.
* The typing judgment uses:

  * `Γ : l ⇀ Q` - logical memory typing environment, mapping logical locations to qualified types.
  * `σ : Var ⇀ Q` - variable typing environment.

At runtime, we still allocate **concrete addresses** `a ∈ Address`. We relate logical locations to concrete addresses via a **realisation map**:

* For each run we maintain a partial map `ρ : l ⇀ a`.
* When a `new` executes along some path and the type system predicted a fresh logical `l`, we extend `ρ(l)` with the fresh concrete address `a`.

This decouples typing from the exact heap layout: types talk about logical locations; each run separately realises some of them as concrete addresses, possibly different across runs. Logical locations that arise only on paths not taken in a particular execution simply remain unrealised in that run.

### 2.2 Sets of possible logical locations

To handle joins like:

```poison
let x = ref 0 in      (* x : ref int @ {l₁} *)
let y = ref 1 in      (* y : ref int @ {l₂} *)
if c then x else y
```

we generalise reference types to carry **sets** of logical locations:

* Base case: `x : ref int @ {l₁}`, `y : ref int @ {l₂}`.
* Join case: `if c then x else y : ref int @ {l₁, l₂}`.

Intuitively, `ref T @ S` means "a pointer to *one of* the locations in `S`, each of which is a cell of type `T`". We do not try to pick a single distinguished location at the join; we explicitly record that both `l₁` and `l₂` are possible targets.

This preserves:

* Alias information: two variables with overlapping sets `S₁, S₂` may alias if `S₁ ∩ S₂ ≠ ∅`.
* Poison tracking at the level of locations: if any `l ∈ S` becomes poisoned, the analysis can conservatively treat `ref T @ S` as pointing to a (potentially) poisoned cell.

Conceptually, this is a standard abstract-interpretation move: sets of abstract addresses over-approximate possible aliasing and reachability in a flow-insensitive way.

### 2.3 Heap and world invariants

For each run we have:

* A concrete heap `μ : a ⇀ Value`.
* A realisation map `ρ : l ⇀ a`.
* A logical memory typing environment `Γ : l ⇀ Q`.

We say that a run **realises** a typing context (with logical memory typing `Γ` and variable typing `σ`) if:

1. For every logical `l` with `ρ(l) = a` defined, the heap has a cell `μ(a)` whose qualified type matches `Γ(l)`.
2. Dereferences and updates through values of type `ref T @ S` only ever use concrete addresses `a = ρ(l)` for some `l ∈ S`.
3. Logical locations may exist in `Γ` without a corresponding `ρ(l)` (paths not taken); they are simply unused ghosts in that run and do not affect observable behaviour.

The realisation map `ρ` satisfies two key properties:

* **Injectivity:** Distinct logical locations map to distinct concrete addresses (`l₁ ≠ l₂ ⇒ ρ(l₁) ≠ ρ(l₂)` when both are defined).
* **Monotonicity:** Once `ρ(l) = a` is established, it remains fixed throughout evaluation.

## 3. Impact on typing rules (high-level)

### 3.1 Allocation

The `ref` typing rule allocates a fresh logical location `l`, producing type `ref T @ {l}` and extending `Γ[l ↦ Q]`. 

At runtime, the big-step rule `b_ref` chooses a fresh concrete address `a`, and the realisation map is extended `ρ(l) := a`.

**Freshness tracking:** The typechecker's `nextLoc` counter generates fresh logical location identifiers. The big-step evaluator's `nextLoc` counter generates fresh concrete addresses. These are independent: the typechecker produces logical names, the runtime produces physical addresses, and `ρ` connects them.

### 3.2 Conditionals and joins

At joins, we now combine **types, location sets, and predicates**:

* If both branches have `ref T @ S₁` and `ref T @ S₂` respectively, the joined type is `ref T @ (S₁ ∪ S₂)`.
* Qualified types of each logical location are joined pointwise in the logical memory typing `Γ`:
  - Types must match (enforced by typing rules)
  - Poison status is joined conservatively (typically `p₁ ⊔ p₂`)
  - Predicates are joined (see Section 3.5 for predicate join semantics)

In particular:

```poison
let x = ref 0 in      (* x : ref int @ {l₁} *)
let y = ref 1 in      (* y : ref int @ {l₂} *)
if c then x else y    (* : ref int @ {l₁, l₂} *)
```

No new logical locations are introduced at the `if`; we just merge the sets. The runtime may only realise some subset of `{l₁, l₂}` in a given execution, depending on which allocations occurred.

This preserves the ability to track poison on both `l₁` and `l₂` across the whole program, and to reason that the result of the `if` may refer to either cell.

**Arrow types and references:** Arrow types `ST1 -> ST2` use surface types without location annotations. Function bodies are re-typechecked at application time (per existing Ott rules `app_fn` and `app_pfn`), so each call allocates fresh logical locations for any `ref` expressions in the body. Joins of function results follow the same location-set rules as conditionals.

Note: Function calls inside loops produce fresh locations per call, but these are scoped to the loop body (see Section 3.3) and do not escape.

### 3.3 Loops

Loops are treated via a fixpoint construction over the logical memory typing `Γ`, poison statuses, and the tag environment `L`.

#### Loop-internal allocations are scoped

A key observation is that allocations inside a loop body **cannot escape** the loop:

1. **Return type is `unit`:** The loop cannot return a reference.
2. **Memory holds only integers:** References cannot be stored in heap cells.
3. **Lexical scoping:** Variables bound inside the loop body go out of scope at the end of each iteration.

Therefore, logical locations created by `ref` expressions inside the loop body are relevant only for typing that iteration's body. They become **ghost locations** that need not persist across fixpoint iterations or appear in the loop's output environment.

#### Modified fixpoint computation

The standard fixpoint iteration `Γᵢ₊₁ = JoinG Γᵢ Γ²ᵢ` (where `Γ²ᵢ` is the environment after typing the body) is modified to:

```
Γᵢ₊₁ = JoinG Γᵢ (restrict Γ²ᵢ to dom(Γᵢ))
```

That is, before joining, we **restrict** the body's output environment to locations that existed *before* entering the body. Fresh allocations from the body are discarded—they served their purpose during body typing but cannot affect code outside the loop.

#### Termination argument

The fixpoint is guaranteed to terminate because the state space is finite and the iteration eventually stabilises:

1. **Finite location set:** The fixpoint iterates only over locations in the initial `Γ` (those existing before the loop). This set is finite and fixed.

2. **Tag environment shrinks monotonically:** The tag environment `L` can only lose entries over fixpoint iterations:
   - `JoinL` keeps only tags where both operands agree on the boolean value
   - `invalidate_deps` removes tags whose dependencies include a written location
   
   Although tags may be temporarily added when guards match (for typing the loop body), these additions don't survive `JoinL` unless the tag was already present in the input `L`. Since `L` is finite, it stabilises after finitely many iterations.

3. **Once `L` stabilises, the rest is monotonic:** After `L` reaches its fixpoint, de-poisoning behaviour becomes deterministic (the same guards are known true/false). From that point:
   - Poison status can only increase via `joinPoison` (or stay the same)
   - Predicates can only be lost via predicate joins (or stay the same)

4. **Finite state space:** Each location has finitely many possible qualified types (two poison values, finitely many predicate forms). Combined with the fixed location set, the total state space is finite.

In practice, simple loops reach a fixpoint in one or two iterations.

### 3.4 Dereference and assignment

Note: Reference types always carry `no_pred` (predicates apply only to stored values, not references). Memory only stores integers, so base types trivially match across location sets.

Dereference:

* **Typing level**: Given `ref T @ S`, look up `Γ(l)` for all `l ∈ S` to get the stored values' qualified types.
* **Conservative poison**: Result is poisoned if **any** `l ∈ S` has poisoned status in `Γ`.
* **Predicate handling**: The stored values may have different predicates; how to combine them is addressed in Section 3.5.
* **Runtime level**: The big-step rule `b_deref` reads from a single concrete cell; the type system's conservative approximation ensures soundness.

Assignment:

* The typing rule for assignment through `ref T @ S` updates `Γ` for **all** logical locations `l ∈ S`, storing the assigned value's qualified type (including predicate).
* This is a typing-level operation: `Γ[l₁ ↦ Q][l₂ ↦ Q]...` for all `l ∈ S`.
* At runtime, the big-step rule `b_assign` updates only the concrete heap cell(s) that are actually accessed.
* This is conservative but sound: if a pointer might alias several logical locations, the type system treats them all as potentially affected.

### 3.5 Guards and depoisoning

The Poison language's key feature is **depoisoning via predicates**. This section specifies how guards interact with location sets.

#### Predicate Merge Semantics

When combining predicates (at control flow joins, dereference through location sets, or guard matching), use the following merge rule:

1. **Exact match:** If `P₁ = P₂` (same tag and closure), preserve the predicate.
2. **Tag match:** If both have the same tag `k` but different closures, use `guard k` (losing the closure).
3. **Otherwise:** Use `no_pred`.

#### Dereference Through Location Sets

When dereferencing `ref T @ S` where `S = {l₁, ..., lₙ}`:
- Look up `Γ(lᵢ)` for each `lᵢ ∈ S`
- Poison status: conservative join of all poison statuses
- Predicate: merge all predicates using the rule above (pairwise, associatively)

#### Guard Matching with Location Sets

When `matchGuard` encounters a dereference `!x` where `x : ref T @ S`:
1. Merge predicates from all `Γ(l)` for `l ∈ S` using the merge rule above.
2. If the merged result is `no_pred`, no match is possible.
3. If the merged result has a tag `k` (either `guard k pred_closure ...` or `guard k`), attempt to match against that.

Rationale: depoisoning is safe only if all potential locations permit depoisoning with the same tag.

#### Assignment Predicate Update

When assigning through `ref T @ S`, all locations in `S` receive the assigned value's qualified type (including predicate). This is conservative but sound.

#### Alias-Aware Depoisoning

Depoisoning operates on `Γ`, not on individual references. If `x : ref int @ {l₁, l₂}` and `y : ref int @ {l₂, l₃}` share location `l₂`, and a guard updates `Γ(l₂)`, then both `x` and `y` see the updated qualified type when accessing `l₂`.

## 4. Impact on non-interference

The existing non-interference property (parameterised by guard regimes, critical inputs, and observable specifications) remains fundamentally unchanged. The adaptation to logical locations requires only one addition: **realisation maps**.

### 4.1 Adding realisation maps

The non-interference property compares two runs. With logical locations, each run maintains its own **realisation map** `ρ₁, ρ₂ : l ⇀ a` linking logical locations to concrete heap addresses.

**Key modification:** Where the existing formulation compares heap cells directly (`μ₁[a]` vs `μ₂[a]` for concrete address `a`), the adapted formulation compares via realisation maps: `μ₁[ρ₁(l)]` vs `μ₂[ρ₂(l)]` for logical location `l`.

**Key insight:** The two runs may have different realisation maps. One run might realise `l` at address `0x100` whilst the other realises it at `0x200`, or one run might realise `l` whilst the other does not (branch-dependent allocation). Non-interference does not require identical realisation—only that observable outputs agree.

### 4.2 Location sets and indistinguishability

For reference values of type `ref T @ S`:
- In each run, the value is a concrete address `aᵢ` such that `aᵢ = ρᵢ(l)` for some `l ∈ S`.
- The *choice* of `l` may differ between runs, as long as both choices are permitted by `S`.
- Observable locations store indistinguishable values (respecting the guard regime).

Example:
```poison
let x = ref 0 in      (* x : ref int @ {l₁} *)
let y = ref 1 in      (* y : ref int @ {l₂} *)
if c then x else y    (* : ref int @ {l₁, l₂} *)
```

If `c` evaluates differently in the two runs, one might return a pointer to `l₁`, the other to `l₂`. Non-interference permits this, provided both choices are in `{l₁, l₂}` and observable outputs remain indistinguishable.

### 4.3 Ghost locations

Logical locations that are never realised in a run (allocation on an untaken branch) are **ghost locations**:
- They appear in `Γ` but have no `ρ(l)` entry.
- No heap cell corresponds to them; no pointer can reference them.
- They do not affect observable behaviour.

The proof must show that unrealised locations do not break indistinguishability. Since they are ghosts, they contribute no observable effects.

**Runtime instantiation predicate:** The existing `runtimeInstantiatesCtx` predicate must be adapted. Instead of requiring all locations in `Γ` to exist in the heap, it should require only *realised* locations:

> For every logical `l ∈ dom(Γ)` with `ρ(l)` defined, the heap `μ` contains `ρ(l)` with a value matching `Γ(l)`.

Ghost locations (where `ρ(l)` is undefined) are excluded from this requirement.

**Monotonicity:** Realisation maps grow monotonically: once `ρ(l) = a` is established, it remains fixed throughout evaluation, ensuring stable correspondence between logical and concrete locations.


