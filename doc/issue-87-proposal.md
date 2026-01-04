## Issue 87 proposal: world-threaded FR step theorem with IO axioms for printing and randomness

### Problem Statement

The FR step theorem requires returned values to agree whenever the inferred result type is clean-under-\(R\). This obligation is problematic for `rand`/`frand` because their interpreter semantics call `IO.rand`, whose outcome depends on the `IO.RealWorld` token. Since the current step proof premises quantify `IO` worlds existentially (and independently) for the two executions, there is no principled way to relate the two random draws, so the proof cannot establish result equality even in clean cases.

### Summary

We will unblock the `rand`/`frand` cases in the Fault-Robustness (FR) step proof by (i) making the `IO` world token an explicit input/output in the step theorem premises (world threading), and (ii) adding a small set of axioms about the `IO` primitives used by the interpreter:

- **printing is argument-insensitive** at the level of world evolution, and
- **random sampling is deterministic** as a function of the world token and its bounds, and satisfies the expected range constraints.

This removes the need for a separate randomness oracle parameter: the `IO.RealWorld` token itself serves as the randomness state.

### Background: why the current proof is blocked

The big-step interpreter implements `Expr.rand` and `Expr.frand` using `IO.rand`. The current world-indexed termination predicate,

- `terminatesToW e c₀ c₁ o := ∃ fuel verbose w₀ w₁, beval fuel c₀ e verbose w₀ = ok ... w₁`,

quantifies the world token existentially, independently for each run. The internal FR step theorem (`StepFRW`) therefore receives two termination premises whose `IO` worlds are unrelated.

However, when the inferred result type is clean-under-\(R\), the step theorem requires the returned values to agree. For `rand` this forces equality of the two sampled integers, which cannot be derived without relating the two runs’ worlds.

### Proposal

#### 1) Thread worlds through the step theorem premises (input and output)

We will replace “existential worlds” termination premises with an explicit input-world form, so that the step theorem can take worlds as inputs and produce worlds as outputs. One convenient predicate is:

- `terminatesToWFrom (w : Void IO.RealWorld) e c₀ c₁ o := ∃ fuel verbose w', beval fuel c₀ e verbose w = ok ... w'`.

The FR step theorem will be reformulated to take a (single) shared input world `w` for the two runs and to return a **shared** output world `w'` (i.e. both runs are shown to advance the world in the same way). This makes “world synchronisation” a first-class induction invariant rather than an implicit side condition, and it is what allows the induction hypothesis to be chained through constructs such as `seq`.

#### 2) IO axioms (trusted semantic interface)

We will postulate axioms for the only IO operations used by the interpreter: printing (`IO.println` via `printInt`/`printString`) and random sampling (`IO.rand` via `rand`/`frand`). These axioms are chosen to be exactly what the FR proof needs, and no stronger.

**Axiom A (printing is argument-insensitive).** For any fixed input world `w`, all successful `IO.println` calls advance the world to the same output world, regardless of the printed argument. Equivalently, there exists a function `printStep : World → World` such that, for all printable arguments `a`,

- `IO.println a` (when it succeeds) transforms `w` into `printStep w`.

This axiom is justified because printing is not observationally relevant for FR: we intentionally model printing as “noise” which may advance the world but does not encode information about printed data into the randomness state.

**Axiom B (random sampling is deterministic, well-ranged, and bounds-insensitive on worlds).** For any fixed input world `w` and bounds, `IO.rand lo hi` has a unique successful outcome `(r, w')`, and the sampled value satisfies `lo ≤ r ≤ hi`. In the concrete interpreter, we only use `lo = 0`, so the relevant constraint is `0 ≤ r ≤ hi`.

Crucially for compositionality, the **world transition does not depend on the bounds**: there exists a function `randStep : World → World` such that every successful call `IO.rand lo hi` transforms `w` into `randStep w`, regardless of `lo` and `hi`.

In particular, if two runs reach the `IO.rand` call with the same world token and the same bounds, then they receive the same sampled value and the same post-world token. If they reach it with the same world token but **different** bounds (as can happen in both `rand` and `frand` when their argument is poisoned), the sampled values may differ, but the post-world token is still the same by bounds-insensitivity of `randStep`.

As an immediate corollary, the `Expr.frand` result is also predictable given the world token and its argument (since it is computed from a single `IO.rand` call). Importantly, `frand` is intended to model *faulty* randomness, so its output is not assumed to satisfy the “requested bound” predicate used for de-poisoning (e.g. it may fall outside the argument-supplied range).

These axioms together ensure that (i) differences in printed values do not desynchronise worlds, and (ii) randomness can be coupled by world equality.

#### 3) How this discharges `rand`/`frand` in the FR step proof

With worlds threaded and the IO axioms in place, the `rand` and `frand` proof cases proceed uniformly:

- Use the existing `bevalRand_structure` / `bevalFrand_structure` lemmas to expose the evaluation structure, including the world token immediately before the `IO.rand` call.
- Use the induction hypothesis to obtain agreement of the bound expression when its type is clean-under-\(R\).
- Apply Axiom B at the `IO.rand` call: the world advances to the shared post-world `randStep w` regardless of the bounds (so chaining through `seq` is preserved even if the argument is poisoned and the bounds differ). When the FR step theorem requires the returned value to agree (i.e. the result is clean-under-\(R\)), the bound expression is clean and thus equal across runs, so the bounds coincide and Axiom B yields equality of the sampled numbers.
- For any intervening printing, apply Axiom A to preserve world synchronisation even if printed arguments differ.

No additional “random oracle” parameter is required: the world token is the oracle state.

### Impact on existing code and proofs

This change is proof-focused but requires a systematic refactor of the step theorem plumbing:

- **`LeanProofs/FaultRobustnessProofs.lean`**
  - reformulate `StepFRW` (and all helper lemmas) to accept/input world tokens and produce/output world tokens,
  - propagate the world-threading through the induction hypothesis of `TypeSystemEnforcesFaultRobustness_stepW`,
  - use the IO axioms in the `rand`/`frand` branches (and, if necessary, in `printInt`/`printString` cases).
- **`LeanProofs/IOHelpers.lean` (or a new small file)**
  - state the IO axioms (printing argument-insensitive; `IO.rand` deterministic + range).

No changes to the interpreter are required.

### Soundness and interpretation

The resulting FR theorem is a statement about the Poison semantics *under the IO axioms above*. The intended reading is not “two completely independent executions”, but rather a *single execution environment* in which some inputs are fault-free and others are faulty, as determined by the regime \(R\). Concretely, the two-run proof compares two instantiations of the same programme run that share the same trusted environment (including the `IO` world), and may differ only on those critical inputs that \(R\) classifies as faulty.

In particular:

- it does **not** claim that two independent executions of the concrete interpreter (with independent external randomness) will return the same random values; and
- it *does* justify FR reasoning for fault injection: the only differences between the two executions are those permitted by \(R\), and all `IO` effects are modelled as coming from the same underlying world state, with printing treated as argument-insensitive.

This is an explicit trust boundary: the FR proofs reduce `rand`/`frand` reasoning to a small, auditable semantic interface for IO.


### Implementation Plan

1.  **Add IO Axioms directly to `FaultRobustnessProofs.lean`**
    - State **Axiom A** (printing) and **Axiom B** (randomness) as Lean axioms in `LeanProofs/FaultRobustnessProofs.lean`, alongside opaque step functions `printStep` and `randStep` (bounds-independent).

2.  **Modify Termination Predicates in place**
    - Instead of creating a new `terminatesToWFrom`, modify `terminatesToW` in `LeanProofs/SemanticsProperties.lean` to take explicit input and output worlds:
      `def terminatesToW (w₀ w₁ : Void IO.RealWorld) (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop`
    - Update the definition to assert `beval ... w₀ = ok ... w₁`.
    - **Refactor impacted lemmas in `SemanticsProperties.lean`**:
        - `terminatesToW_nextAddr_mono`: Update type signature and proof to use explicit world arguments.
        - `wfConfig_preservedW`: Update type signature and proof to use explicit world arguments.
        - Update other lemmas that depend on `terminatesToW` (e.g. `wfConfig_preservedW_*` family) to thread or quantify the world arguments appropriately.

3.  **Refactor `StepFRW` Definition**
    - Modify `StepFRW` in `LeanProofs/FaultRobustnessProofs.lean` to take a single shared input world argument `w`.
    - Update the termination premises to use the modified `terminatesToW` with `w` as the input world.
    - Add a shared output world `w'` to the existential result, ensuring both runs terminate to `w'`.

4.  **Update Structural Helper Lemmas**
    - Update `stepFRW_op`, `stepFRW_seq`, `stepFRW_if`, etc., to propagate the shared world token.
    - Ensure `seq` correctly passes the output world of the first statement as the input to the second.

5.  **Implement `rand` and `frand` Cases**
    - In `TypeSystemEnforcesFaultRobustness_stepW`, apply the IO axioms for `rand` and `frand`.
    - Prove that world synchronization is maintained via `randStep` even when arguments differ (poisoned inputs).
    - Prove that return values agree when inputs are equal (clean inputs).

6.  **Connect to Main Theorem**
    - Update `StepFR_of_StepFRW` to instantiate the initial world using `LeanProofs.defaultWorld` (from `IOHelpers.lean`) and verify the standard `StepFR` still holds by discarding the world threading.

### Documentation Updates

- **`poison-lang/doc/poison-lang-description.tex`**:
  - Add a new subsection under "Fault Robustness Theorem" describing the "World-Threaded Step Theorem".
  - Explain the IO axioms (argument-insensitive printing, bounds-insensitive randomness) and their justification.
  - Clarify that the theorem holds relative to a trusted IO environment.

- **`poison-lang/doc/IO_equality_approach.md`**:
  - Update the "World-indexed termination wrapper" section to reflect the new definition of `terminatesToW` (taking explicit input/output worlds) instead of the existential definition.
