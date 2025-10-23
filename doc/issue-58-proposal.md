# Issue 58: Proposal

## Problem Statement

In `NonInterference.lean`, the `qtypPredHolds` definition evaluates predicates using the current runtime environment `ρ` instead of the environment captured when the predicate was created. This breaks lexical scoping for predicates.

### The Bug

```lean
inductive qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop where
  | guardClosure_ok {qt : QTyp} {μ ρ v k arg_name pred_body var_env}
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hterm : terminatesTo (PExpr.toExpr pred_body)
                  { memory := μ, varEnv := VarEnv.update ρ arg_name v, ... }
                  cfg (Value.bool true)) :
      qtypPredHolds qt μ ρ v
```

The predicate is evaluated with the wrong environment `ρ`. The `var_env` parameter contains only typing information (`List (Name × QTyp)`), not runtime values.

### Example Demonstrating the Issue

```poison
let threshold = 100 in
let checkSensor = 
  extern fn s : (int) -> (int :> poisoned { guard k, v => v > 0 && v < threshold })
in
let threshold = 200 in  (* Shadows previous threshold *)
let readTemp = 
  extern fn t : (int) -> (int :> poisoned { guard h, v => v > 0 && v < threshold })
in
let temp = readTemp 0 in
if temp > 0 && temp < threshold then temp else 0
```

The predicates capture different values of `threshold`:
- `checkSensor`'s predicate captured `threshold = 100`
- `readTemp`'s predicate captured `threshold = 200`

When checking if predicates hold, `qtypPredHolds` incorrectly uses the current environment instead of the captured one.

## Architectural Constraint

The runtime has no access to tags or type information. This clean separation
between types and runtime values fundamentally constrains our solution options.

## Solution: Abstract Predicate Satisfaction

Instead of evaluating predicates concretely, treat predicate satisfaction as an abstract relation.

### Design

```lean
-- Abstract predicate satisfaction relation
-- Note: No VarEnv parameter! See explanation below.
variable (PredSat : Tag → Memory → Value → Prop)

-- Modify qtypPredHolds to use abstract satisfaction
inductive qtypPredHolds : QTyp → Memory → Value → (Tag → Memory → Value → Prop) → Prop where
  | guardClosure_ok {qt μ v k arg_name pred_body var_env predSat}
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hSat : predSat k μ v) :  -- Just check the abstract relation!
      qtypPredHolds qt μ v predSat
  | guardOnly_ok {qt μ v k predSat}
      (h : qt.pred = Predicate.guardOnly k)
      (hSat : predSat k μ v) :
      qtypPredHolds qt μ v predSat
  | noPred_ok {qt μ v predSat}
      (h : qt.pred = Predicate.noPred) :
      qtypPredHolds qt μ v predSat
```

`PredSat` omits a variable environment because tags uniquely identify both the
predicate and its captured lexical context at definition time; the current heap
may still matter, so `PredSat k μ v` depends on memory to account for
dereferences, but not on a runtime `ρ`. Encoding captured variables into the
meaning of the tag eliminates the environment‑capture bug without changing
runtime or typechecker architecture.

### The Axioms

We constrain `PredSat` through axioms that capture language mechanisms, NOT predicate meanings:

```lean
structure SatisfiesAxioms (PredSat : Tag → Memory → Value → Prop) : Prop where
  -- Syntactic matching: If condition matches predicate k and evaluates to true,
  -- then k is satisfied (regardless of what the predicate means!)
  match_sound : ∀ condition k μ ρ v,
    (TypeSystem.matchGuard condition returns k) →
    (terminatesTo condition {memory := μ, varEnv := ρ, ...} _ (Value.bool true)) →
    PredSat k μ v
    
  -- Memory monotonicity: Predicates stable under unrelated memory changes
  -- If a predicate only depends on certain memory locations (deps),
  -- and those locations haven't changed between μ and μ',
  -- then the predicate's truth value remains the same
  mem_monotone : ∀ k μ μ' v deps,
    PredicateDeps k deps →                    -- Type system computed that k reads from deps
    (∀ l ∈ deps, μ.lookup l = μ'.lookup l) → -- Those locations unchanged between μ and μ'
    (PredSat k μ v ↔ PredSat k μ' v)         -- Predicate satisfaction unchanged
```

Note: We do NOT axiomatize what specific predicates mean! This is crucial for
handling arbitrary extern functions.

### Non-Interference Formulation

```lean
def NonInterferenceSpec 
  (e : Expr) 
  (s : InputSpec) 
  (obs : ObservableSpec) 
  (ctx : TypeContext)
  (PredSat : Tag → Memory → Value → Prop)  -- Abstract parameter
  : Prop :=
  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    wfRegime R s →
    inputsConformSpec s μ₁ ρ₁ → inputsConformSpec s μ₂ ρ₂ →
    -- Use PredSat abstractly:
    consistentRegimeSpec PredSat R s μ₁ ρ₁ → 
    consistentRegimeSpec PredSat R s μ₂ ρ₂ →
    agreeOnCriticalInputsUnderRegime PredSat R s μ₁ ρ₁ μ₂ ρ₂ →
    terminatesTo e {memory := μ₁, varEnv := ρ₁, ...} cf₁ o₁ →
    terminatesTo e {memory := μ₂, varEnv := ρ₂, ...} cf₂ o₂ →
    observablesEqual obs cf₁ cf₂ o₁ o₂
```

### Why This Works

1. **Handles arbitrary predicates**: Users can define any predicate in extern functions
2. **Avoids the environment bug**: Never evaluates predicates, so no wrong environment
3. **Maintains soundness**: The axioms ensure `PredSat` behaves consistently with runtime
4. **Preserves architecture**: Respects the type/runtime separation

### Worked Example Using the Abstract Approach

Using the same example from above:
```poison
let threshold = 100 in
let checkSensor = 
  extern fn s : (int) -> (int :> poisoned { guard k, v => v > 0 && v < threshold })
in
let threshold = 200 in
let readTemp = 
  extern fn t : (int) -> (int :> poisoned { guard h, v => v > 0 && v < threshold })
in
let temp = readTemp 0 in
if temp > 0 && temp < threshold then temp else 0
```

The proof works without evaluating predicates:
- `checkSensor` has tag `k` (captured `threshold = 100`)
- `readTemp` has tag `h` (captured `threshold = 200`) 
- `matchGuard` identifies that `temp > 0 && temp < threshold` matches tag `h`
- If condition is true, axiom forces `PredSat h μ temp` to be true
- We never need to know that `h` captured `threshold = 200` - the abstract relation handles it correctly

### Theoretical Soundness

The abstract approach is sound because it replaces concrete predicate evaluation
with a relational parameter `PredSat` that is constrained only by mechanisms the
type system already enforces. The `match_sound` axiom aligns with the typing
rules that use `matchGuard`: whenever a condition syntactically matches a tagged
predicate and evaluates to true, the typing rules de‑poison values guarded by
that tag. `match_sound` records precisely that behavioural commitment without
appealing to any particular meaning of the predicate body or to a runtime
variable environment. 

The `mem_monotone` axiom mirrors the type system’s dependency tracking and
invalidation: dependencies extracted from predicate syntax are stored with tags;
assignments invalidate tags that depend on the written location. Requiring
`PredSat` to be invariant when those dependencies are unchanged ensures the
proof layer cannot assume more than the type system guarantees operationally.
Together, these axioms make the proofs parametric in the predicate meaning while
remaining extensionally consistent with runtime and typing behaviour, yielding
non‑interference theorems that hold for all interpretations of `PredSat`
satisfying the same operational constraints.

### Implementation Steps

1. **Thread PredSat through the specification**
   - Add `PredSat : Tag → Memory → Value → Prop` parameter to `NonInterferenceSpec_step`
   - Update all regime consistency and agreement predicates to use `PredSat` instead of concrete evaluation
   - Replace `qtypPredHolds` with the abstract version shown above

2. **Formalize the axioms**
   - Define `SatisfiesAxioms` structure with `match_sound` and `mem_monotone`
   - Define `PredicateDeps` to track which memory locations each predicate reads (using existing `extractDepsFromPred`)

3. **Update the main theorem**
   - Change the theorem to quantify over all `PredSat` satisfying the axioms:
     ```lean
     theorem TypeSystemEnforcesNonInterference :
       ∀ (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext),
         (∃ fuel res, typecheck ctx e fuel = .ok res ∧ ObsConstraints obs res) →
         ∀ (PredSat : Tag → Memory → Value → Prop),
           SatisfiesAxioms PredSat →
           NonInterferenceSpec e s obs ctx PredSat
     ```

4. **Connect type system to axioms**
   - Prove that when `matchGuard` identifies a match and the condition is true, `match_sound` applies
   - Ensure dependency tracking from the type system aligns with `PredicateDeps` used in `mem_monotone`

5. **Clean up**
   - Remove all concrete predicate evaluation from the proof layer
   - Document that only the type checker examines predicate syntax; proofs treat them abstractly