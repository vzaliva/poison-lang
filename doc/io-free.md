# I/O-free fault-robustness proof plan

## Overview

**Scope:** Prove fault-robustness for expressions excluding I/O primitives and externs.

**Approach:** 
- Delete I/O axioms and I/O-specific proofs
- Refactor non-I/O proofs from world-threaded to world-free (semi-mechanical transformation)
- Replace top-level theorems with IOFree-restricted versions

**Effort:** Medium (5-9 days) - refactoring existing proofs is much faster than rebuilding from scratch.

## Purpose and scope

This note outlines a concrete plan to complete the remaining fault-robustness proofs by **excluding I/O from the proven fragment**. The mechanised theorem will cover an **I/O-free core** of Poison expressions and will not attempt to establish world-synchronisation properties for:

- `rand`
- `frand`
- `printInt`
- `printString`
- `externVal`, `externFn`, `externPfn`

The intent is to preserve the main contribution (typestate-based fault propagation/isolation with predicates, regimes, dependency invalidation, typing closures, etc.) whilst avoiding the substantial additional proof engineering required to reason relationally about Lean's `IO` world token.

This plan is motivated by the world-synchronisation obstruction described in `doc/worldsync-issue.md`: poisoned control flow can take different branches across two runs, which can lead to different numbers of I/O actions (e.g. `if b then rand () else nop`) and hence genuine world divergence. A single-world step theorem is then not compositional for sequencing.

**Rationale for excluding externs:** The current evaluator (`beval`) returns `runtimeError` for all extern constructs. Since `terminatesTo` is defined to require `.success` (not stuck/error states), extern constructs cannot appear in any `terminatesTo` execution. Including them in the proven fragment would provide no additional coverage. They are excluded from `IOFree` for simplicity.

## Key design choice

Rather than completing the world-threaded proof development (`StepFRW` with I/O axioms), we will:

1. **Delete** I/O-specific code:
   - I/O axioms (`io_println_step`, `io_rand_step`, etc.)
   - I/O structure lemmas and proof cases
   - Obsolete infrastructure (`StepFRW`, conversion lemmas)

2. **Refactor** non-I/O proofs from world-threaded to world-free:
   - For each `stepFRW_*` lemma (op, ite, newRef, assign, seq, vlet, fn, app, etc.)
   - Remove world-threading "plumbing" (world parameters, `terminatesToW`, sync proofs)
   - Keep core type reasoning logic intact
   - This is semi-mechanical transformation, not reproving from scratch

3. **Define** `IOFree : Expr → Prop` predicate

4. **Prove** modified theorems with `IOFree e` premise

**Key insight:** The existing world-threaded proofs for non-I/O constructs contain world-free core logic. We refactor these proofs by removing world-threading machinery while preserving the core logic, saving significant effort compared to reproving everything.

**Important:** This is a refactoring approach, not rebuilding from scratch. The type reasoning, memory extension logic, and agreement proofs remain largely intact—we're simply removing world tokens and related plumbing.

## Relevant existing infrastructure

### Two termination relations already exist

In `LeanProofs/SemanticsProperties.lean`:

- `terminatesTo` (world-free): evaluation returns a pure `EvalResult.success`.
- `terminatesToW` (world-indexed): evaluation is a function on `Void IO.RealWorld`.

### A world-free step theorem is already defined

`LeanProofs/FaultRobustnessProofs.lean` already defines `StepFR` in terms of `terminatesTo`:

```82:110:LeanProofs/FaultRobustnessProofs.lean
def StepFR (ctx : TypeContext) (R : Regime) (e : Expr) (res : TypeResult) (predSat : PredSat) : Prop := ...
```

This is the version we will use.

## Implementation plan

### 1) Introduce an I/O-free predicate on expressions

Define an inductive predicate `IOFree : Expr → Prop` in a new file `LeanProofs/IOFree.lean`.

**Design:**

The predicate is defined by providing constructors for all permitted expression forms. An expression is I/O-free if it can be built using only these constructors.

**Excluded constructors** (no corresponding `IOFree` case):
- `Expr.rand : Expr → Expr`
- `Expr.frand : Expr → Expr`
- `Expr.printString : Expr → Expr`
- `Expr.printInt : Expr → Expr`
- `Expr.externVal : Typ → Bool → SyntaxPredicate → Expr`
- `Expr.externFn : Name → Typ → ExternReturn → List Effect → Expr`
- `Expr.externPfn : Name → Typ → ExternReturn → Expr`

**Key design decisions:**

1. **Function bodies are checked recursively:** For both `Expr.fn` and `Expr.pfn`, the constructors require `IOFree body`. This prevents indirect I/O calls through closures:
   ```lean
   | fn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
       (hbody : IOFree body) : 
       IOFree (Expr.fn arg st1 body st2)
   
   | pfn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
       (hbody : IOFree body) :
       IOFree (Expr.pfn arg st1 body st2)
   ```

2. **Decidable companion function:** Also define `ioFree : Expr → Bool` that mirrors the inductive definition, and prove `ioFree_iff_IOFree : ioFree e = true ↔ IOFree e`. The Boolean version is useful for testing and conditional compilation; the inductive version is used in proofs.

**File structure (actual constructor names from `LeanPoison/Syntax.lean`):**

```lean
-- LeanProofs/IOFree.lean
import LeanPoison.Syntax

inductive IOFree : Expr → Prop where
  | num (n : Int) : IOFree (Expr.num n)
  | bool (b : Bool) : IOFree (Expr.bool b)
  | unit : IOFree Expr.unit
  | str (s : String) : IOFree (Expr.str s)
  | var (x : Name) : IOFree (Expr.var x)
  | op (e₁ : Expr) (o : Op) (e₂ : Expr) 
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) : 
      IOFree (Expr.op e₁ o e₂)
  | unaryop (o : UnaryOp) (e : Expr)
      (h : IOFree e) :
      IOFree (Expr.unaryop o e)
  | ite (e₁ e₂ e₃ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) (h₃ : IOFree e₃) :
      IOFree (Expr.ite e₁ e₂ e₃)
  | kwhile (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.kwhile e₁ e₂)
  | newRef (e : Expr) (h : IOFree e) : IOFree (Expr.newRef e)
  | deref (e : Expr) (h : IOFree e) : IOFree (Expr.deref e)
  | assign (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.assign e₁ e₂)
  | seq (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.seq e₁ e₂)
  | vlet (x : Name) (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.vlet x e₁ e₂)
  | fn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
      (hbody : IOFree body) :
      IOFree (Expr.fn arg st1 body st2)
  | pfn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
      (hbody : IOFree body) :
      IOFree (Expr.pfn arg st1 body st2)
  | app (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.app e₁ e₂)
  -- No cases for: rand, frand, printInt, printString, 
  --               externVal, externFn, externPfn

def ioFree : Expr → Bool := ...  -- recursive Boolean version

theorem ioFree_iff_IOFree (e : Expr) : ioFree e = true ↔ IOFree e := ...
```

**Proof use:**

Every inductive proof over expression structure or typing results can carry a hypothesis `hio : IOFree e`; subcases obtain `IOFree` premises for subexpressions via inversion on `hio`. The I/O-excluded cases cannot arise, simplifying case analysis.

### 2) Define the I/O-free fault-robustness theorem

Define a new top-level theorem `TypeSystemEnforcesFaultRobustness_IOFree` that adds the `IOFree e` premise.

**Note:** The theorem names below match actual definitions in `LeanProofs/FaultRobustness.lean` and `LeanProofs/FaultRobustnessProofs.lean`.

**Current situation (will be modified):**
- `TypeSystemEnforcesFaultRobustness_impl` (line ~510) takes `∀ e ctxᵢ predSat, step_spec e ctxᵢ predSat` as premise
- We can only provide `∀ e, IOFree e → step_spec e ctxᵢ predSat`
- So we need a modified impl that accepts the IOFree restriction

```lean
-- Modified impl that accepts IOFree restriction
theorem TypeSystemEnforcesFaultRobustness_impl_IOFree :
  (∀ e ctxᵢ predSat, IOFree e → TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat) →
  (∀ e s obs, IOFree e → TypeSystemEnforcesFaultRobustness_spec e s obs) := by
  -- Proof structure identical to current impl, just threads IOFree assumption
  sorry

-- Main theorem
theorem TypeSystemEnforcesFaultRobustness_IOFree 
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  IOFree e →
  TypeSystemEnforcesFaultRobustness_spec e s obs := by
  intro hio
  apply TypeSystemEnforcesFaultRobustness_impl_IOFree
  · intro e' ctxᵢ predSat hio'
    exact TypeSystemEnforcesFaultRobustness_step_IOFree e' ctxᵢ predSat hio'
  · exact hio
```

This makes the scope restriction explicit throughout the proof chain.

### 3) Prove the I/O-free step theorem

Define and prove `TypeSystemEnforcesFaultRobustness_step_IOFree`, which proves the step spec for IOFree expressions:

```lean
theorem TypeSystemEnforcesFaultRobustness_step_IOFree
  (e : Expr) (ctxᵢ : TypeContext) (predSat : PredSat) :
  IOFree e →
  TypeSystemEnforcesFaultRobustness_step_spec e ctxᵢ predSat := by
  intro hio
  unfold TypeSystemEnforcesFaultRobustness_step_spec
  intro fuel res htc R
  -- Prove StepFR by induction on the typecheck derivation
  -- The IOFree hypothesis hio eliminates all I/O cases
  sorry
```

**Critical fact:** `TypeSystemEnforcesFaultRobustness_step_spec` (line 115-122) already specifies `StepFR`, not `StepFRW`. The current implementation proves it by:
1. Proving `StepFRW` (uses I/O axioms, world-threading, `terminatesToW`)
2. Converting to `StepFR` via `StepFR_of_StepFRW`

**For IOFree, we bypass this entirely:** Prove `StepFR` directly without world-threading.

**Current proof infrastructure (will be deleted):**
```
TypeSystemEnforcesFaultRobustness_stepW
  → proves StepFRW (uses I/O axioms, terminatesToW)
  → 41 references to terminatesToW
  → 29 references to StepFRW
  → bevalPrintString/Int/Rand/Frand_structureW helper lemmas
  ↓
StepFR_of_StepFRW (conversion lemma)
  ↓
TypeSystemEnforcesFaultRobustness_step (combines above)
  ↓
TypeSystemEnforcesFaultRobustness_impl
  ↓
TypeSystemEnforcesFaultRobustness (main theorem)
```

**New IOFree proof chain:**
```
TypeSystemEnforcesFaultRobustness_step_IOFree
  → proves StepFR directly (no worlds, no I/O axioms)
  → uses terminatesTo only (world-free)
  → IOFree premise eliminates I/O cases
  ↓
TypeSystemEnforcesFaultRobustness_impl_IOFree (modified impl)
  ↓
TypeSystemEnforcesFaultRobustness_IOFree (main theorem)
```

**Key differences:**
- No world tokens (`w₀`, `w₁`) anywhere in the proof
- Use `terminatesTo` (world-free) instead of `terminatesToW`
- I/O cases (`rand`, `frand`, `printInt`, `printString`, externs) eliminated by `IOFree` assumption
- No I/O axioms referenced

**Implementation strategy:**

For non-I/O cases, use the existing `stepFRW_*` proofs as templates:

1. **Example: stepFRW_op → stepFR_op transformation**
   
   Before (world-threaded, lines 2601-2700):
   ```lean
   private lemma stepFRW_op ... (w : RealWorld) ... :
     StepFRW ctx R (Expr.op e1 op e2) res predSat := by
     ...
     have ht₀_e1 : terminatesToW w w₀mid e1 cfg₀ cfg₀1 v₀1 := ...
     have ht₁_e1 : terminatesToW w w₁mid e1 cfg₁ cfg₁1 v₁1 := ...
     have hstep_e1 := hIH1 w ... w₀mid w₁mid ht₀_e1 ht₁_e1
     have hw_mid : w₀mid = w₁mid := ... -- world sync proof
     have ht₀_e2 : terminatesToW w₀mid w₀' e2 ...
     have ht₁_e2 : terminatesToW w₀mid w₁' e2 ... := by
       subst hw_mid  -- world rewrite
       ...
     have hstep_e2 := hIH2 w₀mid ... w₀' w₁' ht₀_e2 ht₁_e2
     have hw_out : w₀' = w₁' := ... -- world sync proof
     ...
   ```
   
   After (world-free):
   ```lean
   private lemma stepFR_op ... :
     StepFR ctx R (Expr.op e1 op e2) res predSat := by
     ...
     have ht₀_e1 : terminatesTo e1 cfg₀ cfg₀1 v₀1 := ...
     have ht₁_e1 : terminatesTo e1 cfg₁ cfg₁1 v₁1 := ...
     have hstep_e1 := hIH1 ... ht₀_e1 ht₁_e1
     -- no world sync needed
     have ht₀_e2 : terminatesTo e2 ...
     have ht₁_e2 : terminatesTo e2 ... 
     -- no world rewrite needed
     have hstep_e2 := hIH2 ... ht₀_e2 ht₁_e2
     -- no world sync needed
     ...
   ```
   
   Core logic (type agreement, memory extension, etc.) remains identical.

2. **Apply same transformation to all non-I/O cases:** ite, newRef, assign, seq, vlet, fn, pfn, app, kwhile, deref, unaryop

3. **Skip I/O cases entirely:** IOFree assumption makes them impossible

### 4) Remove entire world-threaded development

The file `FaultRobustnessProofs.lean` currently contains extensive world-threaded infrastructure that must be removed:

**Scope of removal (statistics):**
- 41 references to `terminatesToW` (world-indexed termination)
- 29 references to `StepFRW` (world-threaded step theorem)
- ~2500+ lines of world-threaded proofs

**What must be deleted:**

1. **I/O axioms** (section `IO_Axioms`, lines 20-52):
   - `printStep`, `randStep`, `io_println_step`, `io_rand_step`

2. **I/O-specific structure lemmas** (lines ~3815-4057):
   - `bevalPrintString_structureW`, `bevalPrintInt_structureW`
   - `bevalRand_structureW`, `bevalFrand_structureW`

3. **I/O-specific cases in main proof:**
   - Cases for `rand`, `frand`, `printInt`, `printString`, externs

4. **Obsolete infrastructure after refactoring:**
   - `StepFRW` definition (replaced by using `StepFR` directly)
   - `StepFR_of_StepFRW` conversion lemma (no longer needed)
   - `TypeSystemEnforcesFaultRobustness_step_specW` (replaced by using `step_spec` directly)
   - Current `TypeSystemEnforcesFaultRobustness_step` (lines 4933-4940)
   - Current `TypeSystemEnforcesFaultRobustness_impl` (line 510) - replaced by `_impl_IOFree`
   - Current `TypeSystemEnforcesFaultRobustness` (line 4944) - replaced by `_IOFree` version

**What to refactor (not delete):**

1. **Non-I/O expression cases:** Transform `stepFRW_*` lemmas to `stepFR_*`:
   - `stepFRW_op` → `stepFR_op` (remove world plumbing, keep core logic)
   - `stepFRW_ite` → `stepFR_ite`
   - `stepFRW_newRef` → `stepFR_newRef`
   - `stepFRW_assign` → `stepFR_assign`
   - `stepFRW_seq` → `stepFR_seq`
   - `stepFRW_vlet` → `stepFR_vlet`
   - `stepFRW_fn` → `stepFR_fn`
   - `stepFRW_app` → `stepFR_app`
   - etc. for all non-I/O cases
   
   **Transformation pattern:**
   - Remove world parameters from signature
   - Replace `terminatesToW` with `terminatesTo`
   - Remove world sync proofs
   - Keep all core type reasoning intact

**What to keep unchanged:**
- The `StepFR` definition (line 85) - this is our target
- The `terminatesTo` definition - world-free
- General infrastructure: `InputSpec`, `ObservableSpec`, `agreeValueUnder`, etc.
- World-free helper lemmas (type structure lemmas, agreement transport, etc.)

**Implementation strategy:**

1. Create a backup branch first

2. **Phase 1: Delete I/O-specific code**
   - Delete `IO_Axioms` section (lines 20-52)
   - Delete 4 I/O structure lemmas (lines ~3815-4057)
   - Delete I/O cases from main proof (rand, frand, printInt, printString, externs)

3. **Phase 2: Refactor non-I/O cases**
   - For each `stepFRW_*` lemma, create corresponding `stepFR_*`
   - Apply semi-mechanical transformation (remove worlds, keep core logic)
   - Expect ~10-15 lemmas to refactor

4. **Phase 3: Update top-level**
   - Create `TypeSystemEnforcesFaultRobustness_impl_IOFree`
   - Create `TypeSystemEnforcesFaultRobustness_step_IOFree` 
   - Create `TypeSystemEnforcesFaultRobustness_IOFree`

5. **Phase 4: Delete obsolete infrastructure** ⚠️ **CRITICAL STEP**
   
   **Primary compilation risk:** Must eliminate ALL references to old world-threaded components, not just in "main proof" region. Stray dependencies will cause compilation failures.
   
   Delete these definitions and all references to them:
   - `TypeSystemEnforcesFaultRobustness_stepW` (the old main proof)
   - `StepFR_of_StepFRW` (conversion lemma)
   - `TypeSystemEnforcesFaultRobustness_step_specW` (old spec)
   - `StepFRW` (definition, if exists separately from uses)
   - Old `TypeSystemEnforcesFaultRobustness_impl` (line 510)
   - Old `TypeSystemEnforcesFaultRobustness_step` (lines 4933-4940)
   - Old `TypeSystemEnforcesFaultRobustness` (line 4944)
   - Any helper lemmas that only existed to support the world-threaded  path, such as `terminatesToW_of_terminatesTo`
   
   **Verification strategy:**
   ```bash
   # After deletion, search for any remaining references:
   rg "TypeSystemEnforcesFaultRobustness_stepW" LeanProofs/
   rg "StepFR_of_StepFRW" LeanProofs/
   rg "step_specW" LeanProofs/
   rg "StepFRW" LeanProofs/
   rg "terminatesToW" LeanProofs/
   # All should return zero matches
   ```

6. **Phase 5: Final verification**
   - Run `lake build` - file must compile
   - Run `#print axioms TypeSystemEnforcesFaultRobustness_IOFree` - verify no I/O axioms
   - Ensure no references to deleted infrastructure remain

**Rationale:**

The world-threaded development is tightly coupled to I/O axioms. Once axioms are removed, 29+ references to `StepFRW` and 41+ to `terminatesToW` will fail to compile or become dead code. Rather than maintaining broken/unused code, we remove the world-threading machinery and refactor the core logic to be world-free.

## Effort estimation and Acceptance Criteria

### Expected effort

- **Low (0.5–1 days)** to define `IOFree` and state the new theorems
- **Low-Medium (1–2 days)** to remove I/O-specific code:
  - Delete I/O axioms (lines 20-52)
  - Delete 4 I/O structure lemmas (lines ~3815-4057)
  - Delete I/O cases from main proof
- **Medium (3–5 days)** to refactor non-I/O cases from world-threaded to world-free:
  - **Key insight:** For non-I/O expressions (op, ite, newRef, assign, seq, vlet, fn, pfn, app, etc.), the existing `stepFRW_*` proofs contain world-free core logic wrapped in world-threading plumbing
  - **Refactoring approach:** Semi-mechanical transformation for each case:
    1. Remove world parameters (`w`, `w₀'`, `w₁'`, `w₀mid`, `w₁mid`) from signatures
    2. Replace `terminatesToW w w' e ...` with `terminatesTo e ...`
    3. Remove world synchronization proofs (`hw_mid`, `hw_out`)
    4. Remove world equality rewrites (e.g., `subst hw_mid`)
    5. Keep all core type reasoning, memory extension, regime consistency logic unchanged
  - **Why this is faster:** The core proof logic (70-80% of each lemma) remains unchanged. We're only removing world-threading scaffolding, not re-discovering the proof structure.
  - Estimate: ~10-15 lemmas × 2-4 hours each = 3-5 days
- **Low (0.5–1 days)** for debugging and final integration
- **Total: Medium (5–9 days)** with refactoring optimization

**Key optimization:** We refactor the non-I/O cases by removing world-threading "plumbing" while preserving the core proof logic (~2000 lines of refactoring vs ~2500 lines of reproving). This saves 3-5 days of effort.

## Acceptance criteria (definition of "done")

The I/O-free proof plan is complete when:

1. ✅ There is a clearly defined predicate `IOFree : Expr → Prop` in `LeanProofs/IOFree.lean`
2. ✅ The main theorem `TypeSystemEnforcesFaultRobustness_IOFree` is stated with `IOFree e` as a premise
3. ✅ The modified `TypeSystemEnforcesFaultRobustness_impl_IOFree` is proved
4. ✅ The theorem `TypeSystemEnforcesFaultRobustness_step_IOFree` is proved (no `sorry`)
5. ✅ The main theorem proof is complete
6. ✅ Running `#print axioms TypeSystemEnforcesFaultRobustness_IOFree` shows no I/O axioms
7. ✅ All world-threaded infrastructure removed (verified by search):
   - All `stepFRW_*` lemmas refactored to `stepFR_*` (or deleted if I/O-related)
   - Zero references to `terminatesToW` (run: `rg "terminatesToW" LeanProofs/`)
   - Zero references to `StepFRW` (run: `rg "StepFRW" LeanProofs/`)
   - Zero references to `TypeSystemEnforcesFaultRobustness_stepW` (run: `rg "_stepW" LeanProofs/`)
   - Zero references to `StepFR_of_StepFRW` (run: `rg "StepFR_of_StepFRW" LeanProofs/`)
   - Zero references to `step_specW` (run: `rg "step_specW" LeanProofs/`)
   - Zero references to I/O axioms
8. ✅ The code compiles cleanly with `lake build` (no errors, no warnings about missing definitions)

## What remains unproven

Under this plan, the following are explicitly outside the proven fragment:

- Fault robustness for programs using `rand`/`frand`
- Fault robustness for programs performing printing (`printInt`/`printString`)
- Fault robustness for programs using extern declarations
- Any relational properties about the Lean `IO` world token (synchronisation, determinism)

This is an acceptable and defensible narrowing because it isolates trusted-runtime concerns from the type-system contribution.
