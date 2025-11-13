-- Formal properties of the poison language: MemoryMonotonicity

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanPoison.Poison
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std


-- set_option diagnostics true

set_option maxHeartbeats 2000000

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

-- Helper lemma for op case: binary operations chain memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_op (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1_eq =>
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2_eq =>
          split at h_eval
          · next config'' v2 =>
            -- e2 evaluated successfully
            -- Case analysis on evalOp result
            cases h_evalOp : LeanPoison.evalOp op v1 v2 with
            | some v_result =>
              -- evalOp succeeded
              simp [h_evalOp] at h_eval
              simp [pure] at h_eval
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result with h_eq_config h_eq_val
              -- config₁ = config''
              subst h_eq_config
              -- Convert to pure form for IH
              have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                               pure (.success config' v1) := by
                funext _; simp [pure]; exact h_beval1_eq
              have h_beval2' : LeanPoison.beval fuel' config' e2 verbose =
                               pure (.success config'' v2) := by
                funext _; simp [pure]; exact h_beval2_eq
              -- Chain through IH
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
              exact IH fuel' h_fuel e2 config' config'' v2 h_beval2' l IH1
            | none =>
              -- evalOp returned none (contradiction with success)
              simp [h_evalOp] at h_eval
              simp [pure] at h_eval
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for seq case: sequences chain memory monotonicity through e1 then e2
private lemma beval_memory_monotonic_seq (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1_eq =>
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2_eq =>
          split at h_eval
          · next config'' v2 =>
            -- e2 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config''
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' v1) := by
              funext _; simp [pure]; exact h_beval1_eq
            have h_beval2' : LeanPoison.beval fuel' config' e2 verbose =
                             pure (.success config'' v2) := by
              funext _; simp [pure]; exact h_beval2_eq
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
            exact IH fuel' h_fuel e2 config' config'' v2 h_beval2' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma for unaryop case: unary operations chain memory monotonicity through e1
private lemma beval_memory_monotonic_unaryop (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Unfold beval (use unfold, not simp, due to mutual recursion)
  unfold LeanPoison.beval at h_eval
  -- Apply unit argument to convert to applied form
  apply congrFun (a := ()) at h_eval
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    simp at h_eval
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully to config', v1
        -- Case analysis on evalUnaryOp result
        cases h_evalOp : LeanPoison.evalUnaryOp op v1 with
        | some v_result =>
          -- evalUnaryOp succeeded
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Convert h_beval1 to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' v1) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH for e1
          exact IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
        | none =>
          -- evalUnaryOp returned none (contradiction with success)
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result
      · next h_result1_error =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma for ite case: conditionals chain memory monotonicity through e1, then either e2 or e3
private lemma beval_memory_monotonic_ite (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' =>
        -- e1 evaluated successfully to config₁', now branch on boolean value (true case)
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- Branch matched Value.bool true, now evaluate e2
          split at h_eval
          · next config₂ v₂ =>
            -- e2 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' (Value.bool true)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose =
                             pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool true) h_beval1' l h_contains
            exact IH fuel' h_fuel e2 config₁' config₂ v₂ h_beval2' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next config₁' =>
        -- e1 evaluated successfully to config₁', now branch on boolean value (false case)
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result3 h_state3 h_beval3 =>
          -- Branch matched Value.bool false, now evaluate e3
          split at h_eval
          · next config₂ v₃ =>
            -- e3 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' (Value.bool false)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval3' : LeanPoison.beval fuel' config₁' e3 verbose =
                             pure (.success config₂ v₃) := by
              funext _
              simp [pure]
              exact h_beval3
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool false) h_beval1' l h_contains
            exact IH fuel' h_fuel e3 config₁' config₂ v₃ h_beval3' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error3 h_state3 => injection h_eval
      · next v =>
        -- e1 evaluated to non-boolean value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for deref case: dereference chains memory monotonicity through e1
private lemma beval_memory_monotonic_deref (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.deref e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Unfold beval (use unfold, not simp, due to mutual recursion)
  unfold LeanPoison.beval at h_eval
  -- Apply unit argument to convert to applied form
  apply congrFun (a := ()) at h_eval
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    simp at h_eval
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' loc_val =>
        -- e1 evaluated to location loc_val
        -- Extract memory lookup result first
        cases h_mem_lookup : config'.memory.get? loc_val with
        | some n =>
          -- Location found in memory
          -- Rewrite the match expression using the lookup result
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = some n := h_mem_lookup
          rw [h_mem_eq] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ, and beval uses fuel'
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Convert h_beval1 to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.loc loc_val)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH for e1 (note: IH has order: e, config₀, config₁, v, h_eval, l, h_contains)
          exact IH fuel' h_fuel e1 config₀ config' (Value.loc loc_val) h_beval1' l h_contains
        | none =>
          -- Location not found: deref returns runtimeError (contradiction)
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = none := h_mem_lookup
          rw [h_mem_eq] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_contr
          cases h_contr
      · next h_result1_error =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next h_val =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma: HashMap.insert preserves contains for all keys
-- HashMap.insert either adds a new key or updates an existing one, but never removes other keys
-- This is used by both assign and newRef proofs
private lemma HashMap_insert_preserves_contains {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : Type}
    (m : Std.HashMap α β) (k k' : α) (v : β) :
  m.contains k' → (m.insert k v).contains k' := by
  intro h_contains
  -- HashMap.insert preserves all existing keys - it only adds or updates, never removes
  -- Case analysis: if k' = k, use Std.HashMap.contains_insert
  -- If k' ≠ k, insert doesn't affect other keys (get? is preserved for distinct keys)
  by_cases h_eq : k = k'
  · -- k = k': insert definitely makes this key present
    subst h_eq
    -- Use the mathlib lemma: (m.insert k v).contains k = true
    simp [Std.HashMap.contains_insert]
  · -- k ≠ k': insert preserves other keys
    -- Use the fact that for distinct keys, getElem? is preserved
    -- Convert both sides to mem/getElem? form
    rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?]
    rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?] at h_contains
    -- Now use getElem?_insert: (m.insert k v)[k']? = if (k == k') then some v else m[k']?
    rw [Std.HashMap.getElem?_insert]
    -- Case analysis on (k == k')
    by_cases h_beq : (k == k')
    · -- If (k == k') = true, then we get some v, and isSome (some v) = true
      simp [h_beq]
    · -- If (k == k') = false, then we get m[k']?, and isSome m[k']? = true by h_contains
      simp [h_beq, h_contains]

-- Helper lemma for newRef case: newRef allocates memory (adds one location, but preserves existing)
private lemma beval_memory_monotonic_newRef (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to number n
        -- Final config₁ is {config'' with memory := config''.memory.update l' n}
        -- where (l', config'') = freshLoc config'
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Extract that config₁ = {config'' with memory := config''.memory.update l' n}
        -- where freshLoc config' = (l', config'')
        -- freshLoc is defined in Runtime.lean, accessible directly
        -- config'' = {config' with nextLoc := config'.nextLoc + 1}, so config''.memory = config'.memory
        have h_config''_mem : ({ config' with nextLoc := config'.nextLoc + 1 } : Config).memory = config'.memory := rfl
        -- Extract memory equality from config₁
        have h_mem_eq : config₁.memory = config'.memory.update config'.nextLoc n := by
          -- From h_eq_config: config₁ = {memory := config''.memory.update l' n, ...}
          -- where l' = config'.nextLoc and config''.memory = config'.memory
          have h_lhs_mem : ({ memory := config'.memory.update config'.nextLoc n, varEnv := config'.varEnv, nextLoc := config'.nextLoc + 1, pureMode := config'.pureMode } : Config).memory = config'.memory.update config'.nextLoc n := rfl
          have h_congr : ({ memory := config'.memory.update config'.nextLoc n, varEnv := config'.varEnv, nextLoc := config'.nextLoc + 1, pureMode := config'.pureMode } : Config).memory = config₁.memory :=
            congrArg Config.memory h_eq_config
          rw [← h_congr, h_lhs_mem]
        -- Convert to pure form for IH
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                         pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        -- Chain through IH: config₀ → config' (via e1)
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have IH1 := IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
        -- Now we need: config'.memory.contains l → config'.memory.update config'.nextLoc n contains l
        -- HashMap.update (which is insert) preserves contains for all keys
        rw [h_mem_eq]
        -- Use the helper lemma: HashMap.insert preserves contains
        exact HashMap_insert_preserves_contains config'.memory config'.nextLoc l n IH1
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for assign case: assignment chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_assign (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' loc_val =>
        -- e1 evaluated to location loc_val
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ n =>
            -- e2 evaluated to number n
            -- Final config₁ is {config₂ with memory := config₂.memory.update loc_val n}
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with memory := config₂.memory.update loc_val n}
            -- Memory.update is just insert, which preserves contains
            have h_mem_eq : config₁.memory = config₂.memory.update loc_val n := by
              -- From h_eq_config: {memory := config₂.memory.update loc_val n, ...} = config₁
              have h_lhs_mem : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₂.memory.update loc_val n := rfl
              have h_congr : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              rw [← h_congr, h_lhs_mem]
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                                 pure (.success config₁' (Value.loc loc_val)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose =
                             pure (.success config₂ (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH: config₀ → config₁' (via e1), then config₁' → config₂ (via e2)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.loc loc_val) h_beval1' l h_contains
            have IH2 := IH fuel' h_fuel e2 config₁' config₂ (Value.num n) h_beval2' l IH1
            -- Now we need: config₂.memory.contains l → config₂.memory.update loc_val n contains l
            -- HashMap.update is just insert, and insert preserves contains for all keys
            rw [h_mem_eq]
            -- Memory.update = HashMap.insert, which preserves contains
            -- If l = loc_val, insert adds/updates it (definitely contains)
            -- If l ≠ loc_val, insert doesn't remove it (preserves contains)
            exact HashMap_insert_preserves_contains config₂.memory loc_val l n IH2
          · next v =>
            -- e2 evaluated to non-number value (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next =>
            -- e2 evaluation returned outOfFuel (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next msg =>
            -- e2 evaluation returned runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next v =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for vlet case: let binding chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_vlet (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' v₁ =>
        -- e1 evaluated successfully to config₁', v₁
        -- Now create config'' with updated varEnv and evaluate e2
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ v₂ =>
            -- e2 evaluated successfully to config₂, v₂
            -- Final config₁ is {config₂ with varEnv := config₁'.varEnv}
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with varEnv := config₁'.varEnv}
            -- This means config₁.memory = config₂.memory (since only varEnv differs)
            -- From h_eq_config: {memory := config₂.memory, varEnv := config₁'.varEnv, ...} = config₁
            -- Taking memory of both sides using congrArg: lhs.memory = config₁.memory
            -- But lhs.memory = config₂.memory, so config₁.memory = config₂.memory
            have h_lhs_mem : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₂.memory := rfl
            have h_mem_eq : config₁.memory = config₂.memory := by
              -- Apply congrArg to h_eq_config to get: lhs.memory = config₁.memory
              have h_congr : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              -- Now combine with h_lhs_mem: config₂.memory = lhs.memory = config₁.memory
              rw [← h_congr, h_lhs_mem]
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            -- For e2, we evaluate with config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            have h_beval2' : LeanPoison.beval fuel' ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) e2 verbose =
                             pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH: config₀ → config₁' (via e1), then config₁' → config₂ (via e2)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' v₁ h_beval1' l h_contains
            -- config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            -- config'' has same memory as config₁', so if l is in config₁'.memory, it's in config''.memory
            have h_config''_mem_eq : ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }).memory.contains l =
                                     config₁'.memory.contains l := by
              simp
            rw [← h_config''_mem_eq] at IH1
            -- Now apply IH on e2: config'' → config₂
            have IH2 := IH fuel' h_fuel e2 ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) config₂ v₂ h_beval2' l IH1
            -- config₁.memory = config₂.memory from h_mem_eq
            rw [h_mem_eq]
            exact IH2
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma: bevalFunctionBody preserves memory monotonicity
-- This is needed for the app case
private lemma bevalFunctionBody_memory_monotonic
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
    pure (.success finalConfig v) →
  ∀ l, currentConfig.memory.contains l → finalConfig.memory.contains l := by
  intro h_eval l h_contains
  cases fuel with
  | zero =>
    -- When fuel = 0, bevalFunctionBody returns outOfFuel (contradiction)
    unfold LeanPoison.bevalFunctionBody at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Split on body evaluation
    split at h_eval
    · next h_body_result h_body_state h_beval_body =>
      split at h_eval
      · next evalConfig v_body =>
        -- Body evaluation succeeded
        -- Now handle the if-then-else on isPure using split
        split at h_eval
        · -- isPure = true branch: finalConfig = {currentConfig with pureMode := false}
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          -- Extract memory equality: finalConfig.memory = currentConfig.memory
          have h_mem_eq : finalConfig.memory = currentConfig.memory := by
            have h_lhs_mem : ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv, nextLoc := currentConfig.nextLoc, pureMode := false } : Config).memory = currentConfig.memory := rfl
            have h_congr : ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv, nextLoc := currentConfig.nextLoc, pureMode := false } : Config).memory = finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          rw [h_mem_eq]
          exact h_contains
        · -- isPure = false branch: finalConfig = {currentConfig with memory := evalConfig.memory, ...}
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          -- Extract memory: finalConfig.memory = evalConfig.memory
          have h_mem_eq : finalConfig.memory = evalConfig.memory := by
            have h_lhs_mem : ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextLoc := evalConfig.nextLoc, pureMode := false } : Config).memory = evalConfig.memory := rfl
            have h_congr : ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextLoc := evalConfig.nextLoc, pureMode := false } : Config).memory = finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          -- bodyConfig = {currentConfig with varEnv := env.update x v₂, pureMode := isPure}
          -- In this branch, isPure = false, so bodyConfig with isPure = bodyConfig with false
          -- But we need to extract that isPure = false from being in the false branch
          -- Use the fact that bodyConfig was created with pureMode := isPure, but we can rewrite it
          -- Actually, we don't need to rewrite - we can just use h_beval_body as-is since it has the right config
          have h_bodyConfig_mem : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).memory = currentConfig.memory := rfl
          -- Convert to pure form for IH
          have h_beval_body' : LeanPoison.beval fuel' ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) body verbose =
                               pure (.success evalConfig v_body) := by
            funext _
            simp [pure]
            exact h_beval_body
          -- Apply IH to body evaluation
          -- Use the original IH with fuel' < fuel'.succ
          have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body' l
          rw [h_bodyConfig_mem] at IH_body
          -- Now we have: currentConfig.memory.contains l → evalConfig.memory.contains l
          have h_mem_contains := IH_body h_contains
          rw [h_mem_eq]
          exact h_mem_contains
      · next => injection h_eval with h_contr _; injection h_contr
      · next msg => injection h_eval with h_contr _; injection h_contr
    · next h_body_error h_body_state => injection h_eval

-- Helper lemma for app case: function application chains memory monotonicity through e1, e2, and body
private lemma beval_memory_monotonic_app (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e2 evaluation (app evaluates e2 first)
    split at h_eval
    · next h_result2 h_state2 h_beval2 =>
      -- e2 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' v₂ =>
        -- e2 evaluated to config₁', v₂
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result1 h_state1 h_beval1 =>
          -- e1 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ x body env =>
            -- e1 evaluated to closure
            -- Check if config₂.pureMode
            split at h_eval
            · next h_pureMode =>
              -- Pure mode case: runtime error (contradiction)
              injection h_eval with h_contr
              cases h_contr
            · next h_notPureMode =>
              -- Not pure mode: call bevalFunctionBody
              -- h_eval: bevalFunctionBody fuel' verbose config₂ env x v₂ body false = pure (.success config₁ v)
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              -- Convert to pure form for IH
              have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose =
                               pure (.success config₁' v₂) := by
                funext _
                simp [pure]
                exact h_beval2
              have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose =
                               pure (.success config₂ (Value.closure x body env)) := by
                funext _
                simp [pure]
                exact h_beval1
              -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
              have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2' l h_contains
              have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.closure x body env) h_beval1' l IH2
              -- Apply bevalFunctionBody memory monotonicity helper
              have h_bevalFunctionBody' : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                                         pure (.success config₁ v) := by
                funext _
                simp [pure]
                exact h_eval
              -- Construct IH with fuel' bound from fuel'.succ bound
              have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
                ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
                intro m h_m_lt_fuel' e config₀ config₁ v h_beval_eq l h_contains_loc
                have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
                exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_eq l h_contains_loc
              exact bevalFunctionBody_memory_monotonic fuel' verbose config₂ config₁ env x v₂ body false v IH_fuel' h_bevalFunctionBody' l IH1
          · next config₂ x body env =>
            -- e1 evaluated to peClosure (pure function)
            -- bevalFunctionBody with isPure=true
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            -- Convert to pure form for IH
            have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose =
                             pure (.success config₁' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose =
                             pure (.success config₂ (Value.peClosure x body env)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
            have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2' l h_contains
            have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.peClosure x body env) h_beval1' l IH2
            -- Apply bevalFunctionBody memory monotonicity helper
            have h_bevalFunctionBody' : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
                                       pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval
            -- Construct IH with fuel' bound from fuel'.succ bound
            have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
              LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
              ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
              intro m h_m_lt_fuel' e config₀ config₁ v h_beval_eq l h_contains_loc
              have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
              exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_eq l h_contains_loc
            exact bevalFunctionBody_memory_monotonic fuel' verbose config₂ config₁ env x v₂ body true v IH_fuel' h_bevalFunctionBody' l IH1
          · next v =>
            -- e1 evaluated to non-closure value (contradiction)
            injection h_eval with h_contr
            cases h_contr
          · next =>
            -- e1 evaluation returned outOfFuel (contradiction)
            injection h_eval with h_contr
            cases h_contr
          · next msg =>
            -- e1 evaluation returned runtimeError (contradiction)
            injection h_eval with h_contr
            cases h_contr
        · next h_error1 h_state1 => injection h_eval
      · next =>
        -- e2 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e2 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error2 h_state2 => injection h_eval

-- Helper lemma for rand case: random chains memory monotonicity through e1
private lemma beval_memory_monotonic_rand (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.rand e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- Now split on if n >= 0 (branch for generating random number)
        split at h_eval
        · -- n >= 0: generate random number
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next r_result r_state =>
            -- IO.rand succeeded
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Apply IH on e1: rand doesn't modify memory, only e1 evaluation does
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
          · next r_error r_state => injection h_eval
        · -- n < 0: error case (contradiction with success)
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next p_result p_state =>
            -- IO.println succeeded, but we get runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for frand case: faulty random chains memory monotonicity through e1
private lemma beval_memory_monotonic_frand (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.frand e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- Now split on if n >= 0 (branch for generating faulty random number)
        split at h_eval
        · -- n >= 0: generate faulty random number
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next r_result r_state =>
            -- IO.rand succeeded
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Apply IH on e1: frand doesn't modify memory, only e1 evaluation does
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
          · next r_error r_state => injection h_eval
        · -- n < 0: error case (contradiction with success)
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next p_result p_state =>
            -- IO.println succeeded, but we get runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for printInt case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printInt (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.printInt e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- IO.println is wrapped in Functor.map/EStateM.map
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          -- IO.println succeeded
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Convert to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH on e1: printInt doesn't modify memory, only e1 evaluation does
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
        · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for printString case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printString (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.printString e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' s =>
        -- e1 evaluated to Value.str s
        -- IO.println is wrapped in Functor.map/EStateM.map
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          -- IO.println succeeded
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Convert to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.str s)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH on e1: printString doesn't modify memory, only e1 evaluation does
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          exact IH fuel' h_fuel e1 config₀ config' (Value.str s) h_beval1' l h_contains
        · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-string value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for kwhile case: while loops chain memory monotonicity through iterations
private lemma beval_memory_monotonic_kwhile (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  unfold LeanPoison.beval at h_eval
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel - 1) config₀ unfolded verbose
  simp at h_eval
  -- After simp: the let binding is inlined and fuel - 1 simplifies
  -- Handle fuel = 0 case separately
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    simp [pure] at h_eval
    apply congrFun (a := ()) at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- fuel = fuel' + 1, so fuel - 1 = fuel'
    -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose = pure (.success config₁ v)
    -- Convert to applied form to work with the monadic structure
    apply congrFun (a := ()) at h_eval
    -- h_eval now contains: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose () = pure (.success config₁ v) ()
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    -- Define the unfolded expression that kwhile expands to
    let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
    -- h_eval already contains the evaluation of this unfolded expression
    -- Convert from applied form to pure form for IH
    have h_beval_unfolded : LeanPoison.beval fuel' config₀ unfolded verbose = pure (.success config₁ v) := by
      funext _
      simp [pure]
      exact h_eval
    -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
    -- The unfolded expression (ite) preserves memory monotonicity by IH (which internally uses the ite proof)
    exact IH fuel' h_fuel unfolded config₀ config₁ v h_beval_unfolded l h_contains

-- Memory Monotonicity Lemma: evaluation can only add memory locations, never remove them
-- This is a key property that follows from the fact that memory locations are never deallocated
lemma beval_memory_monotonic : ∀ (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  LeanPoison.beval fuel config₀ e verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro e fuel verbose config₀ config₁ v h_eval
  -- Proof by strong induction on fuel, then case analysis on expression
  induction fuel using Nat.strong_induction_on generalizing e config₀ config₁ v with
  | _ fuel IH =>
    intro l h_contains
    cases e with
    | num n | bool b | str s | unit =>
      -- Literals don't modify memory: config₁ = config₀
      -- All literals (numbers, booleans, strings, unit) follow the same pattern
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | var x =>
      -- Variables don't modify memory: config₁ = config₀
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval does variable lookup
        -- After unfold and apply congrFun, we need to handle the match on lookup
        -- Case analysis on variable lookup result using cases instead of split
        cases h_lookup : config₀.varEnv.lookup x with
        | some v_found =>
          -- Variable found: beval returns success with same config
          simp [h_lookup] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- Now we have config₁ = config₀ from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
          exact h_contains
        | none =>
          -- Variable not found: beval returns runtimeError (contradiction with success)
          simp [h_lookup] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_contr
          -- h_contr : runtimeError ... = success ... is impossible
          cases h_contr
    | op e1 op e2 =>
      -- Binary operations: memory changes come from e1 and e2, evalOp doesn't allocate
      -- Use helper lemma for binary operations
      exact beval_memory_monotonic_op e1 e2 op fuel verbose config₀ config₁ v IH h_eval l h_contains
    | unaryop op e1 =>
      -- Unary operations: memory changes come from e1, evalUnaryOp doesn't modify memory
      -- Use helper lemma for unary operations
      exact beval_memory_monotonic_unaryop op e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | ite e1 e2 e3 =>
      -- Conditionals: memory changes from e1, then either e2 or e3
      -- Use helper lemma for conditionals
      exact beval_memory_monotonic_ite e1 e2 e3 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | newRef e1 =>
      -- newRef allocates memory: adds one location
      -- Use helper lemma for newRef
      exact beval_memory_monotonic_newRef e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | assign e1 e2 =>
      -- Assignment: memory changes from e1 and e2, but no new allocations
      -- Use helper lemma for assign
      exact beval_memory_monotonic_assign e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | deref e1 =>
      -- Dereference: memory changes only from e1, deref itself doesn't modify memory
      -- Use helper lemma for deref
      exact beval_memory_monotonic_deref e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | seq e1 e2 =>
      -- Sequence: memory changes from e1, then e2
      -- Use helper lemma for sequences
      exact beval_memory_monotonic_seq e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | kwhile e1 e2 =>
      -- While loops: needs careful handling of iteration
      -- Use helper lemma for kwhile
      exact beval_memory_monotonic_kwhile e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | vlet x e1 e2 =>
      -- Let binding: memory changes from e1, then e2
      -- Use helper lemma for vlet
      exact beval_memory_monotonic_vlet x e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | fn x paramType body returnType | pfn x paramType body returnType =>
      -- Function abstractions don't modify memory: config₁ = config₀
      -- Both fn and pfn just create closures without modifying config
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | app e1 e2 =>
      -- Function application: memory changes from e1, e2, and function body
      -- Use helper lemma for app
      exact beval_memory_monotonic_app e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | rand e1 =>
      -- Random: memory changes only from e1
      -- Use helper lemma for rand
      exact beval_memory_monotonic_rand e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | frand e1 =>
      -- Faulty random: memory changes only from e1
      -- Use helper lemma for frand
      exact beval_memory_monotonic_frand e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | printInt e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printInt
      exact beval_memory_monotonic_printInt e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | printString e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printString
      exact beval_memory_monotonic_printString e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
