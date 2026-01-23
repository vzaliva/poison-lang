-- Formal properties of the poison language: MemoryMonotonicity

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import LeanProofs.SemanticsProperties
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
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
private lemma beval_memory_monotonic_op (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.op e1 op e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation
    split at h_eq
    · next h_result1 h_state1 h_beval1_eq =>
      -- Case analysis on e1 evaluation result
      cases h_result1 with
      | success config' v1 =>
        -- e1 evaluated successfully
        simp [EST.bind] at h_eq
        split at h_eq
        · next h_result2 h_state2 h_beval2_eq =>
          -- Case analysis on e2 evaluation result
          cases h_result2 with
          | success config'' v2 =>
            -- e2 evaluated successfully
            -- Case analysis on evalOp result
            cases h_evalOp : LeanPoison.evalOp op v1 v2 with
            | some v_result =>
              -- evalOp succeeded
              simp [h_evalOp] at h_eq
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              -- config₁ = config''
              subst h_eq_config
              -- Construct existentials for IH
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁' :=
                ⟨w₀, h_state1, h_beval1_eq⟩
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config' e2 verbose w₀' = EST.Out.ok (.success config'' v2) w₁' :=
                ⟨h_state1, h_state2, h_beval2_eq⟩
              -- Chain through IH
              have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1_ex l h_contains
              exact IH fuel' h_fuel e2 config' config'' v2 h_beval2_ex l IH1
            | none =>
              -- evalOp returned none (contradiction with success)
              simp [h_evalOp] at h_eq
              injection h_eq with h_result h_world
              injection h_result
          | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next h_error2 h_state2 => injection h_eq
      | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next h_error1 h_state1 => injection h_eq

-- Helper lemma for seq case: sequences chain memory monotonicity through e1 then e2
private lemma beval_memory_monotonic_seq (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.seq e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation
    split at h_eq
    · next h_result1 h_state1 h_beval1_eq =>
      -- Case analysis on e1 evaluation result
      cases h_result1 with
      | success config' v1 =>
        -- e1 evaluated successfully
        simp [EST.bind] at h_eq
        split at h_eq
        · next h_result2 h_state2 h_beval2_eq =>
          -- Case analysis on e2 evaluation result
          cases h_result2 with
          | success config'' v2 =>
            -- e2 evaluated successfully
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            -- config₁ = config''
            subst h_eq_config
            -- Construct existentials for IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁' :=
              ⟨w₀, h_state1, h_beval1_eq⟩
            have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config' e2 verbose w₀' = EST.Out.ok (.success config'' v2) w₁' :=
              ⟨h_state1, h_state2, h_beval2_eq⟩
            -- Chain through IH
            have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1_ex l h_contains
            exact IH fuel' h_fuel e2 config' config'' v2 h_beval2_ex l IH1
          | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next h_error2 h_state2 => injection h_eq
      | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eq

-- Helper lemma for unaryop case: unary operations chain memory monotonicity through e1
private lemma beval_memory_monotonic_unaryop (mode : LeanPoison.EvalMode) (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.unaryop op e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      cases h_result1 with
      | success config' v1 =>
        -- e1 evaluated successfully to config', v1
        -- Case analysis on evalUnaryOp result
        cases h_evalOp : LeanPoison.evalUnaryOp op v1 with
        | some v_result =>
          -- evalUnaryOp succeeded
          simp [h_evalOp] at h_eq
          injection h_eq with h_result h_world
          injection h_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Construct existential for IH
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          -- Apply IH for e1
          exact IH fuel' h_fuel e1 config₀ config' v1 h_beval1_ex l h_contains
        | none =>
          -- evalUnaryOp returned none (contradiction with success)
          simp [h_evalOp] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      | outOfFuel =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | runtimeError msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | ioForbidden =>
        -- e1 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eq

-- Helper lemma for ite case: conditionals chain memory monotonicity through e1, then either e2 or e3
private lemma beval_memory_monotonic_ite (mode : LeanPoison.EvalMode) (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.ite e1 e2 e3) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      cases h_result1 with
      | success config₁' v1 =>
        -- e1 evaluated successfully to config₁', now branch on boolean value
        cases v1 with
        | bool b =>
          cases b with
          | true =>
            -- true case: evaluate e2
            simp [EST.bind] at h_eq
            split at h_eq
            · next h_result2 h_state2 h_beval2 =>
              -- Case analysis on e2 evaluation result
              cases h_result2 with
              | success config₂ v₂ =>
                -- e2 evaluated successfully
                injection h_eq with h_result h_world
                injection h_result with h_eq_config h_eq_val
                subst h_eq_config
                -- Construct existentials for IH
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool true)) w₁' :=
                  ⟨w₀, h_state1, h_beval1⟩
                have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
                  ⟨h_state1, h_state2, h_beval2⟩
                -- Chain through IH
                have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool true) h_beval1_ex l h_contains
                exact IH fuel' h_fuel e2 config₁' config₂ v₂ h_beval2_ex l IH1
              | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
              | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
              | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
            · next h_error2 h_state2 => injection h_eq
          | false =>
            -- false case: evaluate e3
            simp [EST.bind] at h_eq
            split at h_eq
            · next h_result3 h_state3 h_beval3 =>
              -- Case analysis on e3 evaluation result
              cases h_result3 with
              | success config₂ v₃ =>
                -- e3 evaluated successfully
                injection h_eq with h_result h_world
                injection h_result with h_eq_config h_eq_val
                subst h_eq_config
                -- Construct existentials for IH
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool false)) w₁' :=
                  ⟨w₀, h_state1, h_beval1⟩
                have h_beval3_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e3 verbose w₀' = EST.Out.ok (.success config₂ v₃) w₁' :=
                  ⟨h_state1, h_state3, h_beval3⟩
                -- Chain through IH
                have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool false) h_beval1_ex l h_contains
                exact IH fuel' h_fuel e3 config₁' config₂ v₃ h_beval3_ex l IH1
              | outOfFuel => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
              | runtimeError msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
              | ioForbidden => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
            · next h_error3 h_state3 => injection h_eq
        | _ =>
          -- e1 evaluated to non-boolean value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      | outOfFuel =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | runtimeError msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | ioForbidden =>
        -- e1 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error1 h_state1 => injection h_eq

-- Helper lemma for deref case: dereference chains memory monotonicity through e1
private lemma beval_memory_monotonic_deref (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.deref e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eq
      · next config' loc_val =>
        -- e1 evaluated to location loc_val
        -- Extract memory lookup result first
        cases h_mem_lookup : config'.memory.get? loc_val with
        | some n =>
          -- Location found in memory
          -- Rewrite the match expression using the lookup result
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = some n := h_mem_lookup
          rw [h_mem_eq] at h_eq
          injection h_eq with h_result h_world
          injection h_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ, and beval uses fuel'
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Construct existential for IH
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.loc loc_val)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          -- Apply IH for e1
          exact IH fuel' h_fuel e1 config₀ config' (Value.loc loc_val) h_beval1_ex l h_contains
        | none =>
          -- Location not found: deref returns runtimeError (contradiction)
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = none := h_mem_lookup
          rw [h_mem_eq] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_result1_error =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next h_val =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · -- e1 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eq

-- Helper lemma: ExtTreeMap.insert preserves contains for all keys
-- ExtTreeMap.insert either adds a new key or updates an existing one, but never removes other keys
-- This is used by both assign and newRef proofs
private lemma ExtTreeMap_insert_preserves_contains {α : Type} [Ord α] [BEq α] [TransCmp (compare : α → α → Ordering)] {β : Type}
    (m : ExtTreeMap α β) (k k' : α) (v : β) :
  m.contains k' → (m.insert k v).contains k' := by
  intro h_contains
  -- ExtTreeMap.insert preserves all existing keys - it only adds or updates, never removes
  -- If k' = k, then insert adds/updates it (definitely contains)
  -- If k' ≠ k, then insert doesn't affect k' (preserves contains)
  by_cases h_eq : k = k'
  · -- k = k': insert adds/updates k', so it's definitely contained
    subst h_eq
    simp [ExtTreeMap.contains_insert]
  · -- k ≠ k': insert doesn't remove k', so it's still contained
    -- Use contains_insert: (t.insert k v).contains a = (cmp k a == .eq || t.contains a)
    -- Since m.contains k' = true (from h_contains), the right side is true regardless of cmp k k'
    rw [ExtTreeMap.contains_insert]
    simp [h_contains]

-- Helper lemma for newRef case: newRef allocates memory (adds one location, but preserves existing)
private lemma beval_memory_monotonic_newRef (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.newRef e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation
    split at h_eq
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eq
      · next config' n =>
        -- e1 evaluated to number n
        -- Final config₁ is {config'' with memory := config''.memory.update l' n}
        -- where (l', config'') = freshLoc config'
        injection h_eq with h_result h_world
        injection h_result with h_eq_config h_eq_val
        -- Extract that config₁ = {config'' with memory := config''.memory.update l' n}
        -- where freshLoc config' = (l', config'')
        -- freshLoc is defined in Runtime.lean, accessible directly
        -- config'' = {config' with nextLoc := config'.nextAddr + 1}, so config''.memory = config'.memory
        have h_config''_mem : ({ config' with nextAddr := config'.nextAddr + 1 } : Config).memory = config'.memory := rfl
        -- Extract memory equality from config₁
        have h_mem_eq : config₁.memory = config'.memory.update config'.nextAddr n := by
          -- From h_eq_config: config₁ = {memory := config''.memory.update l' n, ...}
          -- where l' = config'.nextAddr and config''.memory = config'.memory
          have h_lhs_mem : ({ memory := config'.memory.update config'.nextAddr n, varEnv := config'.varEnv, nextAddr := config'.nextAddr + 1, pureMode := config'.pureMode } : Config).memory = config'.memory.update config'.nextAddr n := rfl
          have h_congr : ({ memory := config'.memory.update config'.nextAddr n, varEnv := config'.varEnv, nextAddr := config'.nextAddr + 1, pureMode := config'.pureMode } : Config).memory = config₁.memory :=
            congrArg Config.memory h_eq_config
          rw [← h_congr, h_lhs_mem]
        -- Construct existential for IH
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
          ⟨w₀, h_state, h_beval1⟩
        -- Chain through IH: config₀ → config' (via e1)
        have IH1 := IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1_ex l h_contains
        -- Now we need: config'.memory.contains l → config'.memory.update config'.nextAddr n contains l
        -- ExtTreeMap.update (which is insert) preserves contains for all keys
        rw [h_mem_eq]
        -- Use the helper lemma: ExtTreeMap.insert preserves contains
        exact ExtTreeMap_insert_preserves_contains config'.memory config'.nextAddr l n IH1
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · -- e1 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error h_state => injection h_eq

-- Helper lemma for assign case: assignment chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_assign (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.assign e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eq
      · next config₁' loc_val =>
        -- e1 evaluated to location loc_val
        simp [EST.bind] at h_eq
        split at h_eq
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eq
          · next config₂ n =>
            -- e2 evaluated to number n
            -- Final config₁ is {config₂ with memory := config₂.memory.update loc_val n}
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with memory := config₂.memory.update loc_val n}
            -- Memory.update is just insert, which preserves contains
            have h_mem_eq : config₁.memory = config₂.memory.update loc_val n := by
              -- From h_eq_config: {memory := config₂.memory.update loc_val n, ...} = config₁
              have h_lhs_mem : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextAddr := config₂.nextAddr, pureMode := config₂.pureMode } : Config).memory = config₂.memory.update loc_val n := rfl
              have h_congr : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextAddr := config₂.nextAddr, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              rw [← h_congr, h_lhs_mem]
            -- Construct existentials for IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.loc loc_val)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ (Value.num n)) w₁' :=
              ⟨h_state1, h_state2, h_beval2⟩
            -- Chain through IH: config₀ → config₁' (via e1), then config₁' → config₂ (via e2)
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.loc loc_val) h_beval1_ex l h_contains
            have IH2 := IH fuel' h_fuel e2 config₁' config₂ (Value.num n) h_beval2_ex l IH1
            -- Now we need: config₂.memory.contains l → config₂.memory.update loc_val n contains l
            -- ExtTreeMap.update is just insert, and insert preserves contains for all keys
            rw [h_mem_eq]
            -- Memory.update = ExtTreeMap.insert, which preserves contains
            -- If l = loc_val, insert adds/updates it (definitely contains)
            -- If l ≠ loc_val, insert doesn't remove it (preserves contains)
            exact ExtTreeMap_insert_preserves_contains config₂.memory loc_val l n IH2
          · next v =>
            -- e2 evaluated to non-number value (contradiction)
            simp [pure] at h_eq
            injection h_eq with h_result h_world
            injection h_result
          · next =>
            -- e2 evaluation returned outOfFuel (contradiction)
            simp [pure] at h_eq
            injection h_eq with h_result h_world
            injection h_result
          · next msg =>
            -- e2 evaluation returned runtimeError (contradiction)
            simp [pure] at h_eq
            injection h_eq with h_result h_world
            injection h_result
          · -- e2 evaluation returned ioForbidden (contradiction)
            simp [pure] at h_eq
            injection h_eq with h_result h_world
            injection h_result
        · next h_error2 h_state2 => injection h_eq
      · next v =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · -- e1 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error1 h_state1 => injection h_eq

-- Helper lemma for vlet case: let binding chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_vlet (mode : LeanPoison.EvalMode) (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.vlet x e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e1 evaluation
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eq
      · next config₁' v₁ =>
        -- e1 evaluated successfully to config₁', v₁
        -- Now create config'' with updated varEnv and evaluate e2
        simp [EST.bind] at h_eq
        split at h_eq
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eq
          · next config₂ v₂ =>
            -- e2 evaluated successfully to config₂, v₂
            -- Final config₁ is {config₂ with varEnv := config₁'.varEnv}
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with varEnv := config₁'.varEnv}
            -- This means config₁.memory = config₂.memory (since only varEnv differs)
            -- From h_eq_config: {memory := config₂.memory, varEnv := config₁'.varEnv, ...} = config₁
            -- Taking memory of both sides using congrArg: lhs.memory = config₁.memory
            -- But lhs.memory = config₂.memory, so config₁.memory = config₂.memory
            have h_lhs_mem : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextAddr := config₂.nextAddr, pureMode := config₂.pureMode } : Config).memory = config₂.memory := rfl
            have h_mem_eq : config₁.memory = config₂.memory := by
              -- Apply congrArg to h_eq_config to get: lhs.memory = config₁.memory
              have h_congr : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextAddr := config₂.nextAddr, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              -- Now combine with h_lhs_mem: config₂.memory = lhs.memory = config₁.memory
              rw [← h_congr, h_lhs_mem]
            -- Construct existentials for IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' v₁) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            -- Chain through IH: config₀ → config₁' (via e1)
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' v₁ h_beval1_ex l h_contains
            -- config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            -- config'' has same memory as config₁', so if l is in config₁'.memory, it's in config''.memory
            have h_config''_mem_eq : ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }).memory.contains l =
                                     config₁'.memory.contains l := by
              simp
            rw [← h_config''_mem_eq] at IH1
            -- For e2, we evaluate with config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
              ⟨h_state1, h_state2, h_beval2⟩
            -- Now apply IH on e2: config'' → config₂
            have IH2 := IH fuel' h_fuel e2 ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) config₂ v₂ h_beval2_ex l IH1
            -- config₁.memory = config₂.memory from h_mem_eq
            rw [h_mem_eq]
            exact IH2
          · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
          · simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result  -- ioForbidden
        · next h_error2 h_state2 => injection h_eq
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result  -- ioForbidden
    · next h_error1 h_state1 => injection h_eq

-- Helper lemma: bevalFunctionBody preserves memory monotonicity
-- This is needed for the app case
private lemma bevalFunctionBody_memory_monotonic
    (mode : LeanPoison.EvalMode) (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.bevalFunctionBody mode fuel verbose currentConfig closureEnv paramName argValue body isPure w₀ =
      EST.Out.ok (.success finalConfig v) w₁) →
  ∀ l, currentConfig.memory.contains l → finalConfig.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    -- When fuel = 0, bevalFunctionBody returns outOfFuel (contradiction)
    unfold LeanPoison.bevalFunctionBody at h_eq
    -- After unfold, we have: pure .outOfFuel w₀ = Result.ok (.success finalConfig v) w₁
    -- Simplify pure to expose Result.ok
    simp [pure] at h_eq
    -- Now we have: Result.ok .outOfFuel w₀ = Result.ok (.success finalConfig v) w₁
    -- Use injection to extract the equality of the inner EvalResult values
    injection h_eq with h_res
    -- h_res : .outOfFuel = .success finalConfig v
    -- outOfFuel and success are distinct constructors, so this is impossible
    cases h_res
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Split on body evaluation
    split at h_eq
    · next h_body_result h_body_state h_beval_body =>
      split at h_eq
      · next evalConfig v_body =>
        -- Body evaluation succeeded
        -- Now handle the if-then-else on isPure using split
        split at h_eq
        · -- isPure = true branch: finalConfig = {currentConfig with pureMode := currentConfig.pureMode}
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          -- Extract memory equality: finalConfig.memory = currentConfig.memory
          have h_mem_eq : finalConfig.memory = currentConfig.memory := by
            have h_lhs_mem :
                ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv,
                   nextAddr := currentConfig.nextAddr, pureMode := currentConfig.pureMode } : Config).memory =
                  currentConfig.memory := rfl
            have h_congr :
                ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv,
                   nextAddr := currentConfig.nextAddr, pureMode := currentConfig.pureMode } : Config).memory =
                  finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          rw [h_mem_eq]
          exact h_contains
        · -- isPure = false branch: finalConfig = {currentConfig with memory := evalConfig.memory, ...}
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          -- Extract memory: finalConfig.memory = evalConfig.memory
          have h_mem_eq : finalConfig.memory = evalConfig.memory := by
            have h_lhs_mem :
                ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextAddr := evalConfig.nextAddr,
                   pureMode := currentConfig.pureMode } : Config).memory = evalConfig.memory := rfl
            have h_congr :
                ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextAddr := evalConfig.nextAddr,
                   pureMode := currentConfig.pureMode } : Config).memory = finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          -- bodyConfig = {currentConfig with varEnv := env.update x v₂, pureMode := isPure}
          -- In this branch, isPure = false, so bodyConfig with isPure = bodyConfig with false
          -- But we need to extract that isPure = false from being in the false branch
          -- Use the fact that bodyConfig was created with pureMode := isPure, but we can rewrite it
          -- Actually, we don't need to rewrite - we can just use h_beval_body as-is since it has the right config
          have h_bodyConfig_mem : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).memory = currentConfig.memory := rfl
          -- Construct existential for IH
          have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval_body_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) body verbose w₀' =
              EST.Out.ok (.success evalConfig v_body) w₁' :=
            ⟨w₀, h_body_state, h_beval_body⟩
          -- Apply IH to body evaluation
          have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body_ex l
          rw [h_bodyConfig_mem] at IH_body
          -- Now we have: currentConfig.memory.contains l → evalConfig.memory.contains l
          have h_mem_contains := IH_body h_contains
          rw [h_mem_eq]
          exact h_mem_contains
      · next => injection h_eq with h_result h_world; injection h_result
      · next msg => injection h_eq with h_result h_world; injection h_result
      · injection h_eq with h_result h_world; injection h_result  -- ioForbidden
    · next h_body_error h_body_state => injection h_eq

-- Helper lemma for app case: function application chains memory monotonicity through e1, e2, and body
private lemma beval_memory_monotonic_app (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.app e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    -- Case analysis on e2 evaluation (app evaluates e2 first)
    split at h_eq
    · next h_result2 h_state2 h_beval2 =>
      -- e2 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eq
      · next config₁' v₂ =>
        -- e2 evaluated to config₁', v₂
        simp [EST.bind] at h_eq
        split at h_eq
        · next h_result1 h_state1 h_beval1 =>
          -- e1 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eq
          · next config₂ x body env =>
            -- e1 evaluated to closure
            -- Check if config₂.pureMode
            split at h_eq
            · next h_pureMode =>
              -- Pure mode case: runtime error (contradiction)
              injection h_eq with h_result h_world
              injection h_result
            · next h_notPureMode =>
              -- Not pure mode: call bevalFunctionBody
              -- h_eq: bevalFunctionBody fuel' verbose config₂ env x v₂ body false h_state1 = Result.ok (.success config₁ v) w₁
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              -- Construct existentials for IH
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
                ⟨w₀, h_state2, h_beval2⟩
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.closure x body env)) w₁' :=
                ⟨h_state2, h_state1, h_beval1⟩
              -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
              have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2_ex l h_contains
              have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.closure x body env) h_beval1_ex l IH2
              -- Apply bevalFunctionBody memory monotonicity helper
              have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body false w₀' =
                  EST.Out.ok (.success config₁ v) w₁' :=
                ⟨h_state1, w₁, h_eq⟩
              -- Construct IH with fuel' bound from fuel'.succ bound
              have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
                ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
                intro m h_m_lt_fuel' e config₀ config₁ v h_beval_ex l h_contains_loc
                have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
                exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_ex l h_contains_loc
              exact bevalFunctionBody_memory_monotonic mode fuel' verbose config₂ config₁ env x v₂ body false v IH_fuel' h_bevalFunctionBody_ex l IH1
          · next config₂ x body env =>
            cases h_pure : Expr.toPExpr? body with
            | none =>
                simp [h_pure, pure] at h_eq
                injection h_eq with h_result h_world
                injection h_result
            | some _ =>
                simp [h_pure] at h_eq
                -- e1 evaluated to peClosure (pure function)
                -- bevalFunctionBody with isPure=true
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                -- Construct existentials for IH
                have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
                  ⟨w₀, h_state2, h_beval2⟩
                have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.peClosure x body env)) w₁' :=
                  ⟨h_state2, h_state1, h_beval1⟩
                -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
                have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2_ex l h_contains
                have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.peClosure x body env) h_beval1_ex l IH2
                -- Apply bevalFunctionBody memory monotonicity helper
                have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body true w₀' =
                    EST.Out.ok (.success config₁ v) w₁' :=
                  ⟨h_state1, w₁, h_eq⟩
                -- Construct IH with fuel' bound from fuel'.succ bound
                have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                  (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
                  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
                  intro m h_m_lt_fuel' e config₀ config₁ v h_beval_ex l h_contains_loc
                  have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
                  exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_ex l h_contains_loc
                exact bevalFunctionBody_memory_monotonic mode fuel' verbose config₂ config₁ env x v₂ body true v IH_fuel' h_bevalFunctionBody_ex l IH1
          · next v =>
            -- e1 evaluated to non-closure value (contradiction)
            injection h_eq with h_result h_world
            injection h_result
          · next =>
            -- e1 evaluation returned outOfFuel (contradiction)
            injection h_eq with h_result h_world
            injection h_result
          · next msg =>
            -- e1 evaluation returned runtimeError (contradiction)
            injection h_eq with h_result h_world
            injection h_result
          · -- e1 evaluation returned ioForbidden (contradiction)
            injection h_eq with h_result h_world
            injection h_result
        · next h_error1 h_state1 => injection h_eq
      · next =>
        -- e2 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · next msg =>
        -- e2 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      · -- e2 evaluation returned ioForbidden (contradiction)
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error2 h_state2 => injection h_eq

-- Helper lemma for rand case: random chains memory monotonicity through e1
private lemma beval_memory_monotonic_rand (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.rand e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- First split on mode (rand checks mode first)
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: proceed with e1 evaluation
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result h_state h_beval1 =>
        -- e1 evaluation succeeded with ok, now split on inner EvalResult
        split at h_eq
        · next config' n =>
          -- e1 evaluated to Value.num n
          -- Now split on if n >= 0 (branch for generating random number)
          split at h_eq
          · -- n >= 0: generate random number
            simp [Functor.map, EST.bind] at h_eq
            split at h_eq
            · next r_result r_state =>
              -- IO.rand succeeded
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              -- config₁ = config' from h_eq_config
              subst h_eq_config
              -- Construct existential for IH
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval LeanPoison.EvalMode.normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
                ⟨w₀, h_state, h_beval1⟩
              -- Apply IH on e1: rand doesn't modify memory, only e1 evaluation does
              exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1_ex l h_contains
            · next r_error r_state => injection h_eq
          · -- n < 0: error case (contradiction with success)
            simp [Functor.map, EST.bind] at h_eq
            split at h_eq
            · next p_result p_state =>
              -- IO.println succeeded, but we get runtimeError (contradiction)
              injection h_eq with h_result h_world
              injection h_result
            · next p_error p_state => injection h_eq
        · next v =>
          -- e1 evaluated to non-number value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · -- e1 evaluation returned ioForbidden (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error h_state => injection h_eq

-- Helper lemma for frand case: faulty random chains memory monotonicity through e1
private lemma beval_memory_monotonic_frand (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.frand e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- First split on mode (frand checks mode first)
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: proceed with e1 evaluation
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result h_state h_beval1 =>
        -- e1 evaluation succeeded with ok, now split on inner EvalResult
        split at h_eq
        · next config' n =>
          -- e1 evaluated to Value.num n
          -- Now split on if n >= 0 (branch for generating faulty random number)
          split at h_eq
          · -- n >= 0: generate faulty random number
            simp [Functor.map, EST.bind] at h_eq
            split at h_eq
            · next r_result r_state =>
              -- IO.rand succeeded
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              -- config₁ = config' from h_eq_config
              subst h_eq_config
              -- Construct existential for IH
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval LeanPoison.EvalMode.normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
                ⟨w₀, h_state, h_beval1⟩
              -- Apply IH on e1: frand doesn't modify memory, only e1 evaluation does
              exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1_ex l h_contains
            · next r_error r_state => injection h_eq
          · -- n < 0: error case (contradiction with success)
            simp [Functor.map, EST.bind] at h_eq
            split at h_eq
            · next p_result p_state =>
              -- IO.println succeeded, but we get runtimeError (contradiction)
              injection h_eq with h_result h_world
              injection h_result
            · next p_error p_state => injection h_eq
        · next v =>
          -- e1 evaluated to non-number value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · -- e1 evaluation returned ioForbidden (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error h_state => injection h_eq

-- Helper lemma for printInt case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printInt (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.printInt e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- First split on mode (printInt checks mode first)
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: proceed with e1 evaluation
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result h_state h_beval1 =>
        -- e1 evaluation succeeded with ok, now split on inner EvalResult
        split at h_eq
        · next config' n =>
          -- e1 evaluated to Value.num n
          -- IO.println is wrapped in Functor.map/EST.bind
          simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            -- IO.println succeeded
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Construct existential for IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval LeanPoison.EvalMode.normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
              ⟨w₀, h_state, h_beval1⟩
            -- Apply IH on e1: printInt doesn't modify memory, only e1 evaluation does
            exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1_ex l h_contains
          · next p_error p_state => injection h_eq
        · next v =>
          -- e1 evaluated to non-number value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · -- e1 evaluation returned ioForbidden (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error h_state => injection h_eq

-- Helper lemma for printString case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printString (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.printString e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- First split on mode (printString checks mode first)
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: proceed with e1 evaluation
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result h_state h_beval1 =>
        -- e1 evaluation succeeded with ok, now split on inner EvalResult
        split at h_eq
        · next config' s =>
          -- e1 evaluated to Value.str s
          -- IO.println is wrapped in Functor.map/EST.bind
          simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            -- IO.println succeeded
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Construct existential for IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval LeanPoison.EvalMode.normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.str s)) w₁' :=
              ⟨w₀, h_state, h_beval1⟩
            -- Apply IH on e1: printString doesn't modify memory, only e1 evaluation does
            exact IH fuel' h_fuel e1 config₀ config' (Value.str s) h_beval1_ex l h_contains
          · next p_error p_state => injection h_eq
        · next v =>
          -- e1 evaluated to non-string value (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e1 evaluation returned outOfFuel (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e1 evaluation returned runtimeError (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · -- e1 evaluation returned ioForbidden (contradiction)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error h_state => injection h_eq

-- Helper lemma for kwhile case: while loops chain memory monotonicity through iterations
private lemma beval_memory_monotonic_kwhile (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.kwhile e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  unfold LeanPoison.beval at h_eq
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel - 1) config₀ unfolded verbose
  simp at h_eq
  -- After simp: the let binding is inlined and fuel - 1 simplifies
  -- Handle fuel = 0 case separately
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- fuel = fuel' + 1, so fuel - 1 = fuel'
    -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose w₀ = Result.ok (.success config₁ v) w₁
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    -- Define the unfolded expression that kwhile expands to
    let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
    -- h_eq already contains the evaluation of this unfolded expression
    -- Construct existential for IH
    have h_beval_unfolded_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ unfolded verbose w₀' = EST.Out.ok (.success config₁ v) w₁' :=
      ⟨w₀, w₁, h_eq⟩
    -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
    -- The unfolded expression (ite) preserves memory monotonicity by IH (which internally uses the ite proof)
    exact IH fuel' h_fuel unfolded config₀ config₁ v h_beval_unfolded_ex l h_contains

private lemma beval_memory_monotonic_externVal (mode : LeanPoison.EvalMode) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.externVal typ poison pred) verbose w₀ = EST.Out.ok (.success config₁ v) w₁)
    (l : Loc) (_h_contains : config₀.memory.contains l) :
  config₁.memory.contains l := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, beval for Expr.externVal matches on mode first
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- Split on mode
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: returns runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result

private lemma beval_memory_monotonic_externFn (mode : LeanPoison.EvalMode) (arg : Name) (argTyp : Typ) (retSpec : ExternReturn) (effects : List Effect) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.externFn arg argTyp retSpec effects) verbose w₀ = EST.Out.ok (.success config₁ v) w₁)
    (l : Loc) (_h_contains : config₀.memory.contains l) :
  config₁.memory.contains l := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, beval for Expr.externFn matches on mode first
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- Split on mode
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: returns runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result

private lemma beval_memory_monotonic_externPfn (mode : LeanPoison.EvalMode) (arg : Name) (argTyp : Typ) (retSpec : ExternReturn) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel config₀ (Expr.externPfn arg argTyp retSpec) verbose w₀ = EST.Out.ok (.success config₁ v) w₁)
    (l : Loc) (_h_contains : config₀.memory.contains l) :
  config₁.memory.contains l := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eq
    simp [EStateM.pure] at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    -- When fuel > 0, beval for Expr.externPfn matches on mode first
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    -- Split on mode
    split at h_eq
    · -- mode = ioFree: returns ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · -- mode = normal: returns runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result

-- Memory Monotonicity Lemma: evaluation can only add memory locations, never remove them
-- This is a key property that follows from the fact that memory locations are never deallocated
lemma beval_memory_monotonic : ∀ (mode : LeanPoison.EvalMode) (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  (∃ w₀ w₁, LeanPoison.beval mode fuel config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro mode e fuel verbose config₀ config₁ v h_eval l h_contains
  -- Proof by strong induction on fuel, then case analysis on expression
  revert mode e verbose config₀ config₁ v h_eval l h_contains
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro mode e verbose config₀ config₁ v h_eval l h_contains
    -- Convert IH to match helper lemma signatures
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
      intro m h_lt e' config₀' config₁' v' h_eval' l' h_contains'
      exact IH m h_lt mode e' verbose config₀' config₁' v' h_eval' l' h_contains'
    cases e with
    | externVal typ poison pred => exact beval_memory_monotonic_externVal mode typ poison pred fuel verbose config₀ config₁ v h_eval l h_contains
    | externFn arg argTyp retSpec effects => exact beval_memory_monotonic_externFn mode arg argTyp retSpec effects fuel verbose config₀ config₁ v h_eval l h_contains
    | externPfn arg argTyp retSpec => exact beval_memory_monotonic_externPfn mode arg argTyp retSpec fuel verbose config₀ config₁ v h_eval l h_contains
    | num n | bool b | str s | unit =>
      -- Literals don't modify memory: config₁ = config₀
      -- All literals (numbers, booleans, strings, unit) follow the same pattern
      rcases h_eval with ⟨w₀, w₁, h_eq⟩
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        unfold LeanPoison.beval at h_eq
        simp [EStateM.pure] at h_eq
        injection h_eq with h_res
        cases h_res
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        unfold LeanPoison.beval at h_eq
        simp at h_eq
        injection h_eq with h_result h_world
        injection h_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | var x =>
      -- Variables don't modify memory: config₁ = config₀
      rcases h_eval with ⟨w₀, w₁, h_eq⟩
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        unfold LeanPoison.beval at h_eq
        simp [EStateM.pure] at h_eq
        injection h_eq with h_res
        cases h_res
      | succ fuel' =>
        -- When fuel > 0, beval does variable lookup
        unfold LeanPoison.beval at h_eq
        simp at h_eq
        -- Case analysis on variable lookup result
        cases h_lookup : config₀.varEnv.lookup x with
        | some v_found =>
          -- Variable found: beval returns success with same config
          simp [h_lookup] at h_eq
          injection h_eq with h_result h_world
          injection h_result with h_eq_config h_eq_val
          -- Now we have config₁ = config₀ from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
          exact h_contains
        | none =>
          -- Variable not found: beval returns runtimeError (contradiction with success)
          simp [h_lookup] at h_eq
          injection h_eq with h_result h_world
          injection h_result
    | op e1 op e2 =>
      -- Binary operations: memory changes come from e1 and e2, evalOp doesn't allocate
      -- Use helper lemma for binary operations
      exact beval_memory_monotonic_op mode e1 e2 op fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | unaryop op e1 =>
      -- Unary operations: memory changes come from e1, evalUnaryOp doesn't modify memory
      -- Use helper lemma for unary operations
      exact beval_memory_monotonic_unaryop mode op e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | ite e1 e2 e3 =>
      -- Conditionals: memory changes from e1, then either e2 or e3
      -- Use helper lemma for conditionals
      exact beval_memory_monotonic_ite mode e1 e2 e3 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | newRef e1 =>
      -- newRef allocates memory: adds one location
      -- Use helper lemma for newRef
      exact beval_memory_monotonic_newRef mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | assign e1 e2 =>
      -- Assignment: memory changes from e1 and e2, but no new allocations
      -- Use helper lemma for assign
      exact beval_memory_monotonic_assign mode e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | deref e1 =>
      -- Dereference: memory changes only from e1, deref itself doesn't modify memory
      -- Use helper lemma for deref
      exact beval_memory_monotonic_deref mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | seq e1 e2 =>
      -- Sequence: memory changes from e1, then e2
      -- Use helper lemma for sequences
      exact beval_memory_monotonic_seq mode e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | kwhile e1 e2 =>
      -- While loops: needs careful handling of iteration
      -- Use helper lemma for kwhile
      exact beval_memory_monotonic_kwhile mode e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | vlet x e1 e2 =>
      -- Let binding: memory changes from e1, then e2
      -- Use helper lemma for vlet
      exact beval_memory_monotonic_vlet mode x e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | fn x paramType body returnType | pfn x paramType body returnType =>
      -- Function abstractions don't modify memory: config₁ = config₀
      -- Both fn and pfn just create closures without modifying config
      rcases h_eval with ⟨w₀, w₁, h_eq⟩
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        unfold LeanPoison.beval at h_eq
        simp [EStateM.pure] at h_eq
        injection h_eq with h_res
        cases h_res
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        unfold LeanPoison.beval at h_eq
        simp at h_eq
        injection h_eq with h_result h_world
        injection h_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | app e1 e2 =>
      -- Function application: memory changes from e1, e2, and function body
      -- Use helper lemma for app
      exact beval_memory_monotonic_app mode e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | rand e1 =>
      -- Random: memory changes only from e1
      -- Use helper lemma for rand
      exact beval_memory_monotonic_rand mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | frand e1 =>
      -- Faulty random: memory changes only from e1
      -- Use helper lemma for frand
      exact beval_memory_monotonic_frand mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | printInt e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printInt
      exact beval_memory_monotonic_printInt mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
    | printString e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printString
      exact beval_memory_monotonic_printString mode e1 fuel verbose config₀ config₁ v IH_converted h_eval l h_contains
