-- Common big-step semantics properties for the Poison Language
--
-- This file contains shared definitions and properties related to evaluation
-- semantics, including evaluation relations and runtime configuration well-formedness.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep

open Std

-- ================================================================
-- Evaluation Relations
-- ================================================================

-- Big-step termination relation to a final configuration and resulting Value
-- Note: evaluation returns EvalResult
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.success c₁ out)

-- World-indexed termination (IO equality-friendly).
def terminatesToW (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld),
    LeanPoison.beval fuel c₀ e verbose w₀ = EST.Out.ok (.success c₁ out) w₁

-- Divergence relation: program runs out of fuel
def diverges (e : Expr) (c₀ : Config) : Prop :=
  ∀ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure LeanPoison.EvalResult.outOfFuel

-- Stuck relation: program encounters a runtime error
def stuck (e : Expr) (c₀ : Config) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (msg : String),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.runtimeError msg)

-- ================================================================
-- Runtime Configuration Well-formedness
-- ================================================================

/-- A runtime configuration is well-formed if all addresses in memory are below nextAddr.
    This captures that nextAddr is the "high-water mark" for allocated physical addresses,
    analogous to wfTypeContext for logical locations. -/
def wfConfig (cfg : Config) : Prop :=
  ∀ a, cfg.memory.contains a → a < cfg.nextAddr

/-- If a config is well-formed, then nextAddr is not already in memory.
    This is the key property needed to prove freshness of newly allocated addresses. -/
lemma nextAddr_not_in_memory (cfg : Config) :
    wfConfig cfg → ¬cfg.memory.contains cfg.nextAddr := by
  intro hwf hcontains
  have h := hwf cfg.nextAddr hcontains
  exact Nat.lt_irrefl cfg.nextAddr h

/-- Evaluation preserves config well-formedness: if we start from a well-formed config
    (all addresses in memory are below nextAddr), then the final config is also well-formed.
    This follows from the fact that freshAddr returns nextAddr and increments it. -/
lemma wfConfig_preserved (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ := by
  -- TODO: Prove by induction on evaluation structure.
  -- Key insight: only newRef allocates new addresses, and it uses freshAddr which
  -- returns config.nextAddr and increments it to config.nextAddr + 1.
  -- For any address a in the new memory:
  --   - If a was in old memory: a < old_nextAddr ≤ new_nextAddr
  --   - If a = old_nextAddr: a < old_nextAddr + 1 = new_nextAddr
  sorry

/-- World-indexed version of wfConfig_preserved for use in FR proofs. -/
lemma wfConfig_preservedW (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesToW e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ := by
  intro _hterm hwf₀
  -- TODO: Follows from wfConfig_preserved once that is proven.
  -- The termination witness can be converted between terminatesToW and terminatesTo.
  sorry

-- ================================================================
-- Evaluation Structure Lemmas
-- ================================================================

-- Helper lemma: extract evaluation structure from successful beval of unary operation.
lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    LeanPoison.evalUnaryOp op v1 = some v ∧
    config₁.memory = config₂.memory ∧
    config₁.varEnv = config₂.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          cases h_evalOp : LeanPoison.evalUnaryOp op v₁ with
          | some v_result =>
              simp [h_evalOp] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              have h_mem_eq : config₁.memory = config₂.memory := by
                rw [h_eq_cfg]
              have h_var_eq : config₁.varEnv = config₂.varEnv := by
                rw [h_eq_cfg]
              -- Rewrite evalUnaryOp to use the final value v.
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                  EST.Out.ok (.success config₁ v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, v₁, h_beval1_ex, h_evalOp, h_mem_eq, h_var_eq⟩
          | none =>
              simp [h_evalOp] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of binary operation.
lemma bevalOp_structure (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₃ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose w₀ =
      EST.Out.ok (.success config₃ v) w₁) →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₁ e2 verbose w₀'' =
        EST.Out.ok (.success config₂ v2) w₁'') ∧
    LeanPoison.evalOp op v1 v2 = some v ∧
    config₂.memory = config₃.memory ∧
    config₂.varEnv = config₃.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          try simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₂ v₂ =>
              cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
              | some v_result =>
                  simp [h_evalOp] at h_eq
                  injection h_eq with h_eq_result h_eq_state
                  injection h_eq_result with h_eq_cfg h_eq_val
                  have h_mem_eq : config₂.memory = config₃.memory := by
                    rw [h_eq_cfg]
                  have h_var_eq : config₂.varEnv = config₃.varEnv := by
                    rw [h_eq_cfg]
                  rw [h_eq_val] at h_evalOp
                  subst h_eq_cfg
                  have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                        EST.Out.ok (.success config₁ v₁) w₁' :=
                    ⟨w₀, h_state1, h_beval1⟩
                  have h_beval2_ex : ∃ w₀'' w₁'', LeanPoison.beval fuel' config₁ e2 verbose w₀'' =
                        EST.Out.ok (.success config₂ v₂) w₁'' :=
                    ⟨h_state1, h_state2, h_beval2⟩
                  simp only [Nat.add_sub_cancel]
                  exact ⟨config₁, config₂, v₁, v₂, h_beval1_ex, h_beval2_ex, h_evalOp, h_mem_eq, h_var_eq⟩
              | none =>
                  simp [h_evalOp] at h_eq
                  injection h_eq with h_eq_result h_eq_state
                  injection h_eq_result
            · next =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
            · next msg =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of sequence.
lemma bevalSeq_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₁ e2 verbose w₀'' =
        EST.Out.ok (.success config₂ v) w₁'') := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁ v₁ =>
          try simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₂ v₂ =>
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              subst h_eq_val
              subst h_eq_cfg
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                    EST.Out.ok (.success config₁ v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex : ∃ w₀'' w₁'', LeanPoison.beval fuel' config₁ e2 verbose w₀'' =
                    EST.Out.ok (.success config₂ v₂) w₁'' :=
                ⟨h_state1, h_state2, h_beval2⟩
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, v₁, h_beval1_ex, h_beval2_ex⟩
            · next =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
            · next msg =>
                simp [pure] at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
        · next msg =>
            simp [pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of vlet.
lemma bevalVlet_structure (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose w₀ =
      EST.Out.ok (.success config_final v) w₁) →
  ∃ (config₁ config₂ config₃ : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ v1) w₁') ∧
    config₂ = { config₁ with varEnv := config₁.varEnv.update x v1 } ∧
    (∃ w₀'' w₁'', LeanPoison.beval (fuel - 1) config₂ e2 verbose w₀'' =
        EST.Out.ok (.success config₃ v) w₁'') ∧
    config_final = { config₃ with varEnv := config₁.varEnv } := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁' v₁ =>
          -- e1 evaluated successfully, now e2
          let config₂' := { config₁' with varEnv := config₁'.varEnv.update x v₁ }
          -- Evaluate e2 in config₂'
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₃' v₂ =>
              -- e2 evaluated successfully
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              -- Construct existentials for h_beval1 and h_beval2
              have h_beval1_ex :
                  ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                    EST.Out.ok (.success config₁' v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex :
                  ∃ w₀'' w₁'', LeanPoison.beval fuel' config₂' e2 verbose w₀'' =
                    EST.Out.ok (.success config₃' v₂) w₁'' :=
                ⟨h_state1, h_state2, h_beval2⟩
              -- Now subst to get final config and value
              subst h_eq_cfg h_eq_val
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁', config₂', config₃', v₁, h_beval1_ex, rfl, h_beval2_ex, rfl⟩
            · next =>
              simp [pure] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
            · next msg =>
              simp [pure] at h_eq
              injection h_eq with h_eq_result h_eq_state
              injection h_eq_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of printInt
lemma bevalPrintInt_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.printInt e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ n, v1 = Value.num n) ∧
    v = Value.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' v₁ =>
          -- After the println, we return success
          simp [EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_⟩
            · simp
            · simp
            · simp
          · next p_error p_state =>
            injection h_eq
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
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of printString
lemma bevalPrintString_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.printString e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ s, v1 = Value.str s) ∧
    v = Value.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      injection h_eq with h_contr
      cases h_contr
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' v₁ =>
          -- After the println, we return success
          simp [EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            subst h_eq_cfg h_eq_val
            -- Construct existential for h_beval1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.str v₁)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            simp only [Nat.add_sub_cancel]
            refine ⟨config', Value.str v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_⟩
            · simp
            · simp
            · simp
          · next p_error p_state =>
            injection h_eq
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
      · next h_error1 h_state1 =>
        injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of newRef
lemma bevalNewRef_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁) →
  ∃ (config₁ : Config) (n : Int) (a : Address),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' =
        EST.Out.ok (.success config₁ (Value.num n)) w₁') ∧
    a = config₁.nextAddr ∧
    config₂.memory = (config₁.memory.update a n) ∧
    config₂.nextAddr = config₁.nextAddr + 1 ∧
    config₂.varEnv = config₁.varEnv ∧
    v = Value.loc a := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      cases h_result1 with
      | success config' v' =>
        cases v' with
        | num n =>
          simp at h_eq
          injection h_eq with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
              EST.Out.ok (.success config' (Value.num n)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          simp only [Nat.add_sub_cancel]
          use config', n, config'.nextAddr, h_beval1_ex, rfl
          simp [freshAddr] at h_eq_cfg h_eq_val
          constructor
          · -- config₂.memory = config₁.memory.update a n
            rw [← h_eq_cfg]
          constructor
          · -- config₂.nextAddr = config₁.nextAddr + 1
            rw [← h_eq_cfg]
          constructor
          · -- config₂.varEnv = config₁.varEnv
            rw [← h_eq_cfg]
          · -- v = Value.loc a
            rw [← h_eq_val]
        | bool _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
          simp [pure] at h_eq
          injection h_eq with h_contr
          cases h_contr
      | outOfFuel =>
        simp [pure] at h_eq
        injection h_eq with h_contr
        cases h_contr
      | runtimeError msg =>
        simp [pure] at h_eq
        injection h_eq with h_contr
        cases h_contr
    · next h_error1 h_state1 =>
      injection h_eq
