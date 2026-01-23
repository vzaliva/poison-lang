-- Formal properties of the poison language: VarEnvPreservation

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
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

-- Helper lemma: bevalFunctionBody preserves varEnv
private lemma bevalFunctionBody_preserves_varEnv
    (mode : LeanPoison.EvalMode)
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
  (∃ w₀ w₁, LeanPoison.bevalFunctionBody mode fuel verbose currentConfig closureEnv paramName argValue body isPure w₀ =
      EST.Out.ok (.success finalConfig v) w₁) →
  currentConfig.varEnv = finalConfig.varEnv := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Proof by strong induction on fuel
  revert finalConfig v w₀ w₁ h_eq
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro finalConfig v w₀ w₁ h_eq
    cases n with
    | zero =>
      -- When fuel = 0, bevalFunctionBody returns outOfFuel
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
      -- fuel = fuel' + 1: bevalFunctionBody has enough fuel
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      -- Split on body evaluation result
      split at h_eq
      · next h_body_result h_body_state h_beval_body =>
        split at h_eq
        · next evalConfig v_body =>
          -- Body evaluation succeeded
          split at h_eq
          · -- isPure = true branch
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with pureMode := currentConfig.pureMode }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
          · -- isPure = false branch
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr,
            --                 pureMode := currentConfig.pureMode }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
        · next =>
          -- Body evaluated to outOfFuel (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- Body evaluated to runtimeError (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- Body evaluated to ioForbidden (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_body_error h_body_state =>
        -- Body evaluation failed (contradiction with success)
        injection h_eq

-- Helper lemmas for beval_preserves_varEnv, one per expression constructor

private lemma beval_preserves_varEnv_num (mode : LeanPoison.EvalMode) (n : Int) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.num n) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.num n returns .success config (Value.num n)
  simp at h_eq
  -- After simp, we have: Result.ok (.success config₀ (Value.num n)) w₀ = Result.ok (.success config₁ v) w₁
  injection h_eq with h_result h_world
  -- h_result : .success config₀ (Value.num n) = .success config₁ v
  injection h_result with h_cfg_eq h_val_eq
  -- h_cfg_eq : config₀ = config₁
  -- h_val_eq : Value.num n = v
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_bool (mode : LeanPoison.EvalMode) (b : Bool) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.bool b) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.bool b returns .success config (Value.bool b)
  simp at h_eq
  -- After simp, we have: Result.ok (.success config₀ (Value.bool b)) w₀ = Result.ok (.success config₁ v) w₁
  injection h_eq with h_result h_world
  -- h_result : .success config₀ (Value.bool b) = .success config₁ v
  injection h_result with h_cfg_eq h_val_eq
  -- h_cfg_eq : config₀ = config₁
  -- h_val_eq : Value.bool b = v
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_unit (mode : LeanPoison.EvalMode) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ Expr.unit verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.unit returns .success config Value.unit
  simp at h_eq
  -- After simp, we have: Result.ok (.success config₀ Value.unit) w₀ = Result.ok (.success config₁ v) w₁
  injection h_eq with h_result h_world
  -- h_result : .success config₀ Value.unit = .success config₁ v
  injection h_result with h_cfg_eq h_val_eq
  -- h_cfg_eq : config₀ = config₁
  -- h_val_eq : Value.unit = v
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_str (mode : LeanPoison.EvalMode) (s : String) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.str s) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.str s returns .success config (Value.str s)
  simp at h_eq
  -- After simp, we have: Result.ok (.success config₀ (Value.str s)) w₀ = Result.ok (.success config₁ v) w₁
  injection h_eq with h_result h_world
  -- h_result : .success config₀ (Value.str s) = .success config₁ v
  injection h_result with h_cfg_eq h_val_eq
  -- h_cfg_eq : config₀ = config₁
  -- h_val_eq : Value.str s = v
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_var (mode : LeanPoison.EvalMode) (x : Name) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.var x) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.var x looks up x in varEnv
  simp at h_eq
  -- Case analysis on variable lookup result
  cases h_lookup : config₀.varEnv.lookup x with
  | some v' =>
    -- Variable found: beval returns .success config v'
    simp [h_lookup] at h_eq
    -- After simp, we have: Result.ok (.success config₀ v') w₀ = Result.ok (.success config₁ v) w₁
    injection h_eq with h_result h_world
    -- h_result : .success config₀ v' = .success config₁ v
    injection h_result with h_cfg_eq h_val_eq
    -- h_cfg_eq : config₀ = config₁
    -- h_val_eq : v' = v
    subst h_cfg_eq
    rfl
  | none =>
    -- Variable not found: beval returns runtimeError (contradiction with success)
    simp [h_lookup] at h_eq
    -- After simp, we have: Result.ok (.runtimeError ...) w₀ = Result.ok (.success config₁ v) w₁
    injection h_eq with h_result h_world
    -- h_result : .runtimeError ... = .success config₁ v
    -- This is impossible since runtimeError and success are distinct constructors
    injection h_result

private lemma beval_preserves_varEnv_unaryop (mode : LeanPoison.EvalMode) (op : UnaryOp) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.unaryop op e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- When fuel > 0, beval for Expr.unaryop evaluates e1 first, then applies evalUnaryOp
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  -- Case analysis on evaluation of e1
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    -- e1 evaluated successfully; inspect inner result
    split at h_eq
    · next config' v' =>
      -- e1 succeeded with config' and v'
      -- Now apply evalUnaryOp
      cases h_evalUnaryOp : LeanPoison.evalUnaryOp op v' with
      | some v_result =>
        -- evalUnaryOp succeeded
        simp [h_evalUnaryOp] at h_eq
        injection h_eq with h_result h_world
        injection h_result with h_cfg_eq h_val_eq
        -- h_cfg_eq : config' = config₁
        -- h_val_eq : v_result = v
        -- Use IH on e1: we have h_beval1 showing e1 evaluated successfully
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' v') w₁' :=
          ⟨w₀, h_state1, h_beval1⟩
        have h_varEnv_eq : config₀.varEnv = config'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config' v' h_beval1_ex
        -- Now use h_cfg_eq to show config'.varEnv = config₁.varEnv
        rw [h_cfg_eq] at h_varEnv_eq
        exact h_varEnv_eq
      | none =>
        -- evalUnaryOp failed (contradiction with success)
        simp [h_evalUnaryOp] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next =>
      -- e1 evaluated to outOfFuel (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · next msg =>
      -- e1 evaluated to runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · next =>
      -- e1 evaluated to ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
  · next h_error h_state =>
    -- e1 evaluation failed (contradiction with success)
    injection h_eq


private lemma beval_preserves_varEnv_op (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (op : Op) (fuel' : Nat) (verbose : Bool) (config₀ config₃ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.op e1 op e2) verbose w₀ = EST.Out.ok (.success config₃ v) w₁) :
  config₀.varEnv = config₃.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  -- Case analysis on evaluation of e1
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    -- e1 evaluated successfully; inspect inner result
    split at h_eq
    · next config₁ v₁ =>
      -- e1 succeeded with config₁ and v₁
      simp [EST.bind] at h_eq
      -- Case analysis on evaluation of e2
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        -- e2 evaluated successfully; inspect inner result
        split at h_eq
        · next config₂ v₂ =>
          -- e2 succeeded with config₂ and v₂
          -- Now apply evalOp
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
            -- evalOp succeeded
            simp [h_evalOp] at h_eq
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            -- h_cfg_eq : config₂ = config₃
            -- h_val_eq : v_result = v
            subst h_cfg_eq
            -- Use IH on e1 and e2
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            -- Construct existential for e1
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁ v₁) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            have h_varEnv_eq1 : config₀.varEnv = config₁.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁ v₁ h_beval1_ex
            -- Construct existential for e2
            have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁ e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
              ⟨h_state1, h_state2, h_beval2⟩
            have h_varEnv_eq2 : config₁.varEnv = config₂.varEnv := IH fuel' h_fuel mode e2 verbose config₁ config₂ v₂ h_beval2_ex
            -- Chain the equalities
            exact Eq.trans h_varEnv_eq1 h_varEnv_eq2
          | none =>
            -- evalOp failed (contradiction with success)
            simp [h_evalOp] at h_eq
            injection h_eq with h_result h_world
            injection h_result
        · next =>
          -- e2 evaluated to outOfFuel (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          -- e2 evaluated to runtimeError (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          -- e2 evaluated to ioForbidden (contradiction with success)
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error2 h_state2 =>
        -- e2 evaluation failed (contradiction with success)
        injection h_eq
    · next =>
      -- e1 evaluated to outOfFuel (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · next msg =>
      -- e1 evaluated to runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · next =>
      -- e1 evaluated to ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
  · next h_error1 h_state1 =>
    -- e1 evaluation failed (contradiction with success)
    injection h_eq

private lemma beval_preserves_varEnv_ite (mode : LeanPoison.EvalMode) (e1 e2 e3 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.ite e1 e2 e3) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  -- Case analysis on evaluation of e1
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    -- e1 evaluated successfully; inspect inner result
    split at h_eq
    · next config₁' =>
      -- e1 evaluated to bool true; evaluate e2
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        -- e2 evaluated successfully
        split at h_eq
        · next config₂ v₂ =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Construct existentials for e1 and e2
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool true)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          have h_varEnv_eq1 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁' (Value.bool true) h_beval1_ex
          have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
            ⟨h_state1, h_state2, h_beval2⟩
          have h_varEnv_eq2 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e2 verbose config₁' config₂ v₂ h_beval2_ex
          exact Eq.trans h_varEnv_eq1 h_varEnv_eq2
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error2 h_state2 => injection h_eq
    · next config₁' =>
      -- e1 evaluated to bool false; evaluate e3
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result3 h_state3 h_beval3 =>
        -- e3 evaluated successfully
        split at h_eq
        · next config₂ v₃ =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Construct existentials for e1 and e3
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool false)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          have h_varEnv_eq1 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁' (Value.bool false) h_beval1_ex
          have h_beval3_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e3 verbose w₀' = EST.Out.ok (.success config₂ v₃) w₁' :=
            ⟨h_state1, h_state3, h_beval3⟩
          have h_varEnv_eq3 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e3 verbose config₁' config₂ v₃ h_beval3_ex
          exact Eq.trans h_varEnv_eq1 h_varEnv_eq3
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error3 h_state3 => injection h_eq
    · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error1 h_state1 => injection h_eq

private lemma beval_preserves_varEnv_newRef (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.newRef e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result h_state h_beval1 =>
    split at h_eq
    · next config' n =>
      injection h_eq with h_result h_world
      injection h_result with h_cfg_eq h_val_eq
      subst h_cfg_eq
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
        ⟨w₀, h_state, h_beval1⟩
      have h_varEnv_eq : config₀.varEnv = config'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config' (Value.num n) h_beval1_ex
      simp [freshAddr]
      exact h_varEnv_eq
    · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_assign (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.assign e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    split at h_eq
    · next config₁' l =>
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        split at h_eq
        · next config₂ n =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.loc l)) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          have h_varEnv_eq1 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁' (Value.loc l) h_beval1_ex
          have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ (Value.num n)) w₁' :=
            ⟨h_state1, h_state2, h_beval2⟩
          have h_varEnv_eq2 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e2 verbose config₁' config₂ (Value.num n) h_beval2_ex
          simp
          exact Eq.trans h_varEnv_eq1 h_varEnv_eq2
        · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error2 h_state2 => injection h_eq
    · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error1 h_state1 => injection h_eq

private lemma beval_preserves_varEnv_deref (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.deref e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result h_state h_beval1 =>
    split at h_eq
    · next config' l =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.loc l)) w₁' :=
        ⟨w₀, h_state, h_beval1⟩
      have h_varEnv_eq : config₀.varEnv = config'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config' (Value.loc l) h_beval1_ex
      cases h_mem_lookup : config'.memory[l]? with
      | some n =>
        simp [h_mem_lookup] at h_eq
        injection h_eq with h_result h_world
        injection h_result with h_cfg_eq h_val_eq
        subst h_cfg_eq
        exact h_varEnv_eq
      | none =>
        simp [h_mem_lookup] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_seq (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.seq e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    split at h_eq
    · next config₁' v₁ =>
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        split at h_eq
        · next config₂ v₂ =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' v₁) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          have h_varEnv_eq1 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁' v₁ h_beval1_ex
          have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
            ⟨h_state1, h_state2, h_beval2⟩
          have h_varEnv_eq2 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e2 verbose config₁' config₂ v₂ h_beval2_ex
          exact Eq.trans h_varEnv_eq1 h_varEnv_eq2
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error2 h_state2 => injection h_eq
    · next h_error1 h_state1 =>
      -- e1 evaluation failed (contradiction with success)
      injection h_eq with h_result_eq h_world_eq
      injection h_result_eq
    · next msg =>
      -- e1 evaluated to runtimeError (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
    · next =>
      -- e1 evaluated to ioForbidden (contradiction with success)
      simp [pure] at h_eq
      injection h_eq with h_result h_world
      injection h_result
  · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_kwhile (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.kwhile e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel'.succ - 1) config₀ unfolded verbose
  simp at h_eq
  -- After simp: the let binding is inlined and fuel'.succ - 1 simplifies to fuel'
  -- So we have: beval mode fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose w₀ = Result.ok (.success config₁ v) w₁
  have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
  -- Define the unfolded expression that kwhile expands to
  let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  -- Construct existential for the unfolded expression
  have h_unfolded_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ unfolded verbose w₀' = EST.Out.ok (.success config₁ v) w₁' :=
    ⟨w₀, w₁, h_eq⟩
  -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
  -- The unfolded expression (ite) preserves varEnv by IH (which internally uses the ite proof)
  exact IH fuel' h_fuel mode unfolded verbose config₀ config₁ v h_unfolded_ex

private lemma beval_preserves_varEnv_vlet (mode : LeanPoison.EvalMode) (x : Name) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.vlet x e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result1 h_state1 h_beval1 =>
    split at h_eq
    · next config₁' v₁ =>
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        split at h_eq
        · next config₂ v₂ =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' v₁) w₁' :=
            ⟨w₀, h_state1, h_beval1⟩
          have h_varEnv_eq : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e1 verbose config₀ config₁' v₁ h_beval1_ex
          simp
          exact h_varEnv_eq
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error2 h_state2 => injection h_eq
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error1 h_state1 => injection h_eq

private lemma beval_preserves_varEnv_fn (mode : LeanPoison.EvalMode) (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.fn x paramType body returnType) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  injection h_eq with h_result h_world
  injection h_result with h_cfg_eq h_val_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_pfn (mode : LeanPoison.EvalMode) (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.pfn x paramType body returnType) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  injection h_eq with h_result h_world
  injection h_result with h_cfg_eq h_val_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_app (mode : LeanPoison.EvalMode) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.app e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  simp [bind, Bind.bind, EST.bind] at h_eq
  split at h_eq
  · next h_result1 h_state1 h_beval2 =>
    split at h_eq
    · next config₁' v₂ =>
      simp [EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval1 =>
        split at h_eq
        · next config₂ x body env =>
          split at h_eq
          · injection h_eq with h_result h_world; injection h_result
          ·             -- pureMode is false, call bevalFunctionBody
            -- h_eq contains: bevalFunctionBody mode fuel' verbose config₂ env x v₂ body false h_state2 = Result.ok (.success config₁ v) w₁
            -- Save this equality
            have h_bevalFunctionBody_eq : LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body false h_state2 =
                EST.Out.ok (.success config₁ v) w₁ := h_eq
            -- We don't need config₂ = config₁; bevalFunctionBody_preserves_varEnv will show config₂.varEnv = config₁.varEnv
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            -- Construct existentials for e1 and e2
            have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
              ⟨w₀, h_state1, h_beval2⟩
            have h_varEnv_eq2 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e2 verbose config₀ config₁' v₂ h_beval2_ex
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.closure x body env)) w₁' :=
              ⟨h_state1, h_state2, h_beval1⟩
            have h_varEnv_eq1 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e1 verbose config₁' config₂ (Value.closure x body env) h_beval1_ex
            -- Apply helper lemma directly with the indexed equality
            have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body false w₀' =
                EST.Out.ok (.success config₁ v) w₁' :=
              ⟨h_state2, w₁, h_bevalFunctionBody_eq⟩
            have h_funcBody : config₂.varEnv = config₁.varEnv :=
              bevalFunctionBody_preserves_varEnv mode fuel' verbose config₂ config₁ env x v₂ body false v h_bevalFunctionBody_ex
            -- Chain: config₀.varEnv = config₁'.varEnv (by h_varEnv_eq2) = config₂.varEnv (by h_varEnv_eq1) = config₁.varEnv (by h_funcBody)
            exact Eq.trans (Eq.trans h_varEnv_eq2 h_varEnv_eq1) h_funcBody
        · next config₂ x body env =>
          cases h_pure : Expr.toPExpr? body with
          | none =>
              simp [h_pure, pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
          | some _ =>
              simp [h_pure] at h_eq
              -- peClosure case (pure function), call bevalFunctionBody with isPure=true
              -- h_eq contains: bevalFunctionBody mode fuel' verbose config₂ env x v₂ body true h_state2 = Result.ok (.success config₁ v) w₁
              have h_bevalFunctionBody_eq : LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body true h_state2 =
                  EST.Out.ok (.success config₁ v) w₁ := h_eq
              -- We don't need config₂ = config₁; bevalFunctionBody_preserves_varEnv will show config₂.varEnv = config₁.varEnv
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              -- Construct existentials for e1 and e2
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
                ⟨w₀, h_state1, h_beval2⟩
              have h_varEnv_eq2 : config₀.varEnv = config₁'.varEnv := IH fuel' h_fuel mode e2 verbose config₀ config₁' v₂ h_beval2_ex
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval mode fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.peClosure x body env)) w₁' :=
                ⟨h_state1, h_state2, h_beval1⟩
              have h_varEnv_eq1 : config₁'.varEnv = config₂.varEnv := IH fuel' h_fuel mode e1 verbose config₁' config₂ (Value.peClosure x body env) h_beval1_ex
              -- Apply helper lemma directly with the indexed equality
              have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody mode fuel' verbose config₂ env x v₂ body true w₀' =
                  EST.Out.ok (.success config₁ v) w₁' :=
                ⟨h_state2, w₁, h_bevalFunctionBody_eq⟩
              have h_funcBody : config₂.varEnv = config₁.varEnv :=
                bevalFunctionBody_preserves_varEnv mode fuel' verbose config₂ config₁ env x v₂ body true v h_bevalFunctionBody_ex
              -- Chain: config₀.varEnv = config₁'.varEnv (by h_varEnv_eq2) = config₂.varEnv (by h_varEnv_eq1) = config₁.varEnv (by h_funcBody)
              exact Eq.trans (Eq.trans h_varEnv_eq2 h_varEnv_eq1) h_funcBody
        · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
        · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next h_error2 h_state2 => injection h_eq
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
  · next h_error1 h_state1 => injection h_eq

private lemma beval_preserves_varEnv_rand (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.rand e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    -- In ioFree mode, rand returns ioForbidden (contradiction with success)
    simp at h_eq
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result h_state h_beval1 =>
      split at h_eq
      · next config' n =>
        split at h_eq
        · simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next r_result r_state =>
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval .normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
              ⟨w₀, h_state, h_beval1⟩
            exact IH fuel' h_fuel .normal e1 verbose config₀ config' (Value.num n) h_beval1_ex
          · next r_error r_state => injection h_eq
        · simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state => injection h_eq with h_result h_world; injection h_result
          · next p_error p_state => injection h_eq
      · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_frand (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.frand e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    -- In ioFree mode, frand returns ioForbidden (contradiction with success)
    simp at h_eq
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result h_state h_beval1 =>
      split at h_eq
      · next config' n =>
        split at h_eq
        · simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next r_result r_state =>
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval .normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
              ⟨w₀, h_state, h_beval1⟩
            exact IH fuel' h_fuel .normal e1 verbose config₀ config' (Value.num n) h_beval1_ex
          · next r_error r_state => injection h_eq
        · simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state => injection h_eq with h_result h_world; injection h_result
          · next p_error p_state => injection h_eq
      · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_printInt (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.printInt e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    -- In ioFree mode, printInt returns ioForbidden (contradiction with success)
    simp at h_eq
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result h_state h_beval1 =>
      split at h_eq
      · next config' n =>
        simp [Functor.map, EST.bind] at h_eq
        split at h_eq
        · next p_result p_state =>
          injection h_eq with h_result h_world
          injection h_result with h_cfg_eq h_val_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval .normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num n)) w₁' :=
            ⟨w₀, h_state, h_beval1⟩
          exact IH fuel' h_fuel .normal e1 verbose config₀ config' (Value.num n) h_beval1_ex
        · next p_error p_state => injection h_eq
      · next v => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next msg => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
      · next => simp [pure] at h_eq; injection h_eq with h_result h_world; injection h_result
    · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_printString (mode : LeanPoison.EvalMode) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (mode' : LeanPoison.EvalMode) (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval mode' m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) → config₀.varEnv = config₁.varEnv)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.printString e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    -- In ioFree mode, printString returns ioForbidden (contradiction with success)
    simp at h_eq
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result h_state h_beval1 =>
      cases h_result with
      | success config' v_str =>
        cases v_str with
        | str s =>
          simp [Functor.map, EST.bind] at h_eq
          split at h_eq
          · next p_result p_state =>
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval .normal fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.str s)) w₁' :=
              ⟨w₀, h_state, h_beval1⟩
            exact IH fuel' h_fuel .normal e1 verbose config₀ config' (Value.str s) h_beval1_ex
          · next p_error p_state => injection h_eq
        | num _ | bool _ | unit | loc _ | closure _ _ _ | peClosure _ _ _ =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      | outOfFuel =>
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | runtimeError msg =>
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
      | ioForbidden =>
        simp [pure] at h_eq
        injection h_eq with h_result h_world
        injection h_result
    · next h_error h_state => injection h_eq

private lemma beval_preserves_varEnv_externVal (mode : LeanPoison.EvalMode) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.externVal typ poison pred) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result

private lemma beval_preserves_varEnv_externFn (mode : LeanPoison.EvalMode) (arg : Name) (argTyp : Typ) (retSpec : ExternReturn) (effects : List Effect) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.externFn arg argTyp retSpec effects) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result

private lemma beval_preserves_varEnv_externPfn (mode : LeanPoison.EvalMode) (arg : Name) (argTyp : Typ) (retSpec : ExternReturn) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (h_eval : ∃ w₀ w₁, LeanPoison.beval mode fuel'.succ config₀ (Expr.externPfn arg argTyp retSpec) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) :
  config₀.varEnv = config₁.varEnv := by
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases mode with
  | ioFree =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result
  | normal =>
    simp [pure] at h_eq
    injection h_eq with h_result h_world
    injection h_result

-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)
lemma beval_preserves_varEnv (mode : LeanPoison.EvalMode) (e : Expr) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value) :
  (exists w₀ w₁, LeanPoison.beval mode fuel config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.varEnv = config₁.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel, then case analysis on e
  -- For all expression forms, the varEnv field is never modified
  -- (even in let bindings, we create a new config with extended varEnv for the body,
  --  but the final result restores the original varEnv)
  revert e config₀ config₁ v h_eval verbose mode
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro mode e verbose config₀ config₁ v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, beval returns outOfFuel at any world; success is impossible.
      rcases h_eval with ⟨w₀, w₁, h_eq⟩
      unfold LeanPoison.beval at h_eq
      simp [EStateM.pure] at h_eq
      -- After unfold and simp, we have: Result.ok .outOfFuel w₀ = Result.ok (.success config₁ v) w₁
      -- Use injection to extract the equality of the inner EvalResult values
      injection h_eq with h_res
      -- h_res : .outOfFuel = .success config₁ v
      -- outOfFuel and success are distinct constructors, so this is impossible
      cases h_res
    | succ fuel' =>
      cases e with
        | externVal typ poison pred => exact beval_preserves_varEnv_externVal mode typ poison pred fuel' verbose config₀ config₁ v h_eval
        | externFn arg argTyp retSpec effects => exact beval_preserves_varEnv_externFn mode arg argTyp retSpec effects fuel' verbose config₀ config₁ v h_eval
        | externPfn arg argTyp retSpec => exact beval_preserves_varEnv_externPfn mode arg argTyp retSpec fuel' verbose config₀ config₁ v h_eval
        | num n => exact beval_preserves_varEnv_num mode n fuel' verbose config₀ config₁ v h_eval
        | bool b => exact beval_preserves_varEnv_bool mode b fuel' verbose config₀ config₁ v h_eval
        | unit => exact beval_preserves_varEnv_unit mode fuel' verbose config₀ config₁ v h_eval
        | str s => exact beval_preserves_varEnv_str mode s fuel' verbose config₀ config₁ v h_eval
        | var x => exact beval_preserves_varEnv_var mode x fuel' verbose config₀ config₁ v h_eval
        | unaryop op e1 =>
          exact beval_preserves_varEnv_unaryop mode op e1 fuel' verbose config₀ config₁ v IH h_eval
        | op e1 op e2 =>
          exact beval_preserves_varEnv_op mode e1 e2 op fuel' verbose config₀ config₁ v IH h_eval
        | ite e1 e2 e3 =>
          exact beval_preserves_varEnv_ite mode e1 e2 e3 fuel' verbose config₀ config₁ v IH h_eval
        | newRef e1 =>
          exact beval_preserves_varEnv_newRef mode e1 fuel' verbose config₀ config₁ v IH h_eval
        | assign e1 e2 =>
          exact beval_preserves_varEnv_assign mode e1 e2 fuel' verbose config₀ config₁ v IH h_eval
        | deref e1 =>
          exact beval_preserves_varEnv_deref mode e1 fuel' verbose config₀ config₁ v IH h_eval
        | seq e1 e2 =>
          exact beval_preserves_varEnv_seq mode e1 e2 fuel' verbose config₀ config₁ v IH h_eval
        | kwhile e1 e2 =>
          exact beval_preserves_varEnv_kwhile mode e1 e2 fuel' verbose config₀ config₁ v IH h_eval
        | vlet x e1 e2 =>
          exact beval_preserves_varEnv_vlet mode x e1 e2 fuel' verbose config₀ config₁ v IH h_eval
        | fn x paramType body returnType =>
          exact beval_preserves_varEnv_fn mode x paramType body returnType fuel' verbose config₀ config₁ v h_eval
        | pfn x paramType body returnType =>
          exact beval_preserves_varEnv_pfn mode x paramType body returnType fuel' verbose config₀ config₁ v h_eval
        | app e1 e2 =>
          exact beval_preserves_varEnv_app mode e1 e2 fuel' verbose config₀ config₁ v IH h_eval
        | rand e1 =>
          exact beval_preserves_varEnv_rand mode e1 fuel' verbose config₀ config₁ v IH h_eval
        | frand e1 =>
          exact beval_preserves_varEnv_frand mode e1 fuel' verbose config₀ config₁ v IH h_eval
        | printInt e1 =>
          exact beval_preserves_varEnv_printInt mode e1 fuel' verbose config₀ config₁ v IH h_eval
        | printString e1 =>
          exact beval_preserves_varEnv_printString mode e1 fuel' verbose config₀ config₁ v IH h_eval
