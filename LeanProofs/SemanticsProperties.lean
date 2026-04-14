-- Common big-step semantics properties for the Poison Language
--
-- This file contains shared definitions and properties related to evaluation
-- semantics, including evaluation relations and runtime configuration well-formedness.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Aux
import Mathlib.Tactic
import Batteries.Data.List.Lemmas

open Std

-- ================================================================
-- Evaluation Relations
-- ================================================================

-- Big-step termination relation to a final configuration and resulting Value
-- Note: evaluation returns EvalResult (pure, no IO)
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value): Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.success c₁ out

-- Divergence relation: program runs out of fuel
def diverges (e : Expr) (c₀ : Config) : Prop :=
  ∀ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.outOfFuel

-- Stuck relation: program encounters a runtime error
def stuck (e : Expr) (c₀ : Config)  : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (msg : String),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.runtimeError msg

-- ================================================================
-- Runtime Configuration Well-formedness
-- ================================================================

mutual
  /-- A runtime value is well-formed w.r.t. a bound on addresses. -/
  inductive wfValue (next : Address) : Value → Prop
    | num (n : Int) : wfValue next (Value.num n)
    | bool (b : Bool) : wfValue next (Value.bool b)
    | unit : wfValue next Value.unit
    | str (s : String) : wfValue next (Value.str s)
    | loc {a : Address} : a < next → wfValue next (Value.loc a)
    | closure (x : Name) (e : Expr) (env : VarEnv) :
        wfVarEnv next env → wfValue next (Value.closure x e env)
    | peClosure (x : Name) (e : Expr) (env : VarEnv) :
        wfVarEnv next env → wfValue next (Value.peClosure x e env)

  /-- A runtime variable environment is well-formed if all stored values are. -/
  inductive wfVarEnv (next : Address) : VarEnv → Prop
    | nil : wfVarEnv next []
    | cons (x : Name) (v : Value) (env : VarEnv) :
        wfValue next v → wfVarEnv next env → wfVarEnv next ((x, v) :: env)
end

/-- A runtime configuration is well-formed if:
    (1) all addresses in memory are below nextAddr, and
    (2) all values in varEnv only reference addresses below nextAddr.
    This captures that nextAddr is the "high-water mark" for allocated physical addresses,
    analogous to wfTypeContext for logical locations. -/
def wfConfig (cfg : Config) : Prop :=
  (∀ a, cfg.memory.contains a → a < cfg.nextAddr) ∧
  wfVarEnv cfg.nextAddr cfg.varEnv

/-- If a config is well-formed, then nextAddr is not already in memory.
    This is the key property needed to prove freshness of newly allocated addresses. -/
lemma nextAddr_not_in_memory (cfg : Config) :
    wfConfig cfg → ¬cfg.memory.contains cfg.nextAddr := by
  intro hwf hcontains
  have h := hwf.1 cfg.nextAddr hcontains
  exact Nat.lt_irrefl cfg.nextAddr h

-- ================================================================
-- Runtime VarEnv Lookup/Update Lemmas
-- ================================================================

-- If y ≠ x, then updating runtime VarEnv with x does not affect lookup y
lemma VarEnv_lookup_update_ne (env : VarEnv) (x y : Name) (v : Value) (h_ne : y ≠ x) :
  (env.update x v).lookup y = env.lookup y := by
  simp [VarEnv.update, VarEnv.lookup]
  exact List_lookup_cons_ne env x y v h_ne

-- ================================================================
-- Evaluation Structure Lemmas
-- ================================================================

-- Helper lemma: extract evaluation structure from successful beval of unary operation.
lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.evalUnaryOp op v1 = some v ∧
    config₁.memory = config₂.memory ∧
    config₁.varEnv = config₂.varEnv ∧
    config₁.nextAddr = config₂.nextAddr ∧
    config₁.pureMode = config₂.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        cases h_evalOp : LeanPoison.evalUnaryOp op v₁ with
        | some v_result =>
            simp [h_evalOp] at h_eq
            obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
            have h_mem_eq : config₁.memory = config₂.memory := by
              rw [h_eq_cfg]
            have h_var_eq : config₁.varEnv = config₂.varEnv := by
              rw [h_eq_cfg]
            have h_next_eq : config₁.nextAddr = config₂.nextAddr := by
              rw [h_eq_cfg]
            have h_pure_eq : config₁.pureMode = config₂.pureMode := by
              rw [h_eq_cfg]
            rw [h_eq_val] at h_evalOp
            subst h_eq_cfg
            simp only [Nat.add_sub_cancel]
            exact ⟨config₁, v₁, h_beval1, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
        | none =>
            simp [h_evalOp] at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of binary operation.
lemma bevalOp_structure (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₃ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose =
      .success config₃ v →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v2 ∧
    LeanPoison.evalOp op v1 v2 = some v ∧
    config₂.memory = config₃.memory ∧
    config₂.varEnv = config₃.varEnv ∧
    config₂.nextAddr = config₃.nextAddr ∧
    config₂.pureMode = config₃.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        split at h_eq
        · next config₂ v₂ h_beval2 =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
              simp [h_evalOp] at h_eq
              obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
              have h_mem_eq : config₂.memory = config₃.memory := by rw [h_eq_cfg]
              have h_var_eq : config₂.varEnv = config₃.varEnv := by rw [h_eq_cfg]
              have h_next_eq : config₂.nextAddr = config₃.nextAddr := by rw [h_eq_cfg]
              have h_pure_eq : config₂.pureMode = config₃.pureMode := by rw [h_eq_cfg]
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, config₂, v₁, v₂, h_beval1, h_beval2, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
          | none =>
              simp [h_evalOp] at h_eq
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of sequence.
lemma bevalSeq_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        split at h_eq
        · next config₂' v₂ h_beval2 =>
          injection h_eq with h_eq_cfg h_eq_val
          subst h_eq_val h_eq_cfg
          simp only [Nat.add_sub_cancel]
          exact ⟨config₁, v₁, h_beval1, h_beval2⟩
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of vlet.
lemma bevalVlet_structure (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose =
      .success config_final v →
  ∃ (config₁ config₂ config₃ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    config₂ = { config₁ with varEnv := config₁.varEnv.update x v1 } ∧
    LeanPoison.beval (fuel - 1) config₂ e2 verbose =
        .success config₃ v ∧
    config_final = { config₃ with varEnv := config₁.varEnv } := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁' v₁ h_beval1 =>
        let config₂' := { config₁' with varEnv := config₁'.varEnv.update x v₁ }
        split at h_eq
        · next config₃' v₂ h_beval2 =>
          injection h_eq with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          simp only [Nat.add_sub_cancel]
          exact ⟨config₁', config₂', config₃', v₁, h_beval1, rfl, h_beval2, rfl⟩
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of newRef
lemma bevalNewRef_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (n : Int) (a : Address),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.num n) ∧
    a = config₁.nextAddr ∧
    config₂.memory = (config₁.memory.update a n) ∧
    config₂.nextAddr = config₁.nextAddr + 1 ∧
    config₂.varEnv = config₁.varEnv ∧
    config₂.pureMode = config₁.pureMode ∧
    v = Value.loc a := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- Only the success-num branch survives
    rename_i config' n h_beval1
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    refine ⟨config', n, config'.nextAddr, h_beval1, rfl, ?_⟩
    simp [freshAddr] at h_eq_cfg h_eq_val
    exact ⟨by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_val]⟩

-- Helper lemma: extract evaluation structure from successful beval of deref
lemma bevalDeref_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.deref e1) verbose =
      .success config₁ v →
  ∃ (config' : Config) (a : Address) (n : Int),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config' (Value.loc a) ∧
    config'.memory.lookup a = some n ∧
    v = Value.num n ∧
    config₁.memory = config'.memory ∧
    config₁.varEnv = config'.varEnv ∧
    config₁.nextAddr = config'.nextAddr ∧
    config₁.pureMode = config'.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- Only the success-loc branch survives; need to split on memory lookup
    rename_i config' a heq_beval
    split at h_eq <;> try simp at h_eq
    -- Only the some-n branch survives
    rename_i n h_mem_some
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    have h_lookup' : config'.memory.lookup a = some n := h_mem_some
    refine ⟨config', a, n, heq_beval, h_lookup', h_eq_val.symm, ?_, ?_, ?_, ?_⟩
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]

-- Helper lemma: extract evaluation structure from successful beval of assign
lemma bevalAssign_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose =
      .success config₂ v →
  ∃ (config₁ config₁' : Config) (a : Address) (n : Int),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.loc a) ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₁' (Value.num n) ∧
    v = Value.unit ∧
    config₂.memory = config₁'.memory.update a n ∧
    config₂.varEnv = config₁'.varEnv ∧
    config₂.nextAddr = config₁'.nextAddr ∧
    config₂.pureMode = config₁'.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- First split: e1 -> .success config₁ (Value.loc a); inner match on e2 remains
    rename_i config₁ a heq_beval1
    split at h_eq <;> try simp at h_eq
    -- Second split: e2 -> .success config₁' (Value.num n)
    rename_i config₁' n heq_beval2
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    refine ⟨config₁, config₁', a, n, heq_beval1, heq_beval2, h_eq_val.symm, ?_, ?_, ?_, ?_⟩
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]

-- Helper lemma: extract evaluation structure from successful beval of ite
lemma bevalIte_structure (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (b : Bool),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.bool b) ∧
    ((b = true ∧ LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v) ∨
     (b = false ∧ LeanPoison.beval (fuel - 1) config₁ e3 verbose =
        .success config₂ v)) := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    · -- true branch: first split gives e1 -> bool true; need split on e2
      rename_i config₁ heq_beval1
      split at h_eq <;> try simp at h_eq
      rename_i config₂' v₂ heq_beval2
      obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
      subst h_eq_cfg h_eq_val
      simp only [Nat.add_sub_cancel]
      exact ⟨config₁, true, heq_beval1, Or.inl ⟨rfl, heq_beval2⟩⟩
    · -- false branch: first split gives e1 -> bool false; need split on e3
      rename_i config₁ heq_beval1
      split at h_eq <;> try simp at h_eq
      rename_i config₂' v₃ heq_beval3
      obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
      subst h_eq_cfg h_eq_val
      simp only [Nat.add_sub_cancel]
      exact ⟨config₁, false, heq_beval1, Or.inr ⟨rfl, heq_beval3⟩⟩

-- Helper lemma: extract evaluation structure from successful beval of app
lemma bevalApp_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.app e1 e2) verbose =
      .success config_final v →
  ∃ (config₁ config₂ : Config) (v₂ : Value) (x : Name) (body : Expr) (env : VarEnv),
    LeanPoison.beval (fuel - 1) config₀ e2 verbose =
        .success config₁ v₂ ∧
    ((LeanPoison.beval (fuel - 1) config₁ e1 verbose =
          .success config₂ (Value.closure x body env) ∧
      config₂.pureMode = false ∧
      LeanPoison.bevalFunctionBody (fuel - 1) verbose config₂ env x v₂ body false =
          .success config_final v) ∨
     (LeanPoison.beval (fuel - 1) config₁ e1 verbose =
          .success config₂ (Value.peClosure x body env) ∧
     Expr.toPExpr? body ≠ none ∧
      LeanPoison.bevalFunctionBody (fuel - 1) verbose config₂ env x v₂ body true =
          .success config_final v)) ∧
    config_final.pureMode = config₂.pureMode := by
  intro h_eq
  -- Helper: bevalFunctionBody success preserves pureMode from currentConfig
  have hpureMode_of_body :
      ∀ fuel (currentConfig finalConfig : Config) (env : VarEnv) (x : Name) (argValue : Value)
        (body : Expr) (isPure : Bool),
        LeanPoison.bevalFunctionBody fuel verbose currentConfig env x argValue body isPure =
            .success finalConfig v →
        finalConfig.pureMode = currentConfig.pureMode := by
    intro fuel currentConfig finalConfig env x argValue body isPure hbeval
    cases fuel with
    | zero =>
        unfold LeanPoison.bevalFunctionBody at hbeval
        simp at hbeval
    | succ fuel' =>
        unfold LeanPoison.bevalFunctionBody at hbeval
        simp at hbeval
        split at hbeval
        · next evalConfig v_body h_beval_body =>
          split at hbeval
          · -- isPure = true
            injection hbeval with h_cfg_eq h_val_eq
            cases h_cfg_eq
            rfl
          · -- isPure = false
            injection hbeval with h_cfg_eq h_val_eq
            cases h_cfg_eq
            rfl
        · next h_oof =>
          simp at hbeval
        · next msg h_err =>
          simp at hbeval
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₂ h_beval2 =>
        split at h_eq
        · next config₂ x body env h_beval1 =>
          split at h_eq
          · next h_pureMode =>
            simp at h_eq
          · next h_notPureMode =>
            have hpure_mode_final :
                config_final.pureMode = config₂.pureMode :=
              hpureMode_of_body fuel' config₂ config_final env x v₂ body false h_eq
            have h_pureMode_false : config₂.pureMode = false := by
              cases h : config₂.pureMode with
              | true => exact absurd h h_notPureMode
              | false => rfl
            simp only [Nat.add_sub_cancel]
            exact ⟨config₁, config₂, v₂, x, body, env, h_beval2, Or.inl ⟨h_beval1, h_pureMode_false, h_eq⟩, hpure_mode_final⟩
        · next config₂ x body env h_beval1 =>
          cases h_pure : Expr.toPExpr? body with
          | none =>
              simp [h_pure] at h_eq
          | some _ =>
              simp [h_pure] at h_eq
              have hpure_mode_final :
                  config_final.pureMode = config₂.pureMode :=
                hpureMode_of_body fuel' config₂ config_final env x v₂ body true h_eq
              simp only [Nat.add_sub_cancel]
              refine ⟨config₁, config₂, v₂, x, body, env, h_beval2, Or.inr ⟨h_beval1, ?_, h_eq⟩, hpure_mode_final⟩
              simp [h_pure]
        · next v h_beval1 =>
          simp at h_eq
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- ================================================================
-- bevalFunctionBody_to_terminatesTo
-- ================================================================

-- Helper: Convert bevalFunctionBody success to terminatesTo for the body
lemma bevalFunctionBody_to_terminatesTo
    (fuel : Nat) (verbose : Bool) (currentConfig : Config) (closureEnv : VarEnv)
    (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool)
    (finalConfig : Config) (v : Value) :
    LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
        .success finalConfig v →
    ∃ (evalConfig : Config),
      terminatesTo body { currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } evalConfig v ∧
      finalConfig =
        (if isPure then
          { currentConfig with pureMode := currentConfig.pureMode }
        else
          { currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := currentConfig.pureMode }) := by
  intro hbeval_body
  cases fuel with
  | zero =>
    unfold LeanPoison.bevalFunctionBody at hbeval_body
    simp at hbeval_body
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at hbeval_body
    simp at hbeval_body
    split at hbeval_body
    · next evalConfig v_body h_beval_body =>
      cases h_isPure : isPure <;> simp [h_isPure] at hbeval_body h_beval_body
      · -- isPure = false
        obtain ⟨h_cfg, h_val⟩ := hbeval_body
        subst h_val
        use evalConfig
        refine ⟨⟨fuel', verbose, h_beval_body⟩, ?_⟩
        simpa [h_isPure] using h_cfg.symm
      · -- isPure = true
        obtain ⟨h_cfg, h_val⟩ := hbeval_body
        subst h_val
        use evalConfig
        refine ⟨⟨fuel', verbose, h_beval_body⟩, ?_⟩
        simpa [h_isPure] using h_cfg.symm
    · next h_oof =>
      simp at hbeval_body
    · next msg h_err =>
      simp at hbeval_body

-- ================================================================
-- terminatesTo inversion lemmas
-- ================================================================

private def isExternExpr : Expr → Prop
  | Expr.externVal _ _ _ => True
  | Expr.externFn _ _ _ _ => True
  | Expr.externPfn _ _ _ => True
  | _ => False

lemma terminatesTo_extern_false {e : Expr} {c₀ c₁ : Config} {o : Value} :
  isExternExpr e →
  terminatesTo e c₀ c₁ o → False := by
  intro hex ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  cases e with
  | externVal _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval
  | externFn _ _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval
  | externPfn _ _ _ =>
      cases fuel <;> simp [LeanPoison.beval] at hbeval
  | _ => cases hex

/-- Inversion lemma for terminatesTo on number literals. -/
lemma terminatesTo_num_inv' (n : Int) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.num n) c₀ c₁ v → c₁ = c₀ ∧ v = Value.num n := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on boolean literals. -/
lemma terminatesTo_bool_inv' (b : Bool) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.bool b) c₀ c₁ v → c₁ = c₀ ∧ v = Value.bool b := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on unit. -/
lemma terminatesTo_unit_inv' (c₀ c₁ : Config) (v : Value) :
    terminatesTo Expr.unit c₀ c₁ v → c₁ = c₀ ∧ v = Value.unit := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on string literals. -/
lemma terminatesTo_str_inv' (s : String) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.str s) c₀ c₁ v → c₁ = c₀ ∧ v = Value.str s := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Combined inversion lemma for terminatesTo on any literal expression. -/
lemma terminatesTo_literal_inv' (e : Expr) (v_expected : Value)
    (hval : Expr.toValue? e = some v_expected) (c₀ c₁ : Config) (v : Value) :
    terminatesTo e c₀ c₁ v → c₁ = c₀ ∧ v = v_expected := by
  intro ht
  cases e with
  | unit =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_unit_inv' c₀ c₁ v ht
  | num n =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_num_inv' n c₀ c₁ v ht
  | bool b =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_bool_inv' b c₀ c₁ v ht
  | str s =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_str_inv' s c₀ c₁ v ht
  | _ => simp [Expr.toValue?] at hval

/-- Inversion lemma for terminatesTo on variable lookup. -/
lemma terminatesTo_var_inv' (x : Name) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.var x) c₀ c₁ v →
    ∃ v', c₀.varEnv.lookup x = some v' ∧ c₁ = c₀ ∧ v = v' := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      cases hlookup : c₀.varEnv.lookup x with
      | none =>
          simp [hlookup] at hbeval
      | some v' =>
          simp [hlookup] at hbeval
          obtain ⟨hcfg, hval⟩ := hbeval
          exact ⟨v', rfl, hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on fn (regular function). -/
lemma terminatesTo_fn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.fn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.closure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on pfn (predicated function). -/
lemma terminatesTo_pfn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.pfn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.peClosure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on unaryop.
    Extracts the sub-expression evaluation and operation application. -/
lemma terminatesTo_unaryop_inv' (op : UnaryOp) (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.unaryop op e) c₀ c₁ v →
    ∃ c₁' v', terminatesTo e c₀ c₁' v' ∧
              LeanPoison.evalUnaryOp op v' = some v ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalUnaryOp_structure op e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', v', hbeval_e, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  exact ⟨cfg', v', ⟨fuel - 1, verbose, hbeval_e⟩, hevalOp, hmem.symm, hvar.symm, hnext.symm, hpure_mode.symm⟩

/-- Inversion lemma for terminatesTo on newRef.
    Extracts the sub-expression evaluation and allocation info. -/
lemma terminatesTo_newRef_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.newRef e) c₀ c₁ v →
    ∃ (c₁' : Config) (n : Int), terminatesTo e c₀ c₁' (Value.num n) ∧
              v = Value.loc c₁'.nextAddr ∧
              c₁.memory = c₁'.memory.insert c₁'.nextAddr n ∧
              c₁.nextAddr = c₁'.nextAddr + 1 ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalNewRef_structure e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', n, a, hbeval_e, ha_eq, hmem, hnext, hvar, hpure_mode, hv⟩
  refine ⟨cfg', n, ⟨fuel - 1, verbose, hbeval_e⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, ha_eq]
  · simp only [hmem, ha_eq, Memory.update]
  · exact hnext
  · exact hvar
  · exact hpure_mode

/-- Inversion lemma for terminatesTo on deref. -/
lemma terminatesTo_deref_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.deref e) c₀ c₁ v →
    ∃ (c₁' : Config) (a : Address) (n : Int), terminatesTo e c₀ c₁' (Value.loc a) ∧
              c₁'.memory.lookup a = some n ∧
              v = Value.num n ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalDeref_structure e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', a, n, hbeval_e, hlookup, hv, hmem, hvar, hnext, hpure⟩
  exact ⟨cfg', a, n, ⟨fuel - 1, verbose, hbeval_e⟩, hlookup, hv, hmem, hvar, hnext, hpure⟩

/-- Helper lemma: in evaluation, `pureMode` is preserved through evaluation.
    This holds for any expression. -/
lemma terminatesTo_preserves_pureMode (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo e c₀ c₁ v →
    c₁.pureMode = c₀.pureMode := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have hmain :
      ∀ fuel e c₀ c₁ v verbose,
        LeanPoison.beval fuel c₀ e verbose = .success c₁ v →
        c₁.pureMode = c₀.pureMode := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | _ fuel ih =>
      intro e c₀ c₁ v verbose hpure
      cases fuel with
      | zero =>
        unfold LeanPoison.beval at hpure
        simp at hpure
      | succ fuel' =>
        have ht : terminatesTo e c₀ c₁ v := ⟨fuel' + 1, verbose, hpure⟩
        cases e with
        | num n =>
          have h := terminatesTo_num_inv' n c₀ c₁ v ht
          rw [h.1]
        | bool b =>
          have h := terminatesTo_bool_inv' b c₀ c₁ v ht
          rw [h.1]
        | unit =>
          have h := terminatesTo_unit_inv' c₀ c₁ v ht
          rw [h.1]
        | str s =>
          have h := terminatesTo_str_inv' s c₀ c₁ v ht
          rw [h.1]
        | var x =>
          have h := terminatesTo_var_inv' x c₀ c₁ v ht
          rcases h with ⟨_, _, hcfg, _⟩
          rw [hcfg]
        | fn x paramType body returnType =>
          have h := terminatesTo_fn_inv' x paramType body returnType c₀ c₁ v ht
          rw [h.1]
        | pfn x paramType body returnType =>
          have h := terminatesTo_pfn_inv' x paramType body returnType c₀ c₁ v ht
          rw [h.1]
        | op e1 op e2 =>
          have hstruct := bevalOp_structure e1 e2 op (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, v1, v2, hbeval1, hbeval2, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ cfg₂ v2 verbose hbeval2
          rw [h_pure_eq.symm, hrec₂, hrec₁]
        | unaryop op e1 =>
          have hstruct := bevalUnaryOp_structure op e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, v1, hbeval1, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          rw [h_pure_eq.symm, hrec₁]
        | seq e1 e2 =>
          have hstruct := bevalSeq_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, v1, hbeval1, hbeval2⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ c₁ v verbose hbeval2
          rw [hrec₂, hrec₁]
        | vlet x e1 e2 =>
          have hstruct := bevalVlet_structure x e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by
            simp [hcfg2_eq]
          have hrec₂ := ih fuel' h_fuel e2 cfg₂ cfg₃ v verbose hbeval2
          rw [hcfg_final_eq]
          simp
          rw [hrec₂, h_pure_cfg2, hrec₁]
        | ite e1 e2 e3 =>
          have hstruct := bevalIte_structure e1 e2 e3 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, b, hbeval1, hbranch⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ (Value.bool b) verbose hbeval1
          cases hbranch with
          | inl htrue =>
            rcases htrue with ⟨_, hbeval2⟩
            have hrec₂ := ih fuel' h_fuel e2 cfg₁ c₁ v verbose hbeval2
            rw [hrec₂, hrec₁]
          | inr hfalse =>
            rcases hfalse with ⟨_, hbeval3⟩
            have hrec₃ := ih fuel' h_fuel e3 cfg₁ c₁ v verbose hbeval3
            rw [hrec₃, hrec₁]
        | newRef e1 =>
          have hstruct := bevalNewRef_structure e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, _, _, hbeval1, _, _, _, _, h_pure_eq, _⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          rw [h_pure_eq, hrec₁]
        | deref e1 =>
          have hstruct := bevalDeref_structure e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, _, _, hbeval1, _, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          rw [h_pure_eq, hrec₁]
        | assign e1 e2 =>
          have hstruct := bevalAssign_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₁', _, _, hbeval1, hbeval2, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ cfg₁' _ verbose hbeval2
          rw [h_pure_eq, hrec₂, hrec₁]
        | app e1 e2 =>
          have hstruct := bevalApp_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, v₂, x, body, env, hbeval_e2, h_app, h_pure_final⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec_e2 := ih fuel' h_fuel e2 c₀ cfg₁ v₂ verbose hbeval_e2
          rcases h_app with ⟨hbeval_e1, _, hbeval_body⟩ | ⟨hbeval_e1, _, hbeval_body⟩
          · have hrec_e1 := ih fuel' h_fuel e1 cfg₁ cfg₂ _ verbose hbeval_e1
            have h_pure_cfg2 : cfg₂.pureMode = c₀.pureMode := by
              rw [hrec_e1, hrec_e2]
            rw [h_pure_final, h_pure_cfg2]
          · have hrec_e1 := ih fuel' h_fuel e1 cfg₁ cfg₂ _ verbose hbeval_e1
            have h_pure_cfg2 : cfg₂.pureMode = c₀.pureMode := by
              rw [hrec_e1, hrec_e2]
            rw [h_pure_final, h_pure_cfg2]
        | externVal _ _ _ =>
          unfold LeanPoison.beval at hpure
          simp at hpure
        | externFn _ _ _ _ =>
          unfold LeanPoison.beval at hpure
          simp at hpure
        | externPfn _ _ _ =>
          unfold LeanPoison.beval at hpure
          simp at hpure
  exact hmain fuel e c₀ c₁ v verbose hbeval

-- ================================================================
-- Composite terminatesTo inversions
-- ================================================================

/-- Inversion lemma for terminatesTo on app (function application).
    The body terminates to some intermediate evalConfig (not c₂), because bevalFunctionBody
    transforms the config after body evaluation. -/
lemma terminatesTo_app_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.app e₁ e₂) c₀ c₂ v →
    -- Either the closure case holds...
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr) (env : VarEnv) (evalConfig : Config),
      terminatesTo e₂ c₀ c₂' v₂ ∧
      terminatesTo e₁ c₂' c₁ (Value.closure x body env) ∧
      c₁.pureMode = false ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := false } evalConfig v ∧
      c₂ = { c₁ with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := c₁.pureMode } ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode) ∨
    -- ...or the peClosure case holds
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr) (env : VarEnv) (evalConfig : Config),
      terminatesTo e₂ c₀ c₂' v₂ ∧
      terminatesTo e₁ c₂' c₁ (Value.peClosure x body env) ∧
      Expr.toPExpr? body ≠ none ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := true } evalConfig v ∧
      c₂ = c₁ ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode) := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalApp_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg2, cfg1, v2, x, body, env, hbeval_e2, h_app, hpure_mode_final⟩
  -- Convert e₂ evaluation to terminatesTo
  have hpure_cfg2 : cfg2.pureMode = c₀.pureMode :=
    terminatesTo_preserves_pureMode e₂ c₀ cfg2 v2 ⟨fuel - 1, verbose, hbeval_e2⟩
  -- Case split: closure vs peClosure
  rcases h_app with ⟨hbeval_e1, hpure_false, hbeval_body⟩ | ⟨hbeval_e1, htoPExpr, hbeval_body⟩
  · -- Case 1: Regular closure
    left
    have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
      terminatesTo_preserves_pureMode e₁ cfg2 cfg1 (Value.closure x body env) ⟨fuel - 1, verbose, hbeval_e1⟩
    obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
      bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body false c₂ v hbeval_body
    refine ⟨cfg2, v2, cfg1, x, body, env, evalConfig, ⟨fuel - 1, verbose, hbeval_e2⟩, ⟨fuel - 1, verbose, hbeval_e1⟩,
            hpure_false, hbody_terminates, (by simpa using hcfg_final), hpure_cfg2, ?_⟩
    rw [hpure_mode_final, hpure_cfg1, hpure_cfg2]
  · -- Case 2: Pure closure (peClosure)
    right
    have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
      terminatesTo_preserves_pureMode e₁ cfg2 cfg1 (Value.peClosure x body env) ⟨fuel - 1, verbose, hbeval_e1⟩
    obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
      bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body true c₂ v hbeval_body
    refine ⟨cfg2, v2, cfg1, x, body, env, evalConfig, ⟨fuel - 1, verbose, hbeval_e2⟩, ⟨fuel - 1, verbose, hbeval_e1⟩,
            htoPExpr, hbody_terminates, (by simpa using hcfg_final), hpure_cfg2, ?_⟩
    rw [hpure_mode_final, hpure_cfg1, hpure_cfg2]

/-- Inversion lemma for terminatesTo on ite (if-then-else).
    Returns intermediate config after condition, which branch was taken, and preserves pureMode. -/
lemma terminatesTo_ite_inv' (e₁ e₂ e₃ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.ite e₁ e₂ e₃) c₀ c₂ v →
    ∃ (c₁ : Config) (b : Bool),
              terminatesTo e₁ c₀ c₁ (Value.bool b) ∧
              ((b = true ∧ terminatesTo e₂ c₁ c₂ v) ∨
               (b = false ∧ terminatesTo e₃ c₁ c₂ v)) ∧
              c₁.pureMode = c₀.pureMode ∧
              c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalIte_structure e₁ e₂ e₃ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, b, hbeval_e1, hbranch⟩
  have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ (Value.bool b) ⟨fuel - 1, verbose, hbeval_e1⟩
  cases hbranch with
  | inl htrue =>
    rcases htrue with ⟨hb, hbeval_e2⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e2⟩
    refine ⟨cfg₁, b, ⟨fuel - 1, verbose, hbeval_e1⟩, Or.inl ⟨hb, ⟨fuel - 1, verbose, hbeval_e2⟩⟩, hrec₁, ?_⟩
    rw [hrec₂, hrec₁]
  | inr hfalse =>
    rcases hfalse with ⟨hb, hbeval_e3⟩
    have hrec₃ := terminatesTo_preserves_pureMode e₃ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e3⟩
    refine ⟨cfg₁, b, ⟨fuel - 1, verbose, hbeval_e1⟩, Or.inr ⟨hb, ⟨fuel - 1, verbose, hbeval_e3⟩⟩, hrec₁, ?_⟩
    rw [hrec₃, hrec₁]

/-- Inversion lemma for terminatesTo on binary op. -/
lemma terminatesTo_op_inv' (e₁ : Expr) (op : Op) (e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.op e₁ op e₂) c₀ c₂ v →
    ∃ c₁ v₁ v₂, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ c₁ c₂ v₂ ∧
                LeanPoison.evalOp op v₁ v₂ = some v ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalOp_structure e₁ e₂ op fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₂, v₁, v₂, hbeval_e1, hbeval_e2, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  have hbeval_e2' : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = .success c₂ v₂ := by
    have h_cfg2_eq : cfg₂ = c₂ := by
      cases cfg₂; cases c₂; simp only [Config.mk.injEq]; exact ⟨hmem, hvar, hnext, hpure_mode⟩
    rw [← h_cfg2_eq]; exact hbeval_e2
  refine ⟨cfg₁, v₁, v₂, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2'⟩, hevalOp, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v₂ ⟨fuel - 1, verbose, hbeval_e2'⟩
    rw [hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on seq. -/
lemma terminatesTo_seq_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.seq e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁, terminatesTo e₁ c₀ c₁ v₁ ∧
             terminatesTo e₂ c₁ c₂ v ∧
             c₁.pureMode = c₀.pureMode ∧
             c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalSeq_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, v₁, hbeval_e1, hbeval_e2⟩
  refine ⟨cfg₁, v₁, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2⟩, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e2⟩
    rw [hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on vlet. -/
lemma terminatesTo_vlet_inv' (x : Name) (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.vlet x e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁ c₃, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ { c₁ with varEnv := c₁.varEnv.update x v₁ } c₃ v ∧
                c₂ = { c₃ with varEnv := c₁.varEnv } ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalVlet_structure x e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v₁, hbeval_e1, hcfg2_eq, hbeval_e2, hcfg_final⟩
  have hpure_e2' : LeanPoison.beval (fuel - 1) { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ } e₂ verbose =
      .success cfg₃ v := by rw [← hcfg2_eq]; exact hbeval_e2
  refine ⟨cfg₁, v₁, cfg₃, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hpure_e2'⟩, hcfg_final, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₂ cfg₃ v ⟨fuel - 1, verbose, hbeval_e2⟩
    have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by rw [hcfg2_eq]
    rw [hcfg_final]; simp; rw [hrec₂, h_pure_cfg2, hrec₁]

/-- Inversion lemma for terminatesTo on assign. -/
lemma terminatesTo_assign_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.assign e₁ e₂) c₀ c₂ v →
    ∃ (c₁ c₁' : Config) (a : Address) (n : Int),
                           terminatesTo e₁ c₀ c₁ (Value.loc a) ∧
                           terminatesTo e₂ c₁ c₁' (Value.num n) ∧
                           v = Value.unit ∧
                           c₂.memory = c₁'.memory.insert a n ∧
                           c₂.varEnv = c₁'.varEnv ∧
                           c₂.nextAddr = c₁'.nextAddr ∧
                           c₂.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalAssign_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₁', a, n, hbeval_e1, hbeval_e2, hv, hmem, hvar, hnext, hpure_mode⟩
  refine ⟨cfg₁, cfg₁', a, n, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2⟩, hv, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; rfl  -- .update = .insert for ExtTreeMap
  · exact hvar
  · exact hnext
  · exact hpure_mode

-- ================================================================
-- NextAddr Monotonicity
-- ================================================================

section nextAddr_monotonic

/-- Helper lemma: bevalFunctionBody preserves monotonicity of nextAddr. -/
private lemma bevalFunctionBody_nextAddr_mono
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = .success config₁ v →
      config₀.nextAddr ≤ config₁.nextAddr) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
      .success finalConfig v →
  currentConfig.nextAddr ≤ finalConfig.nextAddr := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp at h_eq
      split at h_eq
      · next evalConfig v_body h_beval_body =>
        split at h_eq
        · -- isPure = true
          injection h_eq with h_cfg_eq h_val_eq
          cases h_cfg_eq
          simp
        · -- isPure = false
          injection h_eq with h_cfg_eq h_val_eq
          have h_next_eq : finalConfig.nextAddr = evalConfig.nextAddr := by
            cases h_cfg_eq
            rfl
          have h_bodyConfig_next : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).nextAddr = currentConfig.nextAddr := rfl
          have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body
          have IH_body' : currentConfig.nextAddr ≤ evalConfig.nextAddr := by
            simpa [h_bodyConfig_next] using IH_body
          simp [h_next_eq]
          exact IH_body'
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

private lemma beval_nextAddr_mono : ∀ (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  LeanPoison.beval fuel config₀ e verbose = .success config₁ v →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro e fuel verbose config₀ config₁ v h_eval
  revert e verbose config₀ config₁ v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e verbose config₀ config₁ v h_eval
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = .success config₁ v →
      config₀.nextAddr ≤ config₁.nextAddr := by
      intro m h_lt e' config₀' config₁' v' h_eval'
      exact IH m h_lt e' verbose config₀' config₁' v' h_eval'
    cases e with
    | externVal typ poison pred =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
    | externFn arg argTyp retSpec effects =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
    | externPfn arg argTyp retSpec =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
    | num n | bool b | unit | str s =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            obtain ⟨h_eq_config, _⟩ := h_eval
            subst h_eq_config
            exact le_rfl
    | var x =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            cases h_lookup : config₀.varEnv.lookup x with
            | some v_lookup =>
                simp [h_lookup] at h_eval
                obtain ⟨h_eq_config, _⟩ := h_eval
                subst h_eq_config
                exact le_rfl
            | none =>
                simp [h_lookup] at h_eval
    | fn x paramType body returnType | pfn x paramType body returnType =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            obtain ⟨h_eq_config, _⟩ := h_eval
            subst h_eq_config
            exact le_rfl
    | op e1 op e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, hbeval1, hbeval2, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 :=
              IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 :=
              IH_converted fuel' h_fuel e2 cfg₁1 cfg₁2 v2 hbeval2
            have hle02 : config₀.nextAddr ≤ cfg₁2.nextAddr := Nat.le_trans hle1 hle2
            simpa [h_next] using hle02
    | unaryop op e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | ite e1 e2 e3 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalIte_structure e1 e2 e3 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, b, hbeval1, hbranch⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            cases hbranch with
            | inl htrue =>
              rcases htrue with ⟨_, hbeval2⟩
              have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.bool b) hbeval1
              have hle2 := IH_converted fuel' h_fuel e2 cfg₁ config₁ v hbeval2
              exact Nat.le_trans hle1 hle2
            | inr hfalse =>
              rcases hfalse with ⟨_, hbeval3⟩
              have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.bool b) hbeval1
              have hle3 := IH_converted fuel' h_fuel e3 cfg₁ config₁ v hbeval3
              exact Nat.le_trans hle1 hle3
    | newRef e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalNewRef_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, n, a, hbeval1, _ha, _hmem, h_next, _hvar, _hval⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 (Value.num n) hbeval1
            have hle1' : config₀.nextAddr ≤ cfg₁1.nextAddr + 1 :=
              Nat.le_trans hle1 (Nat.le_succ _)
            simpa [h_next] using hle1'
    | assign e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalAssign_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, cfg₁', a, n, hbeval1, hbeval2, _, _, _, hnext, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.loc a) hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁ cfg₁' (Value.num n) hbeval2
            have hle02 : config₀.nextAddr ≤ cfg₁'.nextAddr := Nat.le_trans hle1 hle2
            simpa [hnext] using hle02
    | deref e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalDeref_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, a, n, hbeval1, _, _, hmem, hvar, hnext, hpure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 (Value.loc a) hbeval1
            -- config₁ = cfg₁1 since all fields match
            have : config₁.nextAddr = cfg₁1.nextAddr := hnext
            simpa [this] using hle1
    | seq e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalSeq_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁1 config₁ v hbeval2
            exact Nat.le_trans hle1 hle2
    | vlet x e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, cfg₁2, cfg₁3, v1, hbeval1, hcfg2, hbeval2, hcfg_final⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁2 cfg₁3 v hbeval2
            have h_next_eq1 : cfg₁2.nextAddr = cfg₁1.nextAddr := by
              simp [hcfg2]
            have h_next_eq2 : config₁.nextAddr = cfg₁3.nextAddr := by
              simp [hcfg_final]
            have hle01 : config₀.nextAddr ≤ cfg₁2.nextAddr := by
              simpa [h_next_eq1] using hle1
            have hle03 : config₀.nextAddr ≤ cfg₁3.nextAddr := Nat.le_trans hle01 hle2
            simpa [h_next_eq2] using hle03
    | app e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalApp_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, cfg₂, v₂, x, body, env, hbeval_e2, h_app, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
              LeanPoison.beval m config₀ e verbose = .success config₁ v →
              config₀.nextAddr ≤ config₁.nextAddr := by
              intro m h_m_lt e config₀ config₁ v h_beval_ex
              have h_m_lt_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt (Nat.le_succ fuel')
              exact IH m h_m_lt_succ e verbose config₀ config₁ v h_beval_ex
            have hle_e2 := IH_converted fuel' h_fuel e2 config₀ cfg₁ v₂ hbeval_e2
            rcases h_app with ⟨hbeval_e1, _, hbeval_body⟩ | ⟨hbeval_e1, _, hbeval_body⟩
            · have hle_e1 := IH_converted fuel' h_fuel e1 cfg₁ cfg₂ (Value.closure x body env) hbeval_e1
              have hle_body :=
                bevalFunctionBody_nextAddr_mono fuel' verbose cfg₂ config₁ env x v₂ body false v IH_fuel' hbeval_body
              exact Nat.le_trans hle_e2 (Nat.le_trans hle_e1 hle_body)
            · have hle_e1 := IH_converted fuel' h_fuel e1 cfg₁ cfg₂ (Value.peClosure x body env) hbeval_e1
              have hle_body :=
                bevalFunctionBody_nextAddr_mono fuel' verbose cfg₂ config₁ env x v₂ body true v IH_fuel' hbeval_body
              exact Nat.le_trans hle_e2 (Nat.le_trans hle_e1 hle_body)

/-- Next address is monotone for terminating evaluations. -/
lemma terminatesTo_nextAddr_mono (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v → cfg₀.nextAddr ≤ cfg₁.nextAddr := by
  intro ⟨fuel, verbose, hbeval⟩
  exact beval_nextAddr_mono e fuel verbose cfg₀ cfg₁ v hbeval

end nextAddr_monotonic

-- ================================================================
-- Pure evaluation preserves config (used for pure closures)
-- ================================================================

/-- If a pure expression evaluates successfully in pureMode, it does not change nextAddr/memory. -/
private lemma beval_pure_config_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.nextAddr = cfg₀.nextAddr ∧ cfg₁.pureMode = true ∧ cfg₁.memory = cfg₀.memory := by
  revert e cfg₀ cfg₁ v verbose pe
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval
    cases fuel with
    | zero =>
        unfold LeanPoison.beval at hbeval
        simp at hbeval
    | succ fuel' =>
        cases e with
        | unit | str _ | num _ | bool _ =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            obtain ⟨h_cfg_eq, _⟩ := hbeval
            subst h_cfg_eq
            exact ⟨rfl, h_pm, rfl⟩
        | var x =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            cases h_lookup : cfg₀.varEnv.lookup x with
            | some v' =>
                simp [h_lookup] at hbeval
                obtain ⟨h_cfg_eq, _⟩ := hbeval
                subst h_cfg_eq
                exact ⟨rfl, h_pm, rfl⟩
            | none =>
                simp [h_lookup] at hbeval
        | op e1 op e2 =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, hbeval1', hbeval2', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1'
                    have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₁2 v2 verbose pe2 h_pe2 h1.2.1 hbeval2'
                    refine ⟨?_, ?_, ?_⟩
                    · calc cfg₁.nextAddr = cfg₁2.nextAddr := h_next.symm
                        _ = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · calc cfg₁.pureMode = cfg₁2.pureMode := h_pure_eq.symm
                        _ = true := h2.2.1
                    · calc cfg₁.memory = cfg₁2.memory := _h_mem.symm
                        _ = cfg₁1.memory := h2.2.2
                        _ = cfg₀.memory := h1.2.2
        | unaryop op e1 =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                subst h_pure
                have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1'
                refine ⟨?_, ?_, ?_⟩
                · calc cfg₁.nextAddr = cfg₁1.nextAddr := h_next.symm
                    _ = cfg₀.nextAddr := h1.1
                · calc cfg₁.pureMode = cfg₁1.pureMode := h_pure_eq.symm
                    _ = true := h1.2.1
                · calc cfg₁.memory = cfg₁1.memory := _h_mem.symm
                    _ = cfg₀.memory := h1.2.2
        | ite e1 e2 e3 =>
            have hstruct :=
              bevalIte_structure e1 e2 e3 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, b, hbeval1, hbranch⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    cases h_pe3 : Expr.toPExpr? e3 with
                    | none => simp [h_pe3] at h_pure
                    | some pe3 =>
                        simp [h_pe3] at h_pure
                        subst h_pure
                        have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 (Value.bool b) verbose pe1 h_pe1 h_pm hbeval1
                        cases hbranch with
                        | inl htrue =>
                          rcases htrue with ⟨_, hbeval2⟩
                          have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₁ v verbose pe2 h_pe2 h1.2.1 hbeval2
                          refine ⟨?_, ?_, ?_⟩
                          · calc cfg₁.nextAddr = cfg₁1.nextAddr := h2.1
                              _ = cfg₀.nextAddr := h1.1
                          · exact h2.2.1
                          · calc cfg₁.memory = cfg₁1.memory := h2.2.2
                              _ = cfg₀.memory := h1.2.2
                        | inr hfalse =>
                          rcases hfalse with ⟨_, hbeval3⟩
                          have h3 := IH fuel' h_fuel e3 cfg₁1 cfg₁ v verbose pe3 h_pe3 h1.2.1 hbeval3
                          refine ⟨?_, ?_, ?_⟩
                          · calc cfg₁.nextAddr = cfg₁1.nextAddr := h3.1
                              _ = cfg₀.nextAddr := h1.1
                          · exact h3.2.1
                          · calc cfg₁.memory = cfg₁1.memory := h3.2.2
                              _ = cfg₀.memory := h1.2.2
        | deref e1 =>
            have hstruct :=
              bevalDeref_structure e1 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, _, _, hbeval1, _, _, hmem, hvar, hnext, hpure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                subst h_pure
                have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 _ verbose pe1 h_pe1 h_pm hbeval1
                refine ⟨?_, ?_, ?_⟩
                · calc cfg₁.nextAddr = cfg₁1.nextAddr := hnext
                    _ = cfg₀.nextAddr := h1.1
                · calc cfg₁.pureMode = cfg₁1.pureMode := hpure_eq
                    _ = true := h1.2.1
                · calc cfg₁.memory = cfg₁1.memory := hmem
                    _ = cfg₀.memory := h1.2.2
        | vlet x e1 e2 =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1
                    have h_pm2 : cfg₂.pureMode = true := by
                      simpa [hcfg2_eq] using h1.2.1
                    have h2 := IH fuel' h_fuel e2 cfg₂ cfg₃ v verbose pe2 h_pe2 h_pm2 hbeval2
                    subst hcfg2_eq hcfg_final_eq
                    refine ⟨?_, ?_, ?_⟩
                    · calc cfg₃.nextAddr = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · simpa using h2.2.1
                    · calc cfg₃.memory = cfg₁1.memory := h2.2.2
                        _ = cfg₀.memory := h1.2.2
        | app e1 e2 =>
            have hstruct :=
              bevalApp_structure e1 e2 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁', cfg₂, v₂, x, body, env, hbeval_e2, h_app, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h2 := IH fuel' h_fuel e2 cfg₀ cfg₁' v₂ verbose pe2 h_pe2 h_pm hbeval_e2
                    rcases h_app with ⟨hbeval_e1, _, _⟩ | ⟨hbeval_e1, _, hbeval_body⟩
                    · -- Closure case: pureMode = false, but we showed it should be true
                      have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.closure x body env) verbose pe1 h_pe1 h2.2.1 hbeval_e1
                      -- h1.2.1 says cfg₂.pureMode = true, but h_app says cfg₂.pureMode = false
                      simp_all
                    · -- peClosure case
                      have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.peClosure x body env) verbose pe1 h_pe1 h2.2.1 hbeval_e1
                      -- bevalFunctionBody with isPure = true, body is pure
                      obtain ⟨evalConfig, hbody_term, hcfg_final⟩ :=
                        bevalFunctionBody_to_terminatesTo (fuel' ) verbose cfg₂ env x v₂ body true cfg₁ v hbeval_body
                      simp at hcfg_final
                      -- hcfg_final : cfg₁ = cfg₂ (since { cfg₂ with pureMode := cfg₂.pureMode } = cfg₂)
                      refine ⟨?_, ?_, ?_⟩
                      · calc cfg₁.nextAddr = cfg₂.nextAddr := by rw [hcfg_final]
                          _ = cfg₁'.nextAddr := h1.1
                          _ = cfg₀.nextAddr := h2.1
                      · rw [hcfg_final]; exact h1.2.1
                      · calc cfg₁.memory = cfg₂.memory := by rw [hcfg_final]
                          _ = cfg₁'.memory := h1.2.2
                          _ = cfg₀.memory := h2.2.2
        -- impossible cases: not allowed by pexpr syntax
        | newRef _ | assign _ _ | seq _ _ | fn _ _ _ _ | pfn _ _ _ _
        | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            simp [Expr.toPExpr?] at h_pure

private lemma beval_pure_nextAddr_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.nextAddr = cfg₀.nextAddr := by
  intro h_pure h_pm hbeval
  exact (beval_pure_config_eq e fuel cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval).1

lemma beval_pure_memory_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.memory = cfg₀.memory := by
  intro h_pure h_pm hbeval
  exact (beval_pure_config_eq e fuel cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval).2.2

-- ================================================================
-- wfConfig_preserved Proof
-- ================================================================

section wfConfig_preserved_proof

-- Private lemmas for wfConfig_preserved proof

/-- evalUnaryOp preserves well-formedness of values. -/
private lemma evalUnaryOp_preserves_wfValue (next : Address) (op : UnaryOp) (v1 v : Value) :
    wfValue next v1 →
    LeanPoison.evalUnaryOp op v1 = some v →
    wfValue next v := by
  intro h_wf_v1 h_eval
  cases op with
  | not =>
      simp [LeanPoison.evalUnaryOp] at h_eval
      cases h_wf_v1 with
      | bool b =>
          injection h_eval with h_eq
          subst h_eq
          exact wfValue.bool (!b)
      | num _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
          cases h_eval

/-- evalOp preserves well-formedness of values. -/
private lemma evalOp_preserves_wfValue (next : Address) (op : Op) (v1 v2 v : Value) :
    LeanPoison.evalOp op v1 v2 = some v →
    wfValue next v := by
  intro h_eval
  cases op <;> cases v1 <;> cases v2 <;>
    simp [LeanPoison.evalOp] at h_eval
  all_goals
    cases h_eval
    first
    | exact wfValue.num _
    | exact wfValue.bool _

/-- If a value is found via lookup in a well-formed varEnv, then it's well-formed. -/
private lemma wfVarEnv_lookup (next : Address) (env : VarEnv) (x : Name) (v : Value) :
    wfVarEnv next env →
    env.lookup x = some v →
    wfValue next v := by
  intro h_wf_env h_lookup
  induction env with
  | nil =>
      simp [VarEnv.lookup, List.lookup] at h_lookup
  | cons head tail ih =>
      cases head with
      | mk x' v' =>
          cases h_wf_env with
          | cons x'_wf v'_wf env'_wf h_wf_v' h_wf_tail =>
              simp [VarEnv.lookup, List.lookup] at h_lookup
              by_cases h_eq : x == x'
              · simp [h_eq] at h_lookup
                subst h_lookup
                exact h_wf_v'
              · simp [h_eq] at h_lookup
                exact ih h_wf_tail h_lookup

/-- Updating a well-formed varEnv with a well-formed value preserves well-formedness. -/
private lemma wfVarEnv_update (next : Address) (env : VarEnv) (x : Name) (v : Value) :
    wfVarEnv next env →
    wfValue next v →
    wfVarEnv next (VarEnv.update env x v) := by
  intro hwf_env hwf_v
  exact wfVarEnv.cons x v env hwf_v hwf_env

-- Monotonicity of well-formedness: larger bounds preserve wfValue/wfVarEnv.
mutual
  private lemma wfValue_mono {n m : Address} (h : n ≤ m) :
      ∀ v, wfValue n v → wfValue m v := by
    intro v hv
    cases hv with
    | num n => exact wfValue.num n
    | bool b => exact wfValue.bool b
    | unit => exact wfValue.unit
    | str s => exact wfValue.str s
    | loc hlt =>
        exact wfValue.loc (Nat.lt_of_lt_of_le hlt h)
    | closure x e env hwf =>
        exact wfValue.closure x e env (wfVarEnv_mono h env hwf)
    | peClosure x e env hwf =>
        exact wfValue.peClosure x e env (wfVarEnv_mono h env hwf)

  private lemma wfVarEnv_mono {n m : Address} (h : n ≤ m) :
      ∀ env, wfVarEnv n env → wfVarEnv m env := by
    intro env hwf
    cases hwf with
    | nil => exact wfVarEnv.nil
    | cons x v env hv hwf_tail =>
        exact wfVarEnv.cons x v env (wfValue_mono h v hv) (wfVarEnv_mono h env hwf_tail)
end

/-- If wfConfig holds and nextAddr only increases (with same memory/varEnv structure),
    then wfConfig is preserved. Useful for configs where only nextAddr changed. -/
lemma wfConfig_mono (cfg₀ : Config) (n' : Address) :
    wfConfig cfg₀ →
    cfg₀.nextAddr ≤ n' →
    wfConfig { cfg₀ with nextAddr := n' } := by
  intro ⟨hmem, henv⟩ hle
  constructor
  · intro a ha
    exact Nat.lt_of_lt_of_le (hmem a ha) hle
  · exact wfVarEnv_mono hle cfg₀.varEnv henv

/-- Evaluation preserves config well-formedness. -/
lemma wfConfig_preserved (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  intro hterm hwf₀
  rcases hterm with ⟨fuel, verbose, hbeval⟩
  revert e cfg₀ cfg₁ v hwf₀ verbose hbeval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro e cfg₀ cfg₁ v hwf₀ verbose hbeval
      cases fuel with
      | zero =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
      | succ fuel =>
          have ih :
              ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
                wfConfig cfg₀' →
                LeanPoison.beval fuel cfg₀' e verbose = .success cfg₁' v' →
                wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v' := by
            intro e cfg₀' cfg₁' v' hwf₀' hbeval'
            have hlt : fuel < fuel.succ := Nat.lt_succ_self fuel
            exact IH fuel hlt e cfg₀' cfg₁' v' hwf₀' verbose hbeval'
          cases e with
      -- Literals
      | num n =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.num n⟩
      | bool b =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.bool b⟩
      | unit =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.unit⟩
      | str s =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.str s⟩
      -- Variables
      | var x =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          cases h_lookup : cfg₀.varEnv.lookup x with
          | some v_lookup =>
              simp [h_lookup] at hbeval
              obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
              subst h_eq_cfg
              subst h_eq_val
              exact ⟨hwf₀, wfVarEnv_lookup cfg₀.nextAddr cfg₀.varEnv x v_lookup hwf₀.2 h_lookup⟩
          | none =>
              simp [h_lookup] at hbeval
      -- Function abstractions
      | fn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.closure x body cfg₀.varEnv hwf₀.2⟩
      | pfn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.peClosure x body cfg₀.varEnv hwf₀.2⟩
      -- Binary operations
      | op e1 op e2 =>
          have hstruct :=
            bevalOp_structure e1 e2 op (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with
            ⟨cfg₁1, cfg₁2, v1, v2, hbeval1', hbeval2', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1'
          have hih2 := ih e2 cfg₁1 cfg₁2 v2 hih1.1 hbeval2'
          constructor
          · rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro a hcontains
              have hcontains2 : cfg₁2.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem2 a hcontains2
              simpa [h_next] using hlt
            · simpa [h_var, h_next] using hwfenv2
          · exact evalOp_preserves_wfValue cfg₁.nextAddr op v1 v2 v h_evalOp
      -- Unary operations
      | unaryop op e1 =>
          have hstruct :=
            bevalUnaryOp_structure op e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, v1, hbeval1', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1'
          constructor
          · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro a hcontains
              have hcontains1 : cfg₁1.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem1 a hcontains1
              simpa [h_next] using hlt
            · simpa [h_var, h_next] using hwfenv1
          · exact evalUnaryOp_preserves_wfValue cfg₁.nextAddr op v1 v (by simpa [h_next] using hih1.2) h_evalOp
      -- If-then-else
      | ite e1 e2 e3 =>
          have hstruct :=
            bevalIte_structure e1 e2 e3 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, b, hbeval1, hbranch⟩
          have hih1 := ih e1 cfg₀ cfg₁1 (Value.bool b) hwf₀ hbeval1
          cases hbranch with
          | inl htrue =>
            rcases htrue with ⟨_, hbeval2⟩
            exact ih e2 cfg₁1 cfg₁ v hih1.1 hbeval2
          | inr hfalse =>
            rcases hfalse with ⟨_, hbeval3⟩
            exact ih e3 cfg₁1 cfg₁ v hih1.1 hbeval3
      -- New reference
      | newRef e1 =>
          have hstruct :=
            bevalNewRef_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, n, a, hbeval1, ha, hmem_eq, hnext_eq, hvar_eq, _hpure_eq, hval_eq⟩
          have hih1 := ih e1 cfg₀ cfg₁1 (Value.num n) hwf₀ hbeval1
          constructor
          · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro addr hcontains
              have hcontains' : (cfg₁1.memory.update a n).contains addr := by
                simp [hmem_eq] at hcontains
                exact hcontains
              by_cases h_eq : addr = a
              · subst h_eq
                simp [ha, hnext_eq]
              · have hcmp : compare a addr ≠ Ordering.eq := by
                  intro hcmp
                  have h_eq' : a = addr := LawfulEqCmp.eq_of_compare hcmp
                  exact h_eq h_eq'.symm
                have hcontains1 : cfg₁1.memory.contains addr := by
                  simpa [Memory.update] using
                    (ExtTreeMap.contains_of_contains_insert (t := cfg₁1.memory) (k := a) (a := addr) (v := n) hcontains' hcmp)
                have hlt := hwfmem1 addr hcontains1
                have hlt' : addr < cfg₁1.nextAddr + 1 :=
                  Nat.lt_trans hlt (Nat.lt_succ_self _)
                simp [hnext_eq]
                exact hlt'
            · have hle : cfg₁1.nextAddr ≤ cfg₁.nextAddr := by
                simp [hnext_eq]
              have hwfenv1' : wfVarEnv cfg₁.nextAddr cfg₁1.varEnv :=
                wfVarEnv_mono hle cfg₁1.varEnv hwfenv1
              simp [hvar_eq]
              exact hwfenv1'
          · have hlt : a < cfg₁.nextAddr := by
              simp [ha, hnext_eq]
            simpa [hval_eq] using (wfValue.loc hlt)
      -- Assign
      | assign e1 e2 =>
          have hstruct :=
            bevalAssign_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfgA, cfgB, a, n, hbeval1, hbeval2, hv, hmem, hvar, hnext, hpure⟩
          have hih1 := ih e1 cfg₀ cfgA (Value.loc a) hwf₀ hbeval1
          have hih2 := ih e2 cfgA cfgB (Value.num n) hih1.1 hbeval2
          have hloc_lt : a < cfgA.nextAddr := by
            cases hih1.2 with
            | loc hlt => exact hlt
          have hle_next : cfgA.nextAddr ≤ cfgB.nextAddr :=
            terminatesTo_nextAddr_mono e2 cfgA cfgB (Value.num n) ⟨fuel, verbose, hbeval2⟩
          have hloc_lt' : a < cfgB.nextAddr :=
            Nat.lt_of_lt_of_le hloc_lt hle_next
          constructor
          · rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro addr hcontains
              -- cfg₁.memory = cfgB.memory.update a n (from hmem)
              have hcontains' : (cfgB.memory.update a n).contains addr := by
                rwa [← hmem]
              by_cases h_eq : addr = a
              · subst h_eq
                simpa [hnext] using hloc_lt'
              · have hcmp : compare a addr ≠ Ordering.eq := by
                  intro hcmp
                  have h_eq' : a = addr := LawfulEqCmp.eq_of_compare hcmp
                  exact h_eq h_eq'.symm
                have hcontains_old : cfgB.memory.contains addr := by
                  simpa [Memory.update] using
                    (ExtTreeMap.contains_of_contains_insert (t := cfgB.memory) (k := a) (a := addr) (v := n) hcontains' hcmp)
                have hlt := hwfmem2 addr hcontains_old
                simpa [hnext] using hlt
            · simpa [hvar, hnext] using hwfenv2
          · subst hv
            exact wfValue.unit
      -- Deref
      | deref e1 =>
          have hstruct :=
            bevalDeref_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨config', a, n, hbeval1, _, hv, hmem, hvar, hnext, hpure⟩
          have hih1 := ih e1 cfg₀ config' (Value.loc a) hwf₀ hbeval1
          constructor
          · -- cfg₁ has same fields as config'
            rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro addr hcontains
              have : config'.memory.contains addr := by simpa [hmem] using hcontains
              have hlt := hwfmem1 addr this
              simpa [hnext] using hlt
            · simpa [hvar, hnext] using hwfenv1
          · subst hv
            exact wfValue.num n
      -- Sequence
      | seq e1 e2 =>
          have hstruct :=
            bevalSeq_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1
          exact ih e2 cfg₁1 cfg₁ v hih1.1 hbeval2
      -- Let binding
      | vlet x e1 e2 =>
          have hstruct :=
            bevalVlet_structure x e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1
          have hwf_cfg2 : wfConfig cfg₂ := by
            rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            have hwfenv2 : wfVarEnv cfg₁1.nextAddr (cfg₁1.varEnv.update x v1) :=
              wfVarEnv_update cfg₁1.nextAddr cfg₁1.varEnv x v1 hwfenv1 hih1.2
            subst hcfg2_eq
            exact ⟨hwfmem1, hwfenv2⟩
          have hih2 := ih e2 cfg₂ cfg₃ v hwf_cfg2 hbeval2
          have hle_next : cfg₁1.nextAddr ≤ cfg₃.nextAddr := by
            have hle := terminatesTo_nextAddr_mono e2 cfg₂ cfg₃ v ⟨fuel, verbose, hbeval2⟩
            simpa [hcfg2_eq] using hle
          have hwfenv1_lift : wfVarEnv cfg₃.nextAddr cfg₁1.varEnv :=
            wfVarEnv_mono hle_next cfg₁1.varEnv hih1.1.2
          subst hcfg_final_eq
          constructor
          · rcases hih2.1 with ⟨hwfmem3, _⟩
            exact ⟨by simpa using hwfmem3, by simpa using hwfenv1_lift⟩
          · simpa using hih2.2
      -- Application
      | app e1 e2 =>
          have ih_strong :
              ∀ (m : Nat), m < fuel.succ →
                ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
                  wfConfig cfg₀' →
                  LeanPoison.beval m cfg₀' e verbose = .success cfg₁' v' →
                  wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v' := by
            intro m hlt e cfg₀' cfg₁' v' hwf₀' hbeval'
            exact IH m hlt e cfg₀' cfg₁' v' hwf₀' verbose hbeval'
          -- Extract structure
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          split at hbeval
          · next cfg₁' v₂ h_beval2 =>
            have hih2 :=
              ih_strong fuel (Nat.lt_succ_self fuel) e2 cfg₀ cfg₁' v₂ hwf₀ h_beval2
            split at hbeval
            · next cfg₂ x body env h_beval1 =>
              have hih1 :=
                ih_strong fuel (Nat.lt_succ_self fuel) e1 cfg₁' cfg₂ (Value.closure x body env) hih2.1 h_beval1
              split at hbeval
              · next h_pureMode =>
                simp at hbeval
              · next h_notPureMode =>
                -- bevalFunctionBody
                cases fuel with
                | zero =>
                    simp [LeanPoison.bevalFunctionBody] at hbeval
                | succ fuel' =>
                    unfold LeanPoison.bevalFunctionBody at hbeval
                    simp at hbeval
                    split at hbeval
                    · next evalConfig v_body h_beval_body =>
                      injection hbeval with h_cfg_eq h_val_eq
                      subst h_cfg_eq h_val_eq
                      have h_env_wf : wfVarEnv cfg₂.nextAddr env := by
                        cases hih1.2 with
                        | closure _ _ _ hwf_env => exact hwf_env
                      have hle_arg : cfg₁'.nextAddr ≤ cfg₂.nextAddr :=
                        terminatesTo_nextAddr_mono e1 cfg₁' cfg₂ (Value.closure x body env) ⟨fuel'.succ, verbose, h_beval1⟩
                      have hv2_wf : wfValue cfg₂.nextAddr v₂ :=
                        wfValue_mono hle_arg v₂ hih2.2
                      have hwf_env_updated : wfVarEnv cfg₂.nextAddr (VarEnv.update env x v₂) :=
                        wfVarEnv_update cfg₂.nextAddr env x v₂ h_env_wf hv2_wf
                      have hwf_body_cfg : wfConfig { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } := by
                        rcases hih1.1 with ⟨hwfmem2, _⟩
                        exact ⟨hwfmem2, hwf_env_updated⟩
                      have hlt_body : fuel' < fuel'.succ.succ := by
                        exact Nat.lt_trans (Nat.lt_succ_self fuel') (Nat.lt_succ_self fuel'.succ)
                      have h_body_wf : wfConfig evalConfig ∧ wfValue evalConfig.nextAddr v_body :=
                        ih_strong fuel' hlt_body body
                          { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } evalConfig v_body
                          hwf_body_cfg h_beval_body
                      constructor
                      · rcases h_body_wf.1 with ⟨hwfmem_body, _⟩
                        constructor
                        · intro a hcontains
                          have hcontains' : evalConfig.memory.contains a := by
                            simpa using hcontains
                          exact hwfmem_body a hcontains'
                        · have hle_body : cfg₂.nextAddr ≤ evalConfig.nextAddr := by
                            have hle :=
                              terminatesTo_nextAddr_mono body
                                { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } evalConfig v_body
                                ⟨fuel', verbose, h_beval_body⟩
                            simpa using hle
                          exact wfVarEnv_mono hle_body cfg₂.varEnv hih1.1.2
                      · simpa using h_body_wf.2
                    · next h_oof =>
                      simp at hbeval
                    · next msg h_err =>
                      simp at hbeval
            · next cfg₂ x body env h_beval1 =>
              cases h_pure_body : Expr.toPExpr? body with
              | none =>
                  simp [h_pure_body] at hbeval
              | some pe_body =>
                  simp [h_pure_body] at hbeval
                  have hih1 :=
                    ih_strong fuel (Nat.lt_succ_self fuel) e1 cfg₁' cfg₂ (Value.peClosure x body env) hih2.1 h_beval1
                  cases fuel with
                  | zero =>
                      simp [LeanPoison.bevalFunctionBody] at hbeval
                  | succ fuel' =>
                      unfold LeanPoison.bevalFunctionBody at hbeval
                      simp at hbeval
                      split at hbeval
                      · next evalConfig v_body h_beval_body =>
                        injection hbeval with h_cfg_eq h_val_eq
                        subst h_cfg_eq h_val_eq
                        have h_env_wf : wfVarEnv cfg₂.nextAddr env := by
                          cases hih1.2 with
                          | peClosure _ _ _ hwf_env => exact hwf_env
                        have hle_arg : cfg₁'.nextAddr ≤ cfg₂.nextAddr :=
                          terminatesTo_nextAddr_mono e1 cfg₁' cfg₂ (Value.peClosure x body env) ⟨fuel'.succ, verbose, h_beval1⟩
                        have hv2_wf : wfValue cfg₂.nextAddr v₂ :=
                          wfValue_mono hle_arg v₂ hih2.2
                        have hwf_env_updated : wfVarEnv cfg₂.nextAddr (VarEnv.update env x v₂) :=
                          wfVarEnv_update cfg₂.nextAddr env x v₂ h_env_wf hv2_wf
                        have hwf_body : wfConfig { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := true } := by
                          rcases hih1.1 with ⟨hwfmem2, _⟩
                          exact ⟨hwfmem2, hwf_env_updated⟩
                        have hlt_body : fuel' < fuel'.succ.succ := by
                          exact Nat.lt_trans (Nat.lt_succ_self fuel') (Nat.lt_succ_self fuel'.succ)
                        have h_body : wfConfig evalConfig ∧ wfValue evalConfig.nextAddr v_body :=
                          ih_strong fuel' hlt_body body
                            { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := true } evalConfig v_body
                            hwf_body h_beval_body
                        have h_next_eq : evalConfig.nextAddr = cfg₂.nextAddr := by
                          have h_pure_eq :=
                            beval_pure_nextAddr_eq body fuel'
                              { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := true } evalConfig v_body
                              verbose pe_body h_pure_body rfl h_beval_body
                          simpa using h_pure_eq
                        constructor
                        · simpa using hih1.1
                        · have hv : wfValue cfg₂.nextAddr v_body := by
                            simpa [h_next_eq] using h_body.2
                          simpa using hv
                      · next h_oof =>
                        simp at hbeval
                      · next msg h_err =>
                        simp at hbeval
            · next v_other h_beval1 =>
              simp at hbeval
            · next h_oof =>
              simp at hbeval
            · next msg h_err =>
              simp at hbeval
          · next h_oof =>
            simp at hbeval
          · next msg h_err =>
            simp at hbeval
      -- Extern cases
      | externVal t p pred =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
      | externFn name t ret effs =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
      | externPfn name t ret =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval

end wfConfig_preserved_proof
