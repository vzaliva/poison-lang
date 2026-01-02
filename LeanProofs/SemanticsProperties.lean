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
    config₁.varEnv = config₂.varEnv ∧
    config₁.nextAddr = config₂.nextAddr ∧
    config₁.pureMode = config₂.pureMode := by
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
              have h_next_eq : config₁.nextAddr = config₂.nextAddr := by
                rw [h_eq_cfg]
              have h_pure_eq : config₁.pureMode = config₂.pureMode := by
                rw [h_eq_cfg]
              -- Rewrite evalUnaryOp to use the final value v.
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' =
                  EST.Out.ok (.success config₁ v₁) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, v₁, h_beval1_ex, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
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
    config₂.varEnv = config₃.varEnv ∧
    config₂.nextAddr = config₃.nextAddr ∧
    config₂.pureMode = config₃.pureMode := by
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
                  have h_next_eq : config₂.nextAddr = config₃.nextAddr := by
                    rw [h_eq_cfg]
                  have h_pure_eq : config₂.pureMode = config₃.pureMode := by
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
                  exact ⟨config₁, config₂, v₁, v₂, h_beval1_ex, h_beval2_ex, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
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
    config'.varEnv = config₁.varEnv ∧
    config'.nextAddr = config₁.nextAddr ∧
    config'.pureMode = config₁.pureMode := by
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
            refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp
            · simp
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
    config'.varEnv = config₁.varEnv ∧
    config'.nextAddr = config₁.nextAddr ∧
    config'.pureMode = config₁.pureMode := by
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
            refine ⟨config', Value.str v₁, h_beval1_ex, ⟨v₁, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
            · simp
            · simp
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


-- Helper lemma: extract evaluation structure from successful beval of rand
lemma bevalRand_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.rand e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ n, v1 = Value.num n) ∧
    (∃ randomNo, v = Value.num randomNo) ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv ∧
    config'.nextAddr = config₁.nextAddr ∧
    config'.pureMode = config₁.pureMode := by
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
        -- Check what v₁ is: must be Value.num for success path
        split at h_eq
        . next h_nonneg =>
           simp [EST.bind] at h_eq
           split at h_eq
           · next r_result r_state =>
             injection h_eq with h_eq_result h_eq_state
             injection h_eq_result with h_eq_cfg h_eq_val
             -- h_eq_val is Value.num randomNo = v (equality direction from injection)
             subst h_eq_cfg
             -- Use h_eq_val.symm to get v = Value.num randomNo and extract randomNo
             -- h_eq_val.symm gives us v = Value.num (Int.ofNat a✝) for rand or v = Value.num (Int.ofNat a✝ - 2*v₁) for frand
             -- Extract the number by pattern matching on the right-hand side
             have h_v_num : ∃ randomNo, v = Value.num randomNo := ⟨_, h_eq_val.symm⟩
             obtain ⟨randomNo, h_v_eq⟩ := h_v_num
             subst h_v_eq
             -- Construct existential for h_beval1
             have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num v₁)) w₁' :=
               ⟨w₀, h_state1, h_beval1⟩
             simp only [Nat.add_sub_cancel]
             refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ⟨randomNo, rfl⟩, ?_, ?_, ?_, ?_⟩
             · simp
             · simp
             · simp
             · simp
           · next r_error r_state =>
             -- IO operation failed, but we succeeded - contradiction
             injection h_eq
        . next h_neg =>
          -- After the println and return runtimeError
          simp [EST.bind] at h_eq
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
    · next h_error1 h_state1 =>
      -- EStateM.error - contradiction with success
      injection h_eq

-- Helper lemma: extract evaluation structure from successful beval of frand
lemma bevalFrand_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.frand e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁) →
  ∃ (config' : Config) (v1 : Value),
    (∃ w₀' w₁', LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀' = EST.Out.ok (.success config' v1) w₁') ∧
    (∃ n, v1 = Value.num n) ∧
    (∃ randomNo, v = Value.num randomNo) ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv ∧
    config'.nextAddr = config₁.nextAddr ∧
    config'.pureMode = config₁.pureMode := by
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
        -- Check what v₁ is: must be Value.num for success path
        split at h_eq
        . next h_nonneg =>
           simp [EST.bind] at h_eq
           split at h_eq
           · next r_result r_state =>
             injection h_eq with h_eq_result h_eq_state
             injection h_eq_result with h_eq_cfg h_eq_val
             -- h_eq_val is Value.num randomNo = v (equality direction from injection)
             subst h_eq_cfg
             -- Use h_eq_val.symm to get v = Value.num randomNo and extract randomNo
             -- h_eq_val.symm gives us v = Value.num (Int.ofNat a✝) for rand or v = Value.num (Int.ofNat a✝ - 2*v₁) for frand
             -- Extract the number by pattern matching on the right-hand side
             have h_v_num : ∃ randomNo, v = Value.num randomNo := ⟨_, h_eq_val.symm⟩
             obtain ⟨randomNo, h_v_eq⟩ := h_v_num
             subst h_v_eq
             -- Construct existential for h_beval1
             have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.num v₁)) w₁' :=
               ⟨w₀, h_state1, h_beval1⟩
             simp only [Nat.add_sub_cancel]
             refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ⟨randomNo, rfl⟩, ?_, ?_, ?_, ?_⟩
             · simp
             · simp
             · simp
             · simp
           · next r_error r_state =>
             -- IO operation failed, but we succeeded - contradiction
             injection h_eq
        . next h_neg =>
          -- After the println and return runtimeError
          simp [EST.bind] at h_eq
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
    · next h_error1 h_state1 =>
      -- EStateM.error - contradiction with success
      injection h_eq

-- ================================================================
-- NextAddr Monotonicity
-- ================================================================

section nextAddr_monotonic

/-- Helper lemma: bevalFunctionBody preserves monotonicity of nextAddr. -/
private lemma bevalFunctionBody_nextAddr_mono
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure w₀ =
      EST.Out.ok (.success finalConfig v) w₁) →
  currentConfig.nextAddr ≤ finalConfig.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp [pure] at h_eq
      cases h_eq
  | succ fuel' =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_body_result h_body_state h_beval_body =>
        split at h_eq
        · next evalConfig v_body =>
          split at h_eq
          · -- isPure = true
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            have h_next_eq : finalConfig.nextAddr = currentConfig.nextAddr := by
              have h_congr : ({ currentConfig with pureMode := false } : Config).nextAddr = finalConfig.nextAddr :=
                congrArg Config.nextAddr h_cfg_eq
              calc
                finalConfig.nextAddr = ({ currentConfig with pureMode := false } : Config).nextAddr := by
                  symm
                  exact h_congr
                _ = currentConfig.nextAddr := rfl
            simp [h_next_eq]
          · -- isPure = false
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            have h_next_eq : finalConfig.nextAddr = evalConfig.nextAddr := by
              have h_congr : ({ currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := false } : Config).nextAddr = finalConfig.nextAddr :=
                congrArg Config.nextAddr h_cfg_eq
              calc
                finalConfig.nextAddr = ({ currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := false } : Config).nextAddr := by
                  symm
                  exact h_congr
                _ = evalConfig.nextAddr := rfl
            have h_bodyConfig_next : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).nextAddr = currentConfig.nextAddr := rfl
            have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval_body_ex : ∃ w₀' w₁', LeanPoison.beval fuel' ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) body verbose w₀' =
                EST.Out.ok (.success evalConfig v_body) w₁' :=
              ⟨w₀, h_body_state, h_beval_body⟩
            have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body_ex
            have IH_body' : currentConfig.nextAddr ≤ evalConfig.nextAddr := by
              simpa [h_bodyConfig_next] using IH_body
            simp [h_next_eq]
            exact IH_body'
        · next =>
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          injection h_eq with h_result h_world
          injection h_result
      · next h_body_error h_body_state =>
        injection h_eq

private lemma beval_nextAddr_mono_ite (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      cases h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config₁' =>
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config₂ v₂ =>
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              subst h_eq_config
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool true)) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₁' e2 verbose w₀' = EST.Out.ok (.success config₂ v₂) w₁' :=
                ⟨h_state1, h_state2, h_beval2⟩
              have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool true) h_beval1_ex
              have IH2 := IH fuel' h_fuel e2 config₁' config₂ v₂ h_beval2_ex
              exact Nat.le_trans IH1 IH2
            · next =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
            · next msg =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next config₁' =>
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result3 h_state3 h_beval3 =>
            split at h_eq
            · next config₂ v₃ =>
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              subst h_eq_config
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config₁' (Value.bool false)) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval3_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₁' e3 verbose w₀' = EST.Out.ok (.success config₂ v₃) w₁' :=
                ⟨h_state1, h_state3, h_beval3⟩
              have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool false) h_beval1_ex
              have IH3 := IH fuel' h_fuel e3 config₁' config₂ v₃ h_beval3_ex
              exact Nat.le_trans IH1 IH3
            · next =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
            · next msg =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
          · next h_error3 h_state3 =>
            injection h_eq
        · next v =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error1 h_state1 =>
        injection h_eq

private lemma beval_nextAddr_mono_deref (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.deref e1) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      cases h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' loc_val =>
          cases h_mem_lookup : config'.memory.get? loc_val with
          | some n =>
            have h_mem_eq : config'.memory[loc_val]? = some n := h_mem_lookup
            rw [h_mem_eq] at h_eq
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            subst h_eq_config
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.loc loc_val)) w₁' :=
              ⟨w₀, h_state1, h_beval1⟩
            exact IH fuel' h_fuel e1 config₀ config' (Value.loc loc_val) h_beval1_ex
          | none =>
            have h_mem_eq : config'.memory[loc_val]? = none := by
              simpa using h_mem_lookup
            simp [h_mem_eq] at h_eq
            injection h_eq with h_result h_world
            injection h_result
        · next v =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error1 h_state1 =>
        injection h_eq

private lemma beval_nextAddr_mono_assign (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      cases h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result1 h_state1 h_beval1 =>
        split at h_eq
        · next config' loc_val =>
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            split at h_eq
            · next config'' n_val =>
              injection h_eq with h_result h_world
              injection h_result with h_eq_config h_eq_val
              subst h_eq_config
              -- Chain through IH on e1 and e2
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e1 verbose w₀' = EST.Out.ok (.success config' (Value.loc loc_val)) w₁' :=
                ⟨w₀, h_state1, h_beval1⟩
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config' e2 verbose w₀' = EST.Out.ok (.success config'' (Value.num n_val)) w₁' :=
                ⟨h_state1, h_state2, h_beval2⟩
              have IH1 := IH fuel' h_fuel e1 config₀ config' (Value.loc loc_val) h_beval1_ex
              have IH2 := IH fuel' h_fuel e2 config' config'' (Value.num n_val) h_beval2_ex
              exact Nat.le_trans IH1 IH2
            · next v =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
            · next =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
            · next msg =>
              simp [pure] at h_eq
              injection h_eq with h_result h_world
              injection h_result
          · next h_error2 h_state2 =>
            injection h_eq
        · next v =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error1 h_state1 =>
        injection h_eq

private lemma beval_nextAddr_mono_app (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.app e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      cases h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      simp [bind, Bind.bind, EST.bind] at h_eq
      split at h_eq
      · next h_result2 h_state2 h_beval2 =>
        split at h_eq
        · next config₁' v₂ =>
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result1 h_state1 h_beval1 =>
            split at h_eq
            · next config₂ x body env =>
              split at h_eq
              · next h_pureMode =>
                injection h_eq with h_result h_world
                injection h_result
              · next h_notPureMode =>
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
                  ⟨w₀, h_state2, h_beval2⟩
                have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.closure x body env)) w₁' :=
                  ⟨h_state2, h_state1, h_beval1⟩
                have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2_ex
                have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.closure x body env) h_beval1_ex
                have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false w₀' =
                    EST.Out.ok (.success config₁ v) w₁' :=
                  ⟨h_state1, w₁, h_eq⟩
                have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                  (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
                  config₀.nextAddr ≤ config₁.nextAddr := by
                  intro m h_m_lt e config₀ config₁ v h_beval_ex
                  have h_m_lt_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt (Nat.le_succ fuel')
                  exact IH m h_m_lt_succ e config₀ config₁ v h_beval_ex
                have IH_body :=
                  bevalFunctionBody_nextAddr_mono fuel' verbose config₂ config₁ env x v₂ body false v IH_fuel' h_bevalFunctionBody_ex
                exact Nat.le_trans IH2 (Nat.le_trans IH1 IH_body)
            · next config₂ x body env =>
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have h_beval2_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ e2 verbose w₀' = EST.Out.ok (.success config₁' v₂) w₁' :=
                ⟨w₀, h_state2, h_beval2⟩
              have h_beval1_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₁' e1 verbose w₀' = EST.Out.ok (.success config₂ (Value.peClosure x body env)) w₁' :=
                ⟨h_state2, h_state1, h_beval1⟩
              have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2_ex
              have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.peClosure x body env) h_beval1_ex
              have h_bevalFunctionBody_ex : ∃ w₀' w₁', LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true w₀' =
                  EST.Out.ok (.success config₁ v) w₁' :=
                ⟨h_state1, w₁, h_eq⟩
              have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
                config₀.nextAddr ≤ config₁.nextAddr := by
                intro m h_m_lt e config₀ config₁ v h_beval_ex
                have h_m_lt_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt (Nat.le_succ fuel')
                exact IH m h_m_lt_succ e config₀ config₁ v h_beval_ex
              have IH_body :=
                bevalFunctionBody_nextAddr_mono fuel' verbose config₂ config₁ env x v₂ body true v IH_fuel' h_bevalFunctionBody_ex
              exact Nat.le_trans IH2 (Nat.le_trans IH1 IH_body)
            · next v =>
              injection h_eq with h_result h_world
              injection h_result
            · next =>
              injection h_eq with h_result h_world
              injection h_result
            · next msg =>
              injection h_eq with h_result h_world
              injection h_result
          · next h_error1 h_state1 =>
            injection h_eq
        · next =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at h_eq
          injection h_eq with h_result h_world
          injection h_result
      · next h_error2 h_state2 =>
        injection h_eq

private lemma beval_nextAddr_mono_kwhile (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr) :
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ (Expr.kwhile e1 e2) verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro h_eval
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  unfold LeanPoison.beval at h_eq
  simp at h_eq
  cases fuel with
  | zero =>
      simp at h_eq
      cases h_eq
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
      have h_beval_unfolded_ex : ∃ w₀' w₁', LeanPoison.beval fuel' config₀ unfolded verbose w₀' = EST.Out.ok (.success config₁ v) w₁' :=
        ⟨w₀, w₁, h_eq⟩
      exact IH fuel' h_fuel unfolded config₀ config₁ v h_beval_unfolded_ex

private lemma beval_nextAddr_mono : ∀ (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  (∃ w₀ w₁, LeanPoison.beval fuel config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro e fuel verbose config₀ config₁ v h_eval
  revert e verbose config₀ config₁ v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e verbose config₀ config₁ v h_eval
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      (∃ w₀ w₁, LeanPoison.beval m config₀ e verbose w₀ = EST.Out.ok (.success config₁ v) w₁) →
      config₀.nextAddr ≤ config₁.nextAddr := by
      intro m h_lt e' config₀' config₁' v' h_eval'
      exact IH m h_lt e' verbose config₀' config₁' v' h_eval'
    cases e with
    | externVal typ poison pred =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
    | externFn arg argTyp retSpec effects =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
    | externPfn arg argTyp retSpec =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
    | num n | bool b | unit | str s =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            subst h_eq_config
            exact le_rfl
    | var x =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_lookup : config₀.varEnv.lookup x with
            | some v_lookup =>
                simp [h_lookup] at h_eq
                injection h_eq with h_result h_world
                injection h_result with h_eq_config h_eq_val
                subst h_eq_config
                exact le_rfl
            | none =>
                simp [h_lookup] at h_eq
                injection h_eq with h_result h_world
                injection h_result
    | fn x paramType body returnType =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            subst h_eq_config
            exact le_rfl
    | pfn x paramType body returnType =>
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        cases fuel with
        | zero =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            injection h_eq with h_result h_world
            injection h_result with h_eq_config h_eq_val
            subst h_eq_config
            exact le_rfl
    | op e1 op e2 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, cfg₁2, v1, v2, hbeval1, hbeval2, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁1 cfg₁2 v2 hbeval2
            have hle02 : config₀.nextAddr ≤ cfg₁2.nextAddr := Nat.le_trans hle1 hle2
            simpa [h_next] using hle02
    | unaryop op e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | ite e1 e2 e3 =>
        exact beval_nextAddr_mono_ite e1 e2 e3 fuel verbose config₀ config₁ v IH_converted h_eval
    | newRef e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
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
        exact beval_nextAddr_mono_assign e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval
    | deref e1 =>
        exact beval_nextAddr_mono_deref e1 fuel verbose config₀ config₁ v IH_converted h_eval
    | seq e1 e2 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalSeq_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁1 config₁ v hbeval2
            exact Nat.le_trans hle1 hle2
    | kwhile e1 e2 =>
        exact beval_nextAddr_mono_kwhile e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval
    | vlet x e1 e2 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, cfg₁2, cfg₁3, v1, hbeval1, hcfg2, hbeval2, hcfg_final⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁2 cfg₁3 v hbeval2
            -- nextAddr unchanged by varEnv updates
            have h_next_eq1 : cfg₁2.nextAddr = cfg₁1.nextAddr := by
              simp [hcfg2]
            have h_next_eq2 : config₁.nextAddr = cfg₁3.nextAddr := by
              simp [hcfg_final]
            have hle01 : config₀.nextAddr ≤ cfg₁2.nextAddr := by
              simpa [h_next_eq1] using hle1
            have hle03 : config₀.nextAddr ≤ cfg₁3.nextAddr := Nat.le_trans hle01 hle2
            simpa [h_next_eq2] using hle03
    | app e1 e2 =>
        exact beval_nextAddr_mono_app e1 e2 fuel verbose config₀ config₁ v IH_converted h_eval
    | rand e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalRand_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, _hv_num, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | frand e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalFrand_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, _hv_num, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | printInt e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalPrintInt_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, _hv_unit, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | printString e1 =>
        cases fuel with
        | zero =>
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            unfold LeanPoison.beval at h_eq
            simp at h_eq
            cases h_eq
        | succ fuel' =>
            have hstruct :=
              bevalPrintString_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_str, _hv_unit, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1

/-- Next address is monotone for terminating evaluations. -/
lemma terminatesToW_nextAddr_mono (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesToW e cfg₀ cfg₁ v →
    cfg₀.nextAddr ≤ cfg₁.nextAddr := by
  intro hterm
  rcases hterm with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  exact beval_nextAddr_mono e fuel verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩

end nextAddr_monotonic

-- ================================================================
-- wfConfig_preservedW Proof
-- ================================================================

section wfConfig_preservedW_proof

-- Private lemmas for wfConfig_preservedW proof

/-- evalUnaryOp preserves well-formedness of values. -/
private lemma evalUnaryOp_preserves_wfValue (next : Address) (op : UnaryOp) (v1 v : Value) :
    wfValue next v1 →
    LeanPoison.evalUnaryOp op v1 = some v →
    wfValue next v := by
  intro h_wf_v1 h_eval
  cases op with
  | not =>
      -- evalUnaryOp only succeeds for boolean values
      simp [LeanPoison.evalUnaryOp] at h_eval
      cases h_wf_v1 with
      | bool b =>
          injection h_eval with h_eq
          subst h_eq
          exact wfValue.bool (!b)
      | num _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
          -- evalUnaryOp returns none for these, contradiction
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
  -- Prove by induction on the list structure
  induction env with
  | nil =>
      -- VarEnv.lookup on empty list returns none, but h_lookup says some v
      -- This is impossible - simp recognizes the contradiction
      simp [VarEnv.lookup, List.lookup] at h_lookup
  | cons head tail ih =>
      cases head with
      | mk x' v' =>
          cases h_wf_env with
          | cons x'_wf v'_wf env'_wf h_wf_v' h_wf_tail =>
              simp [VarEnv.lookup, List.lookup] at h_lookup
              -- List.lookup checks if x == x'
              by_cases h_eq : x == x'
              · -- If x == x', then lookup returns v'
                  simp [h_eq] at h_lookup
                  -- After simp, h_lookup becomes v' = v
                  subst h_lookup
                  exact h_wf_v'
              · -- Otherwise, lookup in tail
                  simp [h_eq] at h_lookup
                  exact ih h_wf_tail h_lookup

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

/-- Helper lemma for newRef case of wfConfig_preservedW. -/
private lemma wfConfig_preservedW_newRef (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.newRef e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalNewRef_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, n, a, hbeval1, ha, hmem_eq, hnext_eq, hvar_eq, hval_eq⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 (Value.num n) hwf₀ w₀1 w₁1 hbeval1'
  -- wfConfig for cfg₁
  constructor
  · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    constructor
    · intro addr hcontains
      -- rewrite memory update
      have hcontains' : (cfg₁1.memory.update a n).contains addr := by
        simp [hmem_eq] at hcontains
        exact hcontains
      by_cases h_eq : addr = a
      · subst h_eq
        -- a = cfg₁1.nextAddr and cfg₁.nextAddr = cfg₁1.nextAddr + 1
        simp [ha, hnext_eq]
      · have hcmp : compare a addr ≠ Ordering.eq := by
          intro hcmp
          have h_eq' : a = addr := LawfulEqCmp.eq_of_compare hcmp
          exact h_eq h_eq'.symm
        have hcontains1 : cfg₁1.memory.contains addr := by
          -- update is insert; since addr ≠ a, contains must come from old memory
          simpa [Memory.update] using
            (ExtTreeMap.contains_of_contains_insert (t := cfg₁1.memory) (k := a) (a := addr) (v := n) hcontains' hcmp)
        have hlt := hwfmem1 addr hcontains1
        have hlt' : addr < cfg₁1.nextAddr + 1 :=
          Nat.lt_trans hlt (Nat.lt_succ_self _)
        simp [hnext_eq]
        exact hlt'
    · -- varEnv unchanged; lift bound to nextAddr+1
      have hle : cfg₁1.nextAddr ≤ cfg₁.nextAddr := by
        simp [hnext_eq]
      have hwfenv1' : wfVarEnv cfg₁.nextAddr cfg₁1.varEnv :=
        wfVarEnv_mono hle cfg₁1.varEnv hwfenv1
      simp [hvar_eq]
      exact hwfenv1'
  · -- result value is the fresh location
    have hlt : a < cfg₁.nextAddr := by
      simp [ha, hnext_eq]
    simpa [hval_eq] using (wfValue.loc hlt)

private lemma wfConfig_preservedW_ite (e1 e2 e3 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.ite e1 e2 e3) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_assign (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.assign e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_deref (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.deref e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_seq (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.seq e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalSeq_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  rcases hbeval2 with ⟨w₀2, w₁2, hbeval2'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
  have hih2 := ih e2 cfg₁1 cfg₁ v hih1.1 w₀2 w₁2 hbeval2'
  exact hih2

private lemma wfConfig_preservedW_kwhile (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.kwhile e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_vlet (x : Name) (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.vlet x e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_app (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.app e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  sorry

private lemma wfConfig_preservedW_rand (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.rand e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalRand_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, hv_num, h_mem, h_var, h_next, _h_pure⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
  constructor
  · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    constructor
    · intro a hcontains
      have hcontains1 : cfg₁1.memory.contains a := by
        simpa [h_mem] using hcontains
      have hlt := hwfmem1 a hcontains1
      simpa [h_next] using hlt
    · simpa [h_var, h_next] using hwfenv1
  · rcases hv_num with ⟨randomNo, hv_eq⟩
    subst hv_eq
    exact wfValue.num randomNo

private lemma wfConfig_preservedW_frand (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.frand e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalFrand_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, hv_num, h_mem, h_var, h_next, _h_pure⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
  constructor
  · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    constructor
    · intro a hcontains
      have hcontains1 : cfg₁1.memory.contains a := by
        simpa [h_mem] using hcontains
      have hlt := hwfmem1 a hcontains1
      simpa [h_next] using hlt
    · simpa [h_var, h_next] using hwfenv1
  · rcases hv_num with ⟨randomNo, hv_eq⟩
    subst hv_eq
    exact wfValue.num randomNo

private lemma wfConfig_preservedW_printInt (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.printInt e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalPrintInt_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_num, hv_unit, h_mem, h_var, h_next, _h_pure⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
  constructor
  · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    constructor
    · intro a hcontains
      have hcontains1 : cfg₁1.memory.contains a := by
        simpa [h_mem] using hcontains
      have hlt := hwfmem1 a hcontains1
      simpa [h_next] using hlt
    · simpa [h_var, h_next] using hwfenv1
  · simpa [hv_unit] using wfValue.unit

private lemma wfConfig_preservedW_printString (e1 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.printString e1) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
        wfConfig cfg₀' →
        ∀ (w₀' w₁' : Void IO.RealWorld),
          LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
          wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  have hstruct :=
    bevalPrintString_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
  rcases hstruct with ⟨cfg₁1, v1, hbeval1, _hv1_str, hv_unit, h_mem, h_var, h_next, _h_pure⟩
  rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
  constructor
  · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    constructor
    · intro a hcontains
      have hcontains1 : cfg₁1.memory.contains a := by
        simpa [h_mem] using hcontains
      have hlt := hwfmem1 a hcontains1
      simpa [h_next] using hlt
    · simpa [h_var, h_next] using hwfenv1
  · simpa [hv_unit] using wfValue.unit

private lemma wfConfig_preservedW_externVal (t : Typ) (p : Bool) (pred : SyntaxPredicate) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.externVal t p pred) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁) :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  cases hbeval

private lemma wfConfig_preservedW_externFn (name : Name) (t : Typ) (ret : ExternReturn) (effs : List Effect)
    (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.externFn name t ret effs) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁) :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  cases hbeval

private lemma wfConfig_preservedW_externPfn (name : Name) (t : Typ) (ret : ExternReturn) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.externPfn name t ret) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁) :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  cases hbeval

/-- Evaluation preserves config well-formedness (world-indexed), for use in FR proofs. -/
lemma wfConfig_preservedW (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesToW e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  intro hterm hwf₀
  rcases hterm with ⟨fuel, verbose, w₀, w₁, hbeval⟩
  -- Proof by induction on fuel; main split is on the expression.
  induction fuel generalizing e cfg₀ cfg₁ v w₀ w₁ with
  | zero =>
      -- beval 0 cannot succeed.
      unfold LeanPoison.beval at hbeval
      simp at hbeval
      cases hbeval
  | succ fuel ih =>
      cases e with
      -- Literals (simple cases: config unchanged, value is well-formed)
      | num n =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · exact wfValue.num n
      | bool b =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · exact wfValue.bool b
      | unit =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · exact wfValue.unit
      | str s =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · exact wfValue.str s
      -- Variables (simple: config unchanged, value from varEnv which is well-formed)
      | var x =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          -- Handle the match on config.varEnv.lookup x
          cases h_lookup : cfg₀.varEnv.lookup x with
          | some v_lookup =>
              simp [h_lookup] at hbeval
              injection hbeval with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              subst h_eq_cfg
              constructor
              · exact hwf₀
              · -- v_lookup comes from cfg₀.varEnv, which is well-formed by hwf₀
                have h_wf_env := hwf₀.2
                have h_wf_v_lookup := wfVarEnv_lookup cfg₀.nextAddr cfg₀.varEnv x v_lookup h_wf_env h_lookup
                -- After injection, v = v_lookup, so rewrite
                rw [← h_eq_val]
                exact h_wf_v_lookup
          | none =>
              simp [h_lookup] at hbeval
              injection hbeval with h_eq_result h_eq_state
              injection h_eq_result
      -- Function abstractions (simple: config unchanged, closure value)
      | fn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · -- Closure: need to show varEnv is well-formed
            have h_wf_env := hwf₀.2
            exact wfValue.closure x body cfg₀.varEnv h_wf_env
      | pfn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          injection hbeval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          constructor
          · exact hwf₀
          · -- Pure closure: need to show varEnv is well-formed
            have h_wf_env := hwf₀.2
            exact wfValue.peClosure x body cfg₀.varEnv h_wf_env
      -- Inductive cases (require IH)
      | op e1 op e2 =>
          -- Use the structure lemma for binary operations
          have hstruct :=
            bevalOp_structure e1 e2 op (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
          rcases hstruct with
            ⟨cfg₁1, cfg₁2, v1, v2, hbeval1, hbeval2, h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
          rcases hbeval2 with ⟨w₀2, w₁2, hbeval2'⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
          have hih2 := ih e2 cfg₁1 cfg₁2 v2 hih1.1 w₀2 w₁2 hbeval2'
          constructor
          · -- wfConfig cfg₁
            rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro a hcontains
              have hcontains2 : cfg₁2.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem2 a hcontains2
              simpa [h_next] using hlt
            · -- wfVarEnv for cfg₁
              simpa [h_var, h_next] using hwfenv2
          · -- wfValue cfg₁.nextAddr v
            exact evalOp_preserves_wfValue cfg₁.nextAddr op v1 v2 v h_evalOp
      | unaryop op e1 =>
          have hstruct :=
            bevalUnaryOp_structure op e1 (fuel + 1) verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩
          rcases hstruct with ⟨cfg₁1, v1, hbeval1, h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          rcases hbeval1 with ⟨w₀1, w₁1, hbeval1'⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀1 w₁1 hbeval1'
          constructor
          · -- wfConfig cfg₁
            rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro a hcontains
              have hcontains1 : cfg₁1.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem1 a hcontains1
              simpa [h_next] using hlt
            · simpa [h_var, h_next] using hwfenv1
          · -- wfValue cfg₁.nextAddr v
            have h_evalOp_v : LeanPoison.evalUnaryOp op v1 = some v := h_evalOp
            exact evalUnaryOp_preserves_wfValue cfg₁.nextAddr op v1 v (by simpa [h_next] using hih1.2) h_evalOp_v
      | ite e1 e2 e3 =>
          exact wfConfig_preservedW_ite e1 e2 e3 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | newRef e1 =>
          exact wfConfig_preservedW_newRef e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | assign e1 e2 =>
          exact wfConfig_preservedW_assign e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | deref e1 =>
          exact wfConfig_preservedW_deref e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | seq e1 e2 =>
          exact wfConfig_preservedW_seq e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | kwhile e1 e2 =>
          exact wfConfig_preservedW_kwhile e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | vlet x e1 e2 =>
          exact wfConfig_preservedW_vlet x e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | app e1 e2 =>
          exact wfConfig_preservedW_app e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | rand e1 =>
          exact wfConfig_preservedW_rand e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | frand e1 =>
          exact wfConfig_preservedW_frand e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | printInt e1 =>
          exact wfConfig_preservedW_printInt e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      | printString e1 =>
          exact wfConfig_preservedW_printString e1 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih
      -- Extern cases
      | externVal t p pred =>
          exact wfConfig_preservedW_externVal t p pred fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval
      | externFn name t ret effs =>
          exact wfConfig_preservedW_externFn name t ret effs fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval
      | externPfn name t ret =>
          exact wfConfig_preservedW_externPfn name t ret fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval

end wfConfig_preservedW_proof
