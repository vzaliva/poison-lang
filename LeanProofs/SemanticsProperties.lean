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
             refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ⟨randomNo, rfl⟩, ?_, ?_⟩
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
             refine ⟨config', Value.num v₁, h_beval1_ex, ⟨v₁, rfl⟩, ⟨randomNo, rfl⟩, ?_, ?_⟩
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
      | ite e1 e2 e3 => sorry
      | newRef e1 => sorry
      | assign e1 e2 => sorry
      | deref e1 => sorry
      | seq e1 e2 => sorry
      | kwhile e1 e2 => sorry
      | vlet x e1 e2 => sorry
      | app e1 e2 => sorry
      | rand e1 => sorry
      | frand e1 => sorry
      | printInt e1 => sorry
      | printString e1 => sorry
      -- Extern cases
      | externVal _ _ _ => sorry
      | externFn _ _ _ _ => sorry
      | externPfn _ _ _ => sorry

end wfConfig_preservedW_proof
