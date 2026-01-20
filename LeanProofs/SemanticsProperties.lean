-- Common big-step semantics properties for the Poison Language
--
-- This file contains shared definitions and properties related to evaluation
-- semantics, including evaluation relations and runtime configuration well-formedness.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.IOHelpers
import LeanProofs.IOFree

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
def terminatesToW (w₀ w₁ : Void IO.RealWorld) (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
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
-- IOFree World Preservation
-- ================================================================

-- For IOFree expressions, beval doesn't perform any actual I/O operations,
-- so the world state is preserved. This allows us to convert between
-- world-indexed evaluation (terminatesToW) and world-free evaluation (terminatesTo).

/-- For IOFree expressions, successful beval preserves the world (output = input).
    This is the key lemma that enables reuse of world-indexed structure lemmas
    to prove world-free inversion lemmas.

    Note: The `app` case requires that closures contain IOFree bodies, which
    cannot be recovered from the runtime closure value. For applications,
    we rely on the IOFree predicate covering the entire expression including
    the closure definition site. -/
lemma beval_IOFree_preserves_world (fuel : Nat) (cfg : Config) (e : Expr) (verbose : Bool)
    (r : LeanPoison.EvalResult) (w₀ w₁ : Void IO.RealWorld) :
    IOFree e →
    LeanPoison.beval fuel cfg e verbose w₀ = EST.Out.ok r w₁ →
    w₁ = w₀ := by
  sorry

/-- For IOFree expressions, beval at any world produces the same result.
    Combined with world preservation, this allows us to convert world-indexed
    evaluation to world-free (pure) evaluation. -/
lemma beval_IOFree_result_eq (fuel : Nat) (cfg : Config) (e : Expr) (verbose : Bool)
    (r₁ r₂ : LeanPoison.EvalResult) (w₁ w₂ w₁' w₂' : Void IO.RealWorld) :
    IOFree e →
    LeanPoison.beval fuel cfg e verbose w₁ = EST.Out.ok r₁ w₁' →
    LeanPoison.beval fuel cfg e verbose w₂ = EST.Out.ok r₂ w₂' →
    r₁ = r₂ := by
  sorry

/-- Convert world-indexed evaluation to world-free evaluation for IOFree expressions.
    This is the key bridge lemma that allows using world-indexed structure lemmas
    to prove world-free inversion lemmas. -/
lemma beval_IOFree_eq_pure (fuel : Nat) (cfg : Config) (e : Expr) (verbose : Bool)
    (r : LeanPoison.EvalResult) (w : Void IO.RealWorld) :
    IOFree e →
    LeanPoison.beval fuel cfg e verbose w = EST.Out.ok r w →
    LeanPoison.beval fuel cfg e verbose = pure r := by
  sorry

-- ================================================================
-- Evaluation Structure Lemmas
-- ================================================================

-- Helper lemma: extract evaluation structure from successful beval of unary operation.
lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁ →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ v1) w₁ ∧
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
              -- `h_eq_state` identifies the final world of the whole unaryop evaluation.
              -- After rewriting, we can return the *outer* output world `w₁` as `w_mid`.
              -- This is convenient for world-threading proofs.
              simp only [Nat.add_sub_cancel]
              refine ⟨config₁, v₁, ?_, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
              -- The input world to `e1` is the same as the input world to the whole unaryop.
              simpa [h_eq_state] using h_beval1
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
    (config₀ config₃ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose w₀ =
      EST.Out.ok (.success config₃ v) w₁ →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ v1) w_mid ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose w_mid =
        EST.Out.ok (.success config₂ v2) w₁ ∧
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
                  simp only [Nat.add_sub_cancel]
                  -- `h_eq_state` already identifies the final world.
                  subst h_eq_state
                  refine ⟨config₁, config₂, v₁, v₂, h_state1, ?_, ?_, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
                  · exact h_beval1
                  · exact h_beval2
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
    (config₀ config₂ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁ →
  ∃ (config₁ : Config) (v1 : Value) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ v1) w_mid ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose w_mid =
        EST.Out.ok (.success config₂ v) w₁ := by
  intro h_eq
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
              have hw : h_state2 = w₁ := by
                exact h_eq_state
              simp only [Nat.add_sub_cancel]
              refine ⟨config₁, v₁, h_state1, h_beval1, ?_⟩
              simpa [hw] using h_beval2
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
    (config₀ config_final : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose w₀ =
      EST.Out.ok (.success config_final v) w₁ →
  ∃ (config₁ config₂ config₃ : Config) (v1 : Value) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ v1) w_mid ∧
    config₂ = { config₁ with varEnv := config₁.varEnv.update x v1 } ∧
    LeanPoison.beval (fuel - 1) config₂ e2 verbose w_mid =
        EST.Out.ok (.success config₃ v) w₁ ∧
    config_final = { config₃ with varEnv := config₁.varEnv } := by
  intro h_eq
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
              -- Now subst to get final config and value
              subst h_eq_cfg h_eq_val
              simp only [Nat.add_sub_cancel]
              have hw : h_state2 = w₁ := by
                exact h_eq_state
              refine ⟨config₁', config₂', config₃', v₁, h_state1, ?_, rfl, ?_, rfl⟩
              · -- beval e1
                exact h_beval1
              · -- beval e2 (rewrite final world)
                simpa [hw] using h_beval2
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
    (config₀ config₂ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁ →
  ∃ (config₁ : Config) (n : Int) (a : Address),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ (Value.num n)) w₁ ∧
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
          simp only [Nat.add_sub_cancel]
          -- The final world of the whole `newRef` evaluation is the world after `e1`.
          have hw : h_state1 = w₁ := by
            exact h_eq_state
          refine ⟨config', n, config'.nextAddr, ?_, rfl, ?_⟩
          · -- beval of e1, with the outer worlds
            simpa [hw] using h_beval1
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
          constructor
          · -- config₂.pureMode = config₁.pureMode
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

-- Helper lemma: extract evaluation structure from successful beval of deref
lemma bevalDeref_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.deref e1) verbose w₀ =
      EST.Out.ok (.success config₁ v) w₁ →
  ∃ (config' : Config) (a : Address) (n : Int),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config' (Value.loc a)) w₁ ∧
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
        | loc a =>
          -- Need to handle memory lookup using bracket notation in beval
          cases h_lookup : config'.memory[a]? with
          | none =>
            simp only [h_lookup, pure] at h_eq
            injection h_eq with h_result _
            injection h_result
          | some n =>
            simp only [h_lookup, pure] at h_eq
            injection h_eq with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            simp only [Nat.add_sub_cancel]
            have hw : h_state1 = w₁ := by exact h_eq_state
            -- Convert h_lookup to use .lookup
            have h_lookup' : config'.memory.lookup a = some n := h_lookup
            refine ⟨config', a, n, ?_, h_lookup', h_eq_val.symm, ?_, ?_, ?_, ?_⟩
            · simpa [hw] using h_beval1
            · rw [← h_eq_cfg]
            · rw [← h_eq_cfg]
            · rw [← h_eq_cfg]
            · rw [← h_eq_cfg]
        | num _ | bool _ | unit | str _ | closure _ _ _ | peClosure _ _ _ =>
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

-- Helper lemma: extract evaluation structure from successful beval of assign
lemma bevalAssign_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁ →
  ∃ (config₁ config₁' : Config) (a : Address) (n : Int) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ (Value.loc a)) w_mid ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose w_mid =
        EST.Out.ok (.success config₁' (Value.num n)) w₁ ∧
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
    injection h_eq with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    simp [bind, Bind.bind, EST.bind] at h_eq
    split at h_eq
    · next h_result1 h_state1 h_beval1 =>
      cases h_result1 with
      | success config₁ v₁ =>
        cases v₁ with
        | loc a =>
          simp [EST.bind] at h_eq
          split at h_eq
          · next h_result2 h_state2 h_beval2 =>
            cases h_result2 with
            | success config₁' v₂ =>
              cases v₂ with
              | num n =>
                simp at h_eq
                injection h_eq with h_eq_result h_eq_state
                injection h_eq_result with h_eq_cfg h_eq_val
                simp only [Nat.add_sub_cancel]
                subst h_eq_state
                refine ⟨config₁, config₁', a, n, h_state1, h_beval1, h_beval2, h_eq_val.symm, ?_, ?_, ?_, ?_⟩
                · rw [← h_eq_cfg]
                · rw [← h_eq_cfg]
                · rw [← h_eq_cfg]
                · rw [← h_eq_cfg]
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
          · injection h_eq
        | num _ | bool _ | unit | str _ | closure _ _ _ | peClosure _ _ _ =>
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

-- Helper lemma: extract evaluation structure from successful beval of ite
lemma bevalIte_structure (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose w₀ =
      EST.Out.ok (.success config₂ v) w₁ →
  ∃ (config₁ : Config) (b : Bool) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ (Value.bool b)) w_mid ∧
    ((b = true ∧ LeanPoison.beval (fuel - 1) config₁ e2 verbose w_mid =
        EST.Out.ok (.success config₂ v) w₁) ∨
     (b = false ∧ LeanPoison.beval (fuel - 1) config₁ e3 verbose w_mid =
        EST.Out.ok (.success config₂ v) w₁)) := by
  intro h_eq
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
      | success config₁ v₁ =>
        cases v₁ with
        | bool b =>
          simp only [Nat.add_sub_cancel]
          cases b with
          | true =>
            simp [EST.bind] at h_eq
            split at h_eq
            · next h_result2 h_state2 h_beval2 =>
              split at h_eq
              · injection h_eq with h_eq_result h_eq_state
                injection h_eq_result with h_eq_cfg h_eq_val
                subst h_eq_cfg h_eq_val h_eq_state
                refine ⟨config₁, true, h_state1, h_beval1, Or.inl ⟨rfl, h_beval2⟩⟩
              · injection h_eq with h_r _; injection h_r
              · injection h_eq with h_r _; injection h_r
            · injection h_eq
          | false =>
            simp [EST.bind] at h_eq
            split at h_eq
            · next h_result3 h_state3 h_beval3 =>
              split at h_eq
              · injection h_eq with h_eq_result h_eq_state
                injection h_eq_result with h_eq_cfg h_eq_val
                subst h_eq_cfg h_eq_val h_eq_state
                refine ⟨config₁, false, h_state1, h_beval1, Or.inr ⟨rfl, h_beval3⟩⟩
              · injection h_eq with h_r _; injection h_r
              · injection h_eq with h_r _; injection h_r
            · injection h_eq
        | num _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
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

-- Helper lemma: extract evaluation structure from successful beval of kwhile
-- Note: The kwhile desugars to an ite in beval, making the proof structure complex.
-- For now we leave this as sorry; the inversion lemma can use the ite structure.
lemma bevalKwhile_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) (w₀ w₁ : Void IO.RealWorld) :
  LeanPoison.beval fuel config₀ (Expr.kwhile e1 e2) verbose w₀ =
      EST.Out.ok (.success config_final v) w₁ →
  ∃ (config₁ : Config) (b : Bool) (w_mid : Void IO.RealWorld),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose w₀ =
        EST.Out.ok (.success config₁ (Value.bool b)) w_mid ∧
    ((b = false ∧ v = Value.unit ∧ config_final = config₁ ∧ w₁ = w_mid) ∨
     (b = true ∧ ∃ (config₂ : Config) (v₂ : Value) (w_mid2 : Void IO.RealWorld),
        LeanPoison.beval (fuel - 1) config₁ e2 verbose w_mid =
            EST.Out.ok (.success config₂ v₂) w_mid2 ∧
        LeanPoison.beval (fuel - 1) config₂ (Expr.kwhile e1 e2) verbose w_mid2 =
            EST.Out.ok (.success config_final v) w₁)) := by
  sorry

-- ================================================================
-- World-Free Termination Inversion Lemmas
-- ================================================================

-- These lemmas extract config and value information from terminatesTo
-- (world-free termination) for I/O-free expression forms.

-- Helper: apply IO equality at default world to extract underlying equality
private lemma pure_eq_pure_imp {α : Type} (a b : α) :
    (pure a : IO α) = pure b → a = b := by
  intro h
  have heq := congrArg (fun f => f LeanProofs.defaultWorld) h
  injection heq

/-- Inversion lemma for terminatesTo on number literals. -/
lemma terminatesTo_num_inv' (n : Int) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.num n) c₀ c₁ v → c₁ = c₀ ∧ v = Value.num n := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on boolean literals. -/
lemma terminatesTo_bool_inv' (b : Bool) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.bool b) c₀ c₁ v → c₁ = c₀ ∧ v = Value.bool b := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on unit. -/
lemma terminatesTo_unit_inv' (c₀ c₁ : Config) (v : Value) :
    terminatesTo Expr.unit c₀ c₁ v → c₁ = c₀ ∧ v = Value.unit := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on string literals. -/
lemma terminatesTo_str_inv' (s : String) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.str s) c₀ c₁ v → c₁ = c₀ ∧ v = Value.str s := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

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
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      cases hlookup : c₀.varEnv.lookup x with
      | none =>
          simp only [hlookup] at hbeval
          have := pure_eq_pure_imp _ _ hbeval
          cases this
      | some v' =>
          simp only [hlookup] at hbeval
          have heq := pure_eq_pure_imp _ _ hbeval
          injection heq with hcfg hval
          refine ⟨v', ?_, hcfg.symm, hval.symm⟩
          rw [← hlookup]

/-- Inversion lemma for terminatesTo on fn (regular function). -/
lemma terminatesTo_fn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.fn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.closure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on pfn (predicated function). -/
lemma terminatesTo_pfn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.pfn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.peClosure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero =>
      simp only [LeanPoison.beval] at hbeval
      have := pure_eq_pure_imp _ _ hbeval
      cases this
  | succ fuel' =>
      simp only [LeanPoison.beval, pure] at hbeval
      have heq := pure_eq_pure_imp _ _ hbeval
      injection heq with hcfg hval
      exact ⟨hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on unaryop.
    Extracts the sub-expression evaluation and operation application.
    Uses IOFree to bridge world-indexed structure lemma to world-free result. -/
lemma terminatesTo_unaryop_inv' (op : UnaryOp) (e : Expr) (c₀ c₁ : Config) (v : Value) :
    IOFree (Expr.unaryop op e) →
    terminatesTo (Expr.unaryop op e) c₀ c₁ v →
    ∃ c₁' v', terminatesTo e c₀ c₁' v' ∧
              LeanPoison.evalUnaryOp op v' = some v ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  -- Apply at defaultWorld to get world-indexed equation
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  -- Use world-indexed structure lemma
  have hstruct := bevalUnaryOp_structure op e fuel verbose c₀ c₁ v w w heval_w
  rcases hstruct with ⟨cfg', v', hbeval_e, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  -- Convert sub-expression back to terminatesTo using IOFree
  have hio_e : IOFree e := by cases hio; assumption
  have hpure_e : LeanPoison.beval (fuel - 1) c₀ e verbose = pure (.success cfg' v') :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e verbose (.success cfg' v') w hio_e hbeval_e
  exact ⟨cfg', v', ⟨fuel - 1, verbose, hpure_e⟩, hevalOp, hmem.symm, hvar.symm, hnext.symm, hpure_mode.symm⟩

/-- Inversion lemma for terminatesTo on newRef.
    Extracts the sub-expression evaluation and allocation info. -/
lemma terminatesTo_newRef_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    IOFree (Expr.newRef e) →
    terminatesTo (Expr.newRef e) c₀ c₁ v →
    ∃ (c₁' : Config) (n : Int), terminatesTo e c₀ c₁' (Value.num n) ∧
              v = Value.loc c₁'.nextAddr ∧
              c₁.memory = c₁'.memory.insert c₁'.nextAddr n ∧
              c₁.nextAddr = c₁'.nextAddr + 1 ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.pureMode = c₁'.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalNewRef_structure e fuel verbose c₀ c₁ v w w heval_w
  rcases hstruct with ⟨cfg', n, a, hbeval_e, ha_eq, hmem, hnext, hvar, hpure_mode, hv⟩
  have hio_e : IOFree e := by cases hio; assumption
  have hpure_e : LeanPoison.beval (fuel - 1) c₀ e verbose = pure (.success cfg' (Value.num n)) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e verbose (.success cfg' (Value.num n)) w hio_e hbeval_e
  refine ⟨cfg', n, ⟨fuel - 1, verbose, hpure_e⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, ha_eq]
  · -- hmem : c₁.memory = cfg'.memory.update a n
    -- Need: c₁.memory = cfg'.memory.insert cfg'.nextAddr n
    -- Memory.update is defined as m.insert, so they're definitionally equal
    simp only [hmem, ha_eq, Memory.update]
  · exact hnext
  · exact hvar
  · exact hpure_mode

/-- Helper lemma: pureMode is preserved through evaluation of IOFree expressions.
    This is proven by structural induction, using inversion lemmas for base cases
    and recursive calls for compound cases. -/
lemma terminatesTo_IOFree_preserves_pureMode (e : Expr) (c₀ c₁ : Config) (v : Value) :
    IOFree e →
    terminatesTo e c₀ c₁ v →
    c₁.pureMode = c₀.pureMode := by
  intro hio ht
  -- Use structural case analysis on e to apply appropriate inversion lemmas
  -- Recursive calls are on sub-expressions, so termination is guaranteed
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
    rcases h with ⟨v', _, hcfg, _⟩
    rw [hcfg]
  | fn x paramType body returnType =>
    have h := terminatesTo_fn_inv' x paramType body returnType c₀ c₁ v ht
    rw [h.1]
  | pfn x paramType body returnType =>
    have h := terminatesTo_pfn_inv' x paramType body returnType c₀ c₁ v ht
    rw [h.1]
  | unaryop op e' =>
    have hio' : IOFree e' := by cases hio; assumption
    have h := terminatesTo_unaryop_inv' op e' c₀ c₁ v hio ht
    rcases h with ⟨c₁', v', ht', _, _, _, _, hpure_mode⟩
    have hrec := terminatesTo_IOFree_preserves_pureMode e' c₀ c₁' v' hio' ht'
    rw [hpure_mode, hrec]
  | op e₁ op' e₂ =>
    have hio₁ : IOFree e₁ := by cases hio; assumption
    have hio₂ : IOFree e₂ := by cases hio; assumption
    -- Use structure lemma and prove recursively for sub-expressions
    rcases ht with ⟨fuel, verbose, hpure⟩
    let w := LeanProofs.defaultWorld
    have heval_w := LeanProofs.evalAtWorld_eq w hpure
    have hstruct := bevalOp_structure e₁ e₂ op' fuel verbose c₀ c₁ v w w heval_w
    rcases hstruct with ⟨cfg₁, cfg₂, v₁, v₂, w_mid, hbeval_e1, hbeval_e2, _, hmem, hvar, hnext, hpure_mode_final⟩
    have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
    subst hw_mid_eq
    have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
      beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
    have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success cfg₂ v₂) :=
      beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success cfg₂ v₂) w hio₂ hbeval_e2
    have h_cfg2_eq : cfg₂ = c₁ := by
      cases cfg₂; cases c₁
      simp only [Config.mk.injEq]
      exact ⟨hmem, hvar, hnext, hpure_mode_final⟩
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₁ cfg₂ v₂ hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    -- From h_cfg2_eq: cfg₂ = c₁, so cfg₂.pureMode = c₁.pureMode
    -- From hrec₂: cfg₂.pureMode = cfg₁.pureMode
    -- From hrec₁: cfg₁.pureMode = c₀.pureMode
    -- So: c₁.pureMode = cfg₂.pureMode = cfg₁.pureMode = c₀.pureMode
    rw [← hpure_mode_final, hrec₂, hrec₁]
  | seq e₁ e₂ =>
    have hio₁ : IOFree e₁ := by cases hio; assumption
    have hio₂ : IOFree e₂ := by cases hio; assumption
    -- Use structure lemma and prove recursively for sub-expressions
    rcases ht with ⟨fuel, verbose, hpure⟩
    let w := LeanProofs.defaultWorld
    have heval_w := LeanProofs.evalAtWorld_eq w hpure
    have hstruct := bevalSeq_structure e₁ e₂ fuel verbose c₀ c₁ v w w heval_w
    rcases hstruct with ⟨cfg₁, v₁, w_mid, hbeval_e1, hbeval_e2⟩
    have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
    subst hw_mid_eq
    have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
      beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
    have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success c₁ v) :=
      beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success c₁ v) w hio₂ hbeval_e2
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₁ c₁ v hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    rw [hrec₂, hrec₁]
  | vlet x e₁ e₂ =>
    have hio₁ : IOFree e₁ := by cases hio; assumption
    have hio₂ : IOFree e₂ := by cases hio; assumption
    -- Use structure lemma and prove recursively for sub-expressions
    rcases ht with ⟨fuel, verbose, hpure⟩
    let w := LeanProofs.defaultWorld
    have heval_w := LeanProofs.evalAtWorld_eq w hpure
    have hstruct := bevalVlet_structure x e₁ e₂ fuel verbose c₀ c₁ v w w heval_w
    rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v₁, w_mid, hbeval_e1, hcfg2_eq, hbeval_e2, hcfg_final⟩
    have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
    subst hw_mid_eq
    have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
      beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
    have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₂ e₂ verbose = pure (.success cfg₃ v) :=
      beval_IOFree_eq_pure (fuel - 1) cfg₂ e₂ verbose (.success cfg₃ v) w hio₂ hbeval_e2
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₂ cfg₃ v hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    -- From hcfg_final: c₁ = { cfg₃ with varEnv := cfg₁.varEnv }
    -- So c₁.pureMode = cfg₃.pureMode
    have h_pure_final : c₁.pureMode = cfg₃.pureMode := by
      rw [hcfg_final]
    -- From hcfg2_eq: cfg₂ = { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ }
    -- So cfg₂.pureMode = cfg₁.pureMode
    have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by
      rw [hcfg2_eq]
    -- Chain: c₁.pureMode = cfg₃.pureMode = cfg₂.pureMode = cfg₁.pureMode = c₀.pureMode
    rw [h_pure_final, hrec₂, h_pure_cfg2, hrec₁]
  | deref e' =>
    have hio' : IOFree e' := by cases hio; assumption
    -- Use structure lemma and prove recursively for sub-expression
    rcases ht with ⟨fuel, verbose, hpure⟩
    let w := LeanProofs.defaultWorld
    have heval_w := LeanProofs.evalAtWorld_eq w hpure
    have hstruct := bevalDeref_structure e' fuel verbose c₀ c₁ v w w heval_w
    rcases hstruct with ⟨cfg', a, n, hbeval_e, _, _, _, _, _, hpure_mode⟩
    have hpure_e : LeanPoison.beval (fuel - 1) c₀ e' verbose = pure (.success cfg' (Value.loc a)) :=
      beval_IOFree_eq_pure (fuel - 1) c₀ e' verbose (.success cfg' (Value.loc a)) w hio' hbeval_e
    have hrec := terminatesTo_IOFree_preserves_pureMode e' c₀ cfg' (Value.loc a) hio' ⟨fuel - 1, verbose, hpure_e⟩
    rw [hpure_mode, hrec]
  | newRef e' =>
    have hio' : IOFree e' := by cases hio; assumption
    have h := terminatesTo_newRef_inv' e' c₀ c₁ v hio ht
    rcases h with ⟨c₁', _, ht', _, _, _, _, hpure_mode'⟩
    have hrec := terminatesTo_IOFree_preserves_pureMode e' c₀ c₁' (Value.num _) hio' ht'
    rw [hpure_mode', hrec]
  | assign e₁ e₂ =>
    have hio₁ : IOFree e₁ := by cases hio; assumption
    have hio₂ : IOFree e₂ := by cases hio; assumption
    -- For assign, we need to use the structure lemma directly since terminatesTo_assign_inv' is defined later
    rcases ht with ⟨fuel, verbose, hpure⟩
    let w := LeanProofs.defaultWorld
    have heval_w := LeanProofs.evalAtWorld_eq w hpure
    have hstruct := bevalAssign_structure e₁ e₂ fuel verbose c₀ c₁ v w w heval_w
    rcases hstruct with ⟨cfg₁, cfg₁', a, n, w_mid, hbeval_e1, hbeval_e2, _, _, _, _, hpure_mode'⟩
    have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
    subst hw_mid_eq
    have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ (Value.loc a)) :=
      beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ (Value.loc a)) w hio₁ hbeval_e1
    have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success cfg₁' (Value.num n)) :=
      beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success cfg₁' (Value.num n)) w hio₂ hbeval_e2
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ (Value.loc a) hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₁ cfg₁' (Value.num n) hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    -- From hpure_mode': c₁.pureMode = cfg₁'.pureMode
    -- From hrec₂: cfg₁'.pureMode = cfg₁.pureMode
    -- From hrec₁: cfg₁.pureMode = c₀.pureMode
    -- So: c₁.pureMode = cfg₁'.pureMode = cfg₁.pureMode = c₀.pureMode
    rw [hpure_mode', hrec₂, hrec₁]
  | printInt _ | printString _ | rand _ | frand _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
    cases hio  -- These cases are not IOFree, so this branch is unreachable
  | kwhile _ _ | app _ _ | ite _ _ _ =>
    -- These cases can be IOFree but we don't have inversion lemmas for them yet
    -- For now, we use sorry; these can be proven when the corresponding inversion lemmas are added
    sorry

/-- Inversion lemma for terminatesTo on deref.
    Note: pureMode is preserved through evaluation. -/
lemma terminatesTo_deref_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    IOFree (Expr.deref e) →
    terminatesTo (Expr.deref e) c₀ c₁ v →
    ∃ (c₁' : Config) (a : Address) (n : Int), terminatesTo e c₀ c₁' (Value.loc a) ∧
              c₁'.memory.lookup a = some n ∧
              v = Value.num n ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode ∧
              c₁'.pureMode = c₀.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalDeref_structure e fuel verbose c₀ c₁ v w w heval_w
  rcases hstruct with ⟨cfg', a, n, hbeval_e, hlookup, hv, hmem, hvar, hnext, hpure_mode⟩
  have hio_e : IOFree e := by cases hio; assumption
  have hpure_e : LeanPoison.beval (fuel - 1) c₀ e verbose = pure (.success cfg' (Value.loc a)) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e verbose (.success cfg' (Value.loc a)) w hio_e hbeval_e
  refine ⟨cfg', a, n, ⟨fuel - 1, verbose, hpure_e⟩, hlookup, hv, hmem, hvar, hnext, hpure_mode, ?_⟩
  -- cfg'.pureMode = c₀.pureMode: pureMode preserved by sub-expression evaluation
  exact terminatesTo_IOFree_preserves_pureMode e c₀ cfg' (Value.loc a) hio_e ⟨fuel - 1, verbose, hpure_e⟩

/-- Inversion lemma for terminatesTo on binary op.
    Note: c₁.pureMode = c₀.pureMode = c₂.pureMode is preserved through evaluation. -/
lemma terminatesTo_op_inv' (e₁ : Expr) (op : Op) (e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    IOFree (Expr.op e₁ op e₂) →
    terminatesTo (Expr.op e₁ op e₂) c₀ c₂ v →
    ∃ c₁ v₁ v₂, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ c₁ c₂ v₂ ∧
                LeanPoison.evalOp op v₁ v₂ = some v ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalOp_structure e₁ e₂ op fuel verbose c₀ c₂ v w w heval_w
  rcases hstruct with ⟨cfg₁, cfg₂, v₁, v₂, w_mid, hbeval_e1, hbeval_e2, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  have hio₁ : IOFree e₁ := by cases hio; assumption
  have hio₂ : IOFree e₂ := by cases hio; assumption
  -- World preservation: w_mid = w
  have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
  subst hw_mid_eq
  have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
  have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success cfg₂ v₂) :=
    beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success cfg₂ v₂) w hio₂ hbeval_e2
  -- cfg₂ has same fields as c₂ (from structure equalities)
  -- The structure lemma says config₂.X = config₃.X where config₃ = c₂
  -- So cfg₂.X = c₂.X, meaning terminatesTo e₂ cfg₁ cfg₂ v₂ but we need to c₂
  -- Actually the structure shows cfg₂ is the intermediate and c₂ (= config₃) is the final
  -- But for op, the final config IS the result of e₂ evaluation (no modification)
  -- So the terminatesTo e₂ cfg₁ c₂ v₂ should work if cfg₂ fields match c₂
  have hpure_e2' : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success c₂ v₂) := by
    -- cfg₂ and c₂ have same fields, so .success cfg₂ v₂ = .success c₂ v₂
    have h_cfg2_eq : cfg₂ = c₂ := by
      cases cfg₂; cases c₂
      simp only [Config.mk.injEq]
      exact ⟨hmem, hvar, hnext, hpure_mode⟩
    rw [← h_cfg2_eq]
    exact hpure_e2
  refine ⟨cfg₁, v₁, v₂, ⟨fuel - 1, verbose, hpure_e1⟩, ⟨fuel - 1, verbose, hpure_e2'⟩, hevalOp, ?_, ?_⟩
  · -- c₁.pureMode = c₀.pureMode: pureMode preserved by e₁ evaluation
    exact terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
  · -- c₂.pureMode = c₀.pureMode: pureMode preserved through both evaluations
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₁ cfg₂ v₂ hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    -- From hpure_mode: cfg₂.pureMode = c₂.pureMode
    -- From hrec₂: cfg₂.pureMode = cfg₁.pureMode
    -- From hrec₁: cfg₁.pureMode = c₀.pureMode
    -- So: c₂.pureMode = cfg₂.pureMode = cfg₁.pureMode = c₀.pureMode
    rw [hpure_mode.symm, hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on seq.
    Note: pureMode is preserved through evaluation. -/
lemma terminatesTo_seq_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    IOFree (Expr.seq e₁ e₂) →
    terminatesTo (Expr.seq e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁, terminatesTo e₁ c₀ c₁ v₁ ∧
             terminatesTo e₂ c₁ c₂ v ∧
             c₁.pureMode = c₀.pureMode ∧
             c₂.pureMode = c₀.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalSeq_structure e₁ e₂ fuel verbose c₀ c₂ v w w heval_w
  rcases hstruct with ⟨cfg₁, v₁, w_mid, hbeval_e1, hbeval_e2⟩
  have hio₁ : IOFree e₁ := by cases hio; assumption
  have hio₂ : IOFree e₂ := by cases hio; assumption
  -- World preservation: w_mid = w
  have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
  subst hw_mid_eq
  have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
  have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success c₂ v) :=
    beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success c₂ v) w hio₂ hbeval_e2
  refine ⟨cfg₁, v₁, ⟨fuel - 1, verbose, hpure_e1⟩, ⟨fuel - 1, verbose, hpure_e2⟩, ?_, ?_⟩
  · -- c₁.pureMode = c₀.pureMode: pureMode preserved by e₁ evaluation
    exact terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
  · -- c₂.pureMode = c₀.pureMode: pureMode preserved through both evaluations
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₁ c₂ v hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    rw [hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on vlet.
    Note: e₂ evaluates to config₃, then the final c₂ restores the original varEnv.
    pureMode is preserved through evaluation. -/
lemma terminatesTo_vlet_inv' (x : Name) (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    IOFree (Expr.vlet x e₁ e₂) →
    terminatesTo (Expr.vlet x e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁ c₃, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ { c₁ with varEnv := c₁.varEnv.update x v₁ } c₃ v ∧
                c₂ = { c₃ with varEnv := c₁.varEnv } ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalVlet_structure x e₁ e₂ fuel verbose c₀ c₂ v w w heval_w
  rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v₁, w_mid, hbeval_e1, hcfg2_eq, hbeval_e2, hcfg_final⟩
  have hio₁ : IOFree e₁ := by cases hio; assumption
  have hio₂ : IOFree e₂ := by cases hio; assumption
  -- World preservation: w_mid = w
  have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
  subst hw_mid_eq
  have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ v₁) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ v₁) w hio₁ hbeval_e1
  -- For e₂, the input config is cfg₂ = { cfg₁ with varEnv := ... }
  have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₂ e₂ verbose = pure (.success cfg₃ v) :=
    beval_IOFree_eq_pure (fuel - 1) cfg₂ e₂ verbose (.success cfg₃ v) w hio₂ hbeval_e2
  -- Need to show terminatesTo e₂ {cfg₁ with varEnv:=...} cfg₃ v
  -- hcfg2_eq : cfg₂ = { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ }
  -- hpure_e2 : beval ... cfg₂ e₂ ... = pure (.success cfg₃ v)
  -- So we can substitute cfg₂ with the expanded form
  have hpure_e2' : LeanPoison.beval (fuel - 1) { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ } e₂ verbose =
      pure (.success cfg₃ v) := by
    rw [← hcfg2_eq]; exact hpure_e2
  refine ⟨cfg₁, v₁, cfg₃, ⟨fuel - 1, verbose, hpure_e1⟩, ⟨fuel - 1, verbose, hpure_e2'⟩, hcfg_final, ?_, ?_⟩
  · -- c₁.pureMode = c₀.pureMode: pureMode preserved by e₁ evaluation
    exact terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
  · -- c₂.pureMode = c₀.pureMode: pureMode preserved through both evaluations
    have hrec₁ := terminatesTo_IOFree_preserves_pureMode e₁ c₀ cfg₁ v₁ hio₁ ⟨fuel - 1, verbose, hpure_e1⟩
    have hrec₂ := terminatesTo_IOFree_preserves_pureMode e₂ cfg₂ cfg₃ v hio₂ ⟨fuel - 1, verbose, hpure_e2⟩
    -- From hcfg_final: c₂ = { cfg₃ with varEnv := cfg₁.varEnv }
    -- So c₂.pureMode = cfg₃.pureMode
    have h_pure_final : c₂.pureMode = cfg₃.pureMode := by
      rw [hcfg_final]
    -- From hcfg2_eq: cfg₂ = { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ }
    -- So cfg₂.pureMode = cfg₁.pureMode
    have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by
      rw [hcfg2_eq]
    -- Goal: c₂.pureMode = c₀.pureMode
    -- From h_pure_final: c₂.pureMode = cfg₃.pureMode
    -- From hrec₂: cfg₃.pureMode = cfg₂.pureMode
    -- From h_pure_cfg2: cfg₂.pureMode = cfg₁.pureMode
    -- From hrec₁: cfg₁.pureMode = c₀.pureMode
    -- Chain: c₂.pureMode = cfg₃.pureMode = cfg₂.pureMode = cfg₁.pureMode = c₀.pureMode
    rw [h_pure_final]
    rw [hrec₂]
    rw [h_pure_cfg2]
    exact hrec₁

/-- Inversion lemma for terminatesTo on assign. -/
lemma terminatesTo_assign_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    IOFree (Expr.assign e₁ e₂) →
    terminatesTo (Expr.assign e₁ e₂) c₀ c₂ v →
    ∃ (c₁ c₁' : Config) (a : Address) (n : Int),
                           terminatesTo e₁ c₀ c₁ (Value.loc a) ∧
                           terminatesTo e₂ c₁ c₁' (Value.num n) ∧
                           v = Value.unit ∧
                           c₂.memory = c₁'.memory.insert a n ∧
                           c₂.varEnv = c₁'.varEnv ∧
                           c₂.nextAddr = c₁'.nextAddr ∧
                           c₂.pureMode = c₁'.pureMode := by
  intro hio ⟨fuel, verbose, hpure⟩
  let w := LeanProofs.defaultWorld
  have heval_w := LeanProofs.evalAtWorld_eq w hpure
  have hstruct := bevalAssign_structure e₁ e₂ fuel verbose c₀ c₂ v w w heval_w
  rcases hstruct with ⟨cfg₁, cfg₁', a, n, w_mid, hbeval_e1, hbeval_e2, hv, hmem, hvar, hnext, hpure_mode⟩
  have hio₁ : IOFree e₁ := by cases hio; assumption
  have hio₂ : IOFree e₂ := by cases hio; assumption
  -- World preservation: w_mid = w
  have hw_mid_eq : w_mid = w := beval_IOFree_preserves_world (fuel - 1) c₀ e₁ verbose _ w w_mid hio₁ hbeval_e1
  subst hw_mid_eq
  have hpure_e1 : LeanPoison.beval (fuel - 1) c₀ e₁ verbose = pure (.success cfg₁ (Value.loc a)) :=
    beval_IOFree_eq_pure (fuel - 1) c₀ e₁ verbose (.success cfg₁ (Value.loc a)) w hio₁ hbeval_e1
  have hpure_e2 : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = pure (.success cfg₁' (Value.num n)) :=
    beval_IOFree_eq_pure (fuel - 1) cfg₁ e₂ verbose (.success cfg₁' (Value.num n)) w hio₂ hbeval_e2
  refine ⟨cfg₁, cfg₁', a, n, ⟨fuel - 1, verbose, hpure_e1⟩, ⟨fuel - 1, verbose, hpure_e2⟩, hv, ?_, ?_, ?_, ?_⟩
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
            cases h_cfg_eq
            simp
          · -- isPure = false
            injection h_eq with h_result h_world
            injection h_result with h_cfg_eq h_val_eq
            have h_next_eq : finalConfig.nextAddr = evalConfig.nextAddr := by
              cases h_cfg_eq
              rfl
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
              cases h_pure : Expr.toPExpr? body with
              | none =>
                  simp [h_pure, pure] at h_eq
                  injection h_eq with h_result h_world
                  injection h_result
              | some _ =>
                  simp [h_pure] at h_eq
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
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose config₀ config₁ v w₀ w₁ h_eq
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, w_mid, hbeval1, hbeval2, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 :=
              IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 ⟨w₀, w_mid, hbeval1⟩
            have hle2 :=
              IH_converted fuel' h_fuel e2 cfg₁1 cfg₁2 v2 ⟨w_mid, w₁, hbeval2⟩
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
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose config₀ config₁ v w₀ w₁ h_eq
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 ⟨w₀, w₁, hbeval1⟩
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
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            have hstruct :=
              bevalNewRef_structure e1 (fuel' + 1) verbose config₀ config₁ v w₀ w₁ h_eq
            rcases hstruct with ⟨cfg₁1, n, a, hbeval1, _ha, _hmem, h_next, _hvar, _hval⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 (Value.num n) ⟨w₀, w₁, hbeval1⟩
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
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            have hstruct :=
              bevalSeq_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v w₀ w₁ h_eq
            rcases hstruct with ⟨cfg₁1, v1, w_mid, hbeval1, hbeval2⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 ⟨w₀, w_mid, hbeval1⟩
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁1 config₁ v ⟨w_mid, w₁, hbeval2⟩
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
            rcases h_eval with ⟨w₀, w₁, h_eq⟩
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose config₀ config₁ v w₀ w₁ h_eq
            rcases hstruct with ⟨cfg₁1, cfg₁2, cfg₁3, v1, w_mid, hbeval1, hcfg2, hbeval2, hcfg_final⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 ⟨w₀, w_mid, hbeval1⟩
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁2 cfg₁3 v ⟨w_mid, w₁, hbeval2⟩
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

/-- Next address is monotone for terminating evaluations (world-indexed). -/
lemma terminatesToW_nextAddr_mono (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    ∀ (w₀ w₁ : Void IO.RealWorld), terminatesToW w₀ w₁ e cfg₀ cfg₁ v →
    cfg₀.nextAddr ≤ cfg₁.nextAddr := by
  intro w₀ w₁ hterm
  rcases hterm with ⟨fuel, verbose, hbeval⟩
  exact beval_nextAddr_mono e fuel verbose cfg₀ cfg₁ v ⟨w₀, w₁, hbeval⟩

/-- Next address is monotone for terminating evaluations (world-free). -/
lemma terminatesTo_nextAddr_mono (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v → cfg₀.nextAddr ≤ cfg₁.nextAddr := by
  intro ⟨fuel, verbose, hbeval⟩
  -- Convert world-free to world-indexed by applying at defaultWorld
  have hterm_w : terminatesToW LeanProofs.defaultWorld LeanProofs.defaultWorld e cfg₀ cfg₁ v := by
    refine ⟨fuel, verbose, ?_⟩
    exact LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval
  exact terminatesToW_nextAddr_mono e cfg₀ cfg₁ v LeanProofs.defaultWorld LeanProofs.defaultWorld hterm_w

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

/-- Updating a well-formed varEnv with a well-formed value preserves well-formedness. -/
private lemma wfVarEnv_update (next : Address) (env : VarEnv) (x : Name) (v : Value) :
    wfVarEnv next env →
    wfValue next v →
    wfVarEnv next (VarEnv.update env x v) := by
  intro hwf_env hwf_v
  -- VarEnv.update adds the binding to the front of the list
  exact wfVarEnv.cons x v env hwf_v hwf_env

-- ================================================================
-- Pure evaluation preserves nextAddr (used for pure closures)
-- ================================================================

/-- If a pure expression evaluates successfully in pureMode, it does not change nextAddr. -/
private lemma beval_pure_config_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (w₀ w₁ : Void IO.RealWorld) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose w₀ = EST.Out.ok (.success cfg₁ v) w₁ →
    cfg₁.nextAddr = cfg₀.nextAddr ∧ cfg₁.pureMode = true := by
  revert e cfg₀ cfg₁ v verbose w₀ w₁ pe
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e cfg₀ cfg₁ v verbose w₀ w₁ pe h_pure h_pm hbeval
    cases fuel with
    | zero =>
        unfold LeanPoison.beval at hbeval
        simp at hbeval
        cases hbeval
    | succ fuel' =>
        cases e with
        | unit =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            injection hbeval with h_res h_world
            injection h_res with h_cfg_eq h_val_eq
            subst h_cfg_eq
            exact ⟨rfl, h_pm⟩
        | str s =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            injection hbeval with h_res h_world
            injection h_res with h_cfg_eq h_val_eq
            subst h_cfg_eq
            exact ⟨rfl, h_pm⟩
        | num n =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            injection hbeval with h_res h_world
            injection h_res with h_cfg_eq h_val_eq
            subst h_cfg_eq
            exact ⟨rfl, h_pm⟩
        | bool b =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            injection hbeval with h_res h_world
            injection h_res with h_cfg_eq h_val_eq
            subst h_cfg_eq
            exact ⟨rfl, h_pm⟩
        | var x =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            cases h_lookup : cfg₀.varEnv.lookup x with
            | some v' =>
                simp [h_lookup] at hbeval
                injection hbeval with h_res h_world
                injection h_res with h_cfg_eq h_val_eq
                subst h_cfg_eq
                exact ⟨rfl, h_pm⟩
            | none =>
                simp [h_lookup] at hbeval
                cases hbeval
        | op e1 op e2 =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, w_mid, hbeval1', hbeval2', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none =>
                simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none =>
                    simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h_pure_op : (e1.op op e2).toPExpr? = some (pe1.op op pe2) := by
                      simp [Expr.toPExpr?, h_pe1, h_pe2]
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose w₀ w_mid pe1 h_pe1 h_pm hbeval1'
                    have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₁2 v2 verbose w_mid w₁ pe2 h_pe2 h1.2 hbeval2'
                    constructor
                    · calc
                        cfg₁.nextAddr = cfg₁2.nextAddr := h_next.symm
                        _ = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · calc
                        cfg₁.pureMode = cfg₁2.pureMode := h_pure_eq.symm
                        _ = true := h2.2
        | unaryop op e1 =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none =>
                simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                subst h_pure
                have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose w₀ w₁ pe1 h_pe1 h_pm hbeval1'
                constructor
                · calc
                    cfg₁.nextAddr = cfg₁1.nextAddr := h_next.symm
                    _ = cfg₀.nextAddr := h1.1
                · calc
                    cfg₁.pureMode = cfg₁1.pureMode := h_pure_eq.symm
                    _ = true := h1.2
        | ite e1 e2 e3 =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            simp [bind, Bind.bind, EST.bind] at hbeval
            split at hbeval
            · next h_result1 h_state1 h_beval1 =>
              cases h_result1 with
              | success cfg₁1 v₁ =>
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                simp [Expr.toPExpr?] at h_pure
                cases h_pe1 : Expr.toPExpr? e1 with
                | none =>
                    simp [h_pe1] at h_pure
                | some pe1 =>
                    simp [h_pe1] at h_pure
                    cases h_pe2 : Expr.toPExpr? e2 with
                    | none =>
                        simp [h_pe2] at h_pure
                    | some pe2 =>
                        simp [h_pe2] at h_pure
                        cases h_pe3 : Expr.toPExpr? e3 with
                        | none =>
                            simp [h_pe3] at h_pure
                        | some pe3 =>
                            simp [h_pe3] at h_pure
                            subst h_pure
                            have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v₁ verbose w₀ h_state1 pe1 h_pe1 h_pm h_beval1
                            cases v₁ with
                            | bool b =>
                                cases b with
                                | true =>
                                    simp [EST.bind] at hbeval
                                    split at hbeval
                                    · next h_result2 h_state2 h_beval2 =>
                                      split at hbeval
                                      · next cfg₂ v₂ =>
                                        injection hbeval with h_res h_world
                                        injection h_res with h_cfg_eq h_val_eq
                                        subst h_cfg_eq
                                        have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₂ v₂ verbose h_state1 h_state2 pe2 h_pe2 h1.2 h_beval2
                                        constructor
                                        · calc
                                            cfg₂.nextAddr = cfg₁1.nextAddr := h2.1
                                            _ = cfg₀.nextAddr := h1.1
                                        · simpa using h2.2
                                      · next =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                      · next msg =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                    · next =>
                                      cases hbeval
                                | false =>
                                    simp [EST.bind] at hbeval
                                    split at hbeval
                                    · next h_result3 h_state3 h_beval3 =>
                                      split at hbeval
                                      · next cfg₂ v₃ =>
                                        injection hbeval with h_res h_world
                                        injection h_res with h_cfg_eq h_val_eq
                                        subst h_cfg_eq
                                        have h3 := IH fuel' h_fuel e3 cfg₁1 cfg₂ v₃ verbose h_state1 h_state3 pe3 h_pe3 h1.2 h_beval3
                                        constructor
                                        · calc
                                            cfg₂.nextAddr = cfg₁1.nextAddr := h3.1
                                            _ = cfg₀.nextAddr := h1.1
                                        · simpa using h3.2
                                      · next =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                      · next msg =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                    · next =>
                                      cases hbeval
                            | _ =>
                              simp [pure] at hbeval
                              cases hbeval
              | outOfFuel =>
                simp [pure] at hbeval
                cases hbeval
              | runtimeError msg =>
                simp [pure] at hbeval
                cases hbeval
            · next h_error1 h_state1 =>
              injection hbeval
        | deref e1 =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            simp [bind, Bind.bind, EST.bind] at hbeval
            split at hbeval
            · next h_result1 h_state1 h_beval1 =>
              split at hbeval
              · next cfg₁1 loc_val =>
                cases h_mem : cfg₁1.memory[loc_val]? with
                | none =>
                    simp [h_mem] at hbeval
                    cases hbeval
                | some _ =>
                    simp [h_mem] at hbeval
                    injection hbeval with h_res h_world
                    injection h_res with h_cfg_eq h_val_eq
                    subst h_cfg_eq
                    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                    simp [Expr.toPExpr?] at h_pure
                    cases h_pe1 : Expr.toPExpr? e1 with
                    | none =>
                        simp [h_pe1] at h_pure
                    | some pe1 =>
                        simp [h_pe1] at h_pure
                        subst h_pure
                        have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 (Value.loc loc_val) verbose w₀ h_state1 pe1 h_pe1 h_pm h_beval1
                        exact h1
              · next h_result1_error =>
                simp [pure] at hbeval
                cases hbeval
              · next msg =>
                simp [pure] at hbeval
                cases hbeval
              · next h_val =>
                simp [pure] at hbeval
                cases hbeval
            · next h_error1 h_state1 =>
              injection hbeval
        | vlet x e1 e2 =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
            rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, w_mid, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none =>
                simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none =>
                    simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose w₀ w_mid pe1 h_pe1 h_pm hbeval1
                    have h_pm2 : cfg₂.pureMode = true := by
                      simpa [hcfg2_eq] using h1.2
                    have h2 := IH fuel' h_fuel e2 cfg₂ cfg₃ v verbose w_mid w₁ pe2 h_pe2 h_pm2 hbeval2
                    subst hcfg2_eq hcfg_final_eq
                    constructor
                    · calc
                        cfg₃.nextAddr = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · simpa using h2.2
        | app e1 e2 =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            simp [bind, Bind.bind, EST.bind] at hbeval
            split at hbeval
            · next h_result2 h_state2 h_beval2 =>
              cases h_result2 with
              | success cfg₁' v₂ =>
                have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
                simp [Expr.toPExpr?] at h_pure
                cases h_pe1 : Expr.toPExpr? e1 with
                | none =>
                    simp [h_pe1] at h_pure
                | some pe1 =>
                    simp [h_pe1] at h_pure
                    cases h_pe2 : Expr.toPExpr? e2 with
                    | none =>
                        simp [h_pe2] at h_pure
                    | some pe2 =>
                        simp [h_pe2] at h_pure
                        subst h_pure
                        have h2 := IH fuel' h_fuel e2 cfg₀ cfg₁' v₂ verbose w₀ h_state2 pe2 h_pe2 h_pm h_beval2
                        simp [EST.bind] at hbeval
                        split at hbeval
                        · next h_result1 h_state1 h_beval1 =>
                          split at hbeval
                          · next cfg₂ x body env =>
                            have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.closure x body env) verbose h_state2 h_state1 pe1 h_pe1 h2.2 h_beval1
                            -- impure closure: impossible in pureMode
                            split at hbeval
                            · next _ =>
                              injection hbeval with h_res h_world
                              injection h_res
                            · next h_notPureMode =>
                              have : False := by
                                simpa [h_notPureMode] using h1.2
                              cases this
                          · next cfg₂ x body env =>
                            cases h_pure_body : Expr.toPExpr? body with
                            | none =>
                                simp [h_pure_body, pure] at hbeval
                                injection hbeval with h_res h_world
                                injection h_res
                            | some pe_body =>
                                simp [h_pure_body] at hbeval
                                have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.peClosure x body env) verbose h_state2 h_state1 pe1 h_pe1 h2.2 h_beval1
                                cases fuel' with
                                | zero =>
                                    simp [LeanPoison.bevalFunctionBody] at hbeval
                                    injection hbeval with h_res h_world
                                    injection h_res
                                | succ fuel'' =>
                                    unfold LeanPoison.bevalFunctionBody at hbeval
                                    simp at hbeval
                                    simp [bind, Bind.bind, EST.bind] at hbeval
                                    split at hbeval
                                    · next h_body_result h_body_state h_beval_body =>
                                      split at hbeval
                                      · next evalConfig v_body =>
                                        injection hbeval with h_res h_world
                                        injection h_res with h_cfg_eq h_val_eq
                                        subst h_cfg_eq
                                        constructor
                                        · calc
                                            ({ cfg₂ with pureMode := cfg₂.pureMode } : Config).nextAddr = cfg₂.nextAddr := rfl
                                            _ = cfg₁'.nextAddr := h1.1
                                            _ = cfg₀.nextAddr := h2.1
                                        · simpa using h1.2
                                      · next =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                      · next =>
                                        simp [pure] at hbeval
                                        cases hbeval
                                    · next h_body_error h_body_state =>
                                      injection hbeval
                          · next v =>
                            simp [pure] at hbeval
                            cases hbeval
                          · next =>
                            simp [pure] at hbeval
                            cases hbeval
                          · next msg =>
                            simp [pure] at hbeval
                            cases hbeval
                        · next h_error1 h_state1 =>
                          cases hbeval
              | outOfFuel =>
                simp [pure] at hbeval
                cases hbeval
              | runtimeError msg =>
                simp [pure] at hbeval
                cases hbeval
            · next h_error2 h_state2 =>
              cases hbeval
        -- impossible cases below: not allowed by pexpr syntax
        | newRef e1
        | assign e1 e2
        | seq e1 e2
        | kwhile e1 e2
        | fn x t1 body t2
        | pfn x t1 body t2
        | rand e1
        | frand e1
        | printString e1
        | printInt e1
        | externVal t b p
        | externFn name t ret effs
        | externPfn name t ret =>
            simp [Expr.toPExpr?] at h_pure

private lemma beval_pure_nextAddr_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (w₀ w₁ : Void IO.RealWorld) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose w₀ = EST.Out.ok (.success cfg₁ v) w₁ →
    cfg₁.nextAddr = cfg₀.nextAddr := by
  intro h_pure h_pm hbeval
  exact (beval_pure_config_eq e fuel cfg₀ cfg₁ v verbose w₀ w₁ pe h_pure h_pm hbeval).1

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
    bevalNewRef_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
  rcases hstruct with ⟨cfg₁1, n, a, hbeval1, ha, hmem_eq, hnext_eq, hvar_eq, hval_eq⟩
  have hih1 := ih e1 cfg₀ cfg₁1 (Value.num n) hwf₀ w₀ w₁ hbeval1
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
  -- Expose the recursive structure
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  simp [bind, Bind.bind, EST.bind] at hbeval
  split at hbeval
  · next h_result1 h_state1 h_beval1 =>
    split at hbeval
    · next config₁' =>
      simp [EST.bind] at hbeval
      split at hbeval
      · next h_result2 h_state2 h_beval2 =>
        split at hbeval
        · next config₂ v₂ =>
          injection hbeval with h_result h_world
          injection h_result with h_eq_config h_eq_val
          subst h_eq_config h_eq_val
          have hih1 := ih e1 cfg₀ config₁' (Value.bool true) hwf₀ w₀ h_state1 h_beval1
          have hih2 := ih e2 config₁' config₂ v₂ hih1.1 h_state1 h_state2 h_beval2
          exact hih2
        · next =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
      · next h_error2 h_state2 =>
        injection hbeval
    · next config₁' =>
      simp [EST.bind] at hbeval
      split at hbeval
      · next h_result3 h_state3 h_beval3 =>
        split at hbeval
        · next config₂ v₃ =>
          injection hbeval with h_result h_world
          injection h_result with h_eq_config h_eq_val
          subst h_eq_config h_eq_val
          have hih1 := ih e1 cfg₀ config₁' (Value.bool false) hwf₀ w₀ h_state1 h_beval1
          have hih3 := ih e3 config₁' config₂ v₃ hih1.1 h_state1 h_state3 h_beval3
          exact hih3
        · next =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
      · next h_error3 h_state3 =>
        injection hbeval
    · next v =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next msg =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
  · next h_error1 h_state1 =>
    injection hbeval

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
  -- Expose the recursive structure
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  simp [bind, Bind.bind, EST.bind] at hbeval
  split at hbeval
  · next h_result1 h_state1 h_beval1 =>
    split at hbeval
    · next config' loc_val =>
      simp [EST.bind] at hbeval
      split at hbeval
      · next h_result2 h_state2 h_beval2 =>
        split at hbeval
        · next config'' n_val =>
          injection hbeval with h_result h_world
          injection h_result with h_eq_config h_eq_val
          subst h_eq_config h_eq_val
          have hih1 := ih e1 cfg₀ config' (Value.loc loc_val) hwf₀ w₀ h_state1 h_beval1
          have hih2 := ih e2 config' config'' (Value.num n_val) hih1.1 h_state1 h_state2 h_beval2
          -- Extract loc_val < config'.nextAddr from hih1
          have hloc_lt : loc_val < config'.nextAddr := by
            cases hih1.2 with
            | loc hlt => exact hlt
          -- nextAddr monotonicity for e2
          have hterm : terminatesToW h_state1 h_state2 e2 config' config'' (Value.num n_val) :=
            ⟨fuel, verbose, h_beval2⟩
          have hle_next : config'.nextAddr ≤ config''.nextAddr :=
            terminatesToW_nextAddr_mono e2 config' config'' (Value.num n_val) h_state1 h_state2 hterm
          have hloc_lt' : loc_val < config''.nextAddr :=
            Nat.lt_of_lt_of_le hloc_lt hle_next
          constructor
          · rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro addr hcontains
              by_cases h_eq : addr = loc_val
              · subst h_eq
                exact hloc_lt'
              · have hcmp : compare loc_val addr ≠ Ordering.eq := by
                  intro hcmp
                  have h_eq' : loc_val = addr := LawfulEqCmp.eq_of_compare hcmp
                  exact h_eq h_eq'.symm
                have hcontains_old : config''.memory.contains addr := by
                  simpa [Memory.update] using
                    (ExtTreeMap.contains_of_contains_insert (t := config''.memory) (k := loc_val) (a := addr) (v := n_val) hcontains hcmp)
                exact hwfmem2 addr hcontains_old
            · simpa using hwfenv2
          · exact wfValue.unit
        · next v =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
        · next =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
        · next msg =>
          simp [pure] at hbeval
          injection hbeval with h_result h_world
          injection h_result
      · next h_error2 h_state2 =>
        injection hbeval
    · next v =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next msg =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
  · next h_error1 h_state1 =>
    injection hbeval

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
  -- Expose the recursive structure
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  simp [bind, Bind.bind, EST.bind] at hbeval
  split at hbeval
  · next h_result1 h_state1 h_beval1 =>
    split at hbeval
    · next config' loc_val =>
      cases h_mem_lookup : config'.memory.get? loc_val with
      | some n =>
        have h_mem_eq : config'.memory[loc_val]? = some n := h_mem_lookup
        rw [h_mem_eq] at hbeval
        injection hbeval with h_result h_world
        injection h_result with h_eq_config h_eq_val
        subst h_eq_config h_eq_val
        have hih1 := ih e1 cfg₀ config' (Value.loc loc_val) hwf₀ w₀ h_state1 h_beval1
        constructor
        · exact hih1.1
        · exact wfValue.num n
      | none =>
        have h_mem_eq : config'.memory[loc_val]? = none := h_mem_lookup
        rw [h_mem_eq] at hbeval
        injection hbeval with h_result h_world
        injection h_result
    · next h_result1_error =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next msg =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
    · next h_val =>
      simp [pure] at hbeval
      injection hbeval with h_result h_world
      injection h_result
  · next h_error1 h_state1 =>
    injection hbeval

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
    bevalSeq_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
  rcases hstruct with ⟨cfg₁1, v1, w_mid, hbeval1, hbeval2⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀ w_mid hbeval1
  have hih2 := ih e2 cfg₁1 cfg₁ v hih1.1 w_mid w₁ hbeval2
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
  -- Expose the recursive structure
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  have hbeval_unfolded :
      LeanPoison.beval fuel cfg₀ unfolded verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁ := by
    simpa using hbeval
  exact ih unfolded cfg₀ cfg₁ v hwf₀ w₀ w₁ hbeval_unfolded

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
  have hstruct :=
    bevalVlet_structure x e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
  rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, w_mid, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
  have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀ w_mid hbeval1
  -- Show cfg₂ is well-formed (varEnv updated with v1)
  have hwf_cfg2 : wfConfig cfg₂ := by
    rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
    have hwfenv2 : wfVarEnv cfg₁1.nextAddr (cfg₁1.varEnv.update x v1) :=
      wfVarEnv_update cfg₁1.nextAddr cfg₁1.varEnv x v1 hwfenv1 hih1.2
    -- cfg₂ = { cfg₁1 with varEnv := cfg₁1.varEnv.update x v1 }
    subst hcfg2_eq
    exact ⟨hwfmem1, hwfenv2⟩
  have hih2 := ih e2 cfg₂ cfg₃ v hwf_cfg2 w_mid w₁ hbeval2
  -- Lift cfg₁1.varEnv to cfg₃.nextAddr (since e2 may allocate)
  have hterm : terminatesToW w_mid w₁ e2 cfg₂ cfg₃ v := ⟨fuel, verbose, hbeval2⟩
  have hle_next : cfg₁1.nextAddr ≤ cfg₃.nextAddr := by
    have hle := terminatesToW_nextAddr_mono e2 cfg₂ cfg₃ v w_mid w₁ hterm
    simpa [hcfg2_eq] using hle
  have hwfenv1_lift : wfVarEnv cfg₃.nextAddr cfg₁1.varEnv :=
    wfVarEnv_mono hle_next cfg₁1.varEnv hih1.1.2
  -- Final config restores cfg₁1.varEnv
  subst hcfg_final_eq
  constructor
  · rcases hih2.1 with ⟨hwfmem3, _hwfenv3⟩
    constructor
    · simpa using hwfmem3
    · simpa using hwfenv1_lift
  · simpa using hih2.2

private lemma wfConfig_preservedW_app (e1 e2 : Expr) (fuel : Nat)
    (cfg₀ cfg₁ : Config) (v : Value) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld)
    (hbeval : LeanPoison.beval (fuel + 1) cfg₀ (Expr.app e1 e2) verbose w₀ =
        EST.Out.ok (.success cfg₁ v) w₁)
    (hwf₀ : wfConfig cfg₀)
    (ih : ∀ (m : Nat), m < fuel.succ →
        ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
          wfConfig cfg₀' →
          ∀ (w₀' w₁' : Void IO.RealWorld),
            LeanPoison.beval m cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
            wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v') :
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  unfold LeanPoison.beval at hbeval
  simp at hbeval
  simp [bind, Bind.bind, EST.bind] at hbeval
  split at hbeval
  · next h_result2 h_state2 h_beval2 =>
    split at hbeval
    · next cfg₁' v₂ =>
      have hih2 :=
        ih fuel (Nat.lt_succ_self fuel) e2 cfg₀ cfg₁' v₂ hwf₀ w₀ h_state2 h_beval2
      simp [EST.bind] at hbeval
      split at hbeval
      · next h_result1 h_state1 h_beval1 =>
        split at hbeval
        · next cfg₂ x body env =>
          have hih1 :=
            ih fuel (Nat.lt_succ_self fuel) e1 cfg₁' cfg₂ (Value.closure x body env) hih2.1
              h_state2 h_state1 h_beval1
          split at hbeval
          · next h_pureMode =>
            injection hbeval with h_res h_world
            injection h_res
          · next h_notPureMode =>
            cases fuel with
            | zero =>
                simp [LeanPoison.bevalFunctionBody] at hbeval
                injection hbeval with h_res h_world
                injection h_res
            | succ fuel' =>
                unfold LeanPoison.bevalFunctionBody at hbeval
                simp at hbeval
                simp [bind, Bind.bind, EST.bind] at hbeval
                split at hbeval
                · next h_body_result h_body_state h_beval_body =>
                  split at hbeval
                  · next evalConfig v_body =>
                    injection hbeval with h_res h_world
                    injection h_res with h_cfg_eq h_val_eq
                    subst h_cfg_eq h_val_eq
                    -- Extract environment well-formedness from closure value
                    have h_env_wf : wfVarEnv cfg₂.nextAddr env := by
                      cases hih1.2 with
                      | closure _ _ _ hwf_env => exact hwf_env
                    -- Prove argument value is well-formed at cfg₂
                    have hterm1 : terminatesToW h_state2 h_state1 e1 cfg₁' cfg₂ (Value.closure x body env) :=
                      ⟨fuel'.succ, verbose, h_beval1⟩
                    have hle_arg : cfg₁'.nextAddr ≤ cfg₂.nextAddr :=
                      terminatesToW_nextAddr_mono e1 cfg₁' cfg₂ (Value.closure x body env) h_state2 h_state1 hterm1
                    have hv2_wf : wfValue cfg₂.nextAddr v₂ :=
                      wfValue_mono hle_arg v₂ hih2.2
                    -- Prove function body starting config is well-formed
                    have hwf_env_updated : wfVarEnv cfg₂.nextAddr (VarEnv.update env x v₂) :=
                      wfVarEnv_update cfg₂.nextAddr env x v₂ h_env_wf hv2_wf
                    have hwf_body_cfg : wfConfig { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } := by
                      rcases hih1.1 with ⟨hwfmem2, _⟩
                      exact ⟨hwfmem2, hwf_env_updated⟩
                    -- Prove fuel bound for IH
                    have hlt_body : fuel' < fuel'.succ.succ := by
                      exact Nat.lt_trans (Nat.lt_succ_self fuel') (Nat.lt_succ_self fuel'.succ)
                    -- Apply IH to body evaluation
                    have h_body_wf : wfConfig evalConfig ∧ wfValue evalConfig.nextAddr v_body :=
                      ih fuel' hlt_body body
                        { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } evalConfig v_body
                        hwf_body_cfg h_state1 h_body_state h_beval_body
                    -- Prove final config and value are well-formed
                    constructor
                    · rcases h_body_wf.1 with ⟨hwfmem_body, _⟩
                      constructor
                      · intro a hcontains
                        have hcontains' : evalConfig.memory.contains a := by
                          simpa using hcontains
                        exact hwfmem_body a hcontains'
                      · have hterm_body :
                          terminatesToW h_state1 h_body_state body
                            { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } evalConfig v_body :=
                          ⟨fuel', verbose, h_beval_body⟩
                        have hle_body : cfg₂.nextAddr ≤ evalConfig.nextAddr := by
                          have hle :=
                            terminatesToW_nextAddr_mono body
                              { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := false } evalConfig v_body
                              h_state1 h_body_state hterm_body
                          simpa using hle
                        have hwfenv2 : wfVarEnv cfg₂.nextAddr cfg₂.varEnv := hih1.1.2
                        exact wfVarEnv_mono hle_body cfg₂.varEnv hwfenv2
                    · simpa using h_body_wf.2
                  · next =>
                    simp [pure] at hbeval
                    injection hbeval with h_contra _
                    cases h_contra
                  · next msg =>
                    simp [pure] at hbeval
                    injection hbeval with h_contra _
                    cases h_contra
                · next h_body_error h_body_state =>
                  injection hbeval

        · next cfg₂ x body env =>
          cases h_pure_body : Expr.toPExpr? body with
          | none =>
              simp [h_pure_body, pure] at hbeval
              injection hbeval with h_res h_world
              injection h_res
          | some pe_body =>
              simp [h_pure_body] at hbeval
              have hih1 :=
                ih fuel (Nat.lt_succ_self fuel) e1 cfg₁' cfg₂ (Value.peClosure x body env) hih2.1
                  h_state2 h_state1 h_beval1
              cases fuel with
              | zero =>
                  simp [LeanPoison.bevalFunctionBody] at hbeval
                  injection hbeval with h_res h_world
                  injection h_res
              | succ fuel' =>
                  unfold LeanPoison.bevalFunctionBody at hbeval
                  simp at hbeval
                  simp [bind, Bind.bind, EST.bind] at hbeval
                  split at hbeval
                  · next h_body_result h_body_state h_beval_body =>
                    split at hbeval
                    · next evalConfig v_body =>
                      injection hbeval with h_res h_world
                      injection h_res with h_cfg_eq h_val_eq
                      subst h_cfg_eq h_val_eq
                      have h_env_wf : wfVarEnv cfg₂.nextAddr env := by
                        cases hih1.2 with
                        | peClosure _ _ _ hwf_env => exact hwf_env
                      have hterm1 : terminatesToW h_state2 h_state1 e1 cfg₁' cfg₂ (Value.peClosure x body env) :=
                        ⟨fuel'.succ, verbose, h_beval1⟩
                      have hle_arg : cfg₁'.nextAddr ≤ cfg₂.nextAddr :=
                        terminatesToW_nextAddr_mono e1 cfg₁' cfg₂ (Value.peClosure x body env) h_state2 h_state1 hterm1
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
                        ih fuel' hlt_body body
                          { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := true } evalConfig v_body
                          hwf_body h_state1 h_body_state h_beval_body
                      have h_next_eq : evalConfig.nextAddr = cfg₂.nextAddr := by
                        have h_pure_eq :=
                          beval_pure_nextAddr_eq body fuel'
                            { cfg₂ with varEnv := VarEnv.update env x v₂, pureMode := true } evalConfig v_body
                            verbose h_state1 h_body_state pe_body h_pure_body rfl h_beval_body
                        simpa using h_pure_eq
                      constructor
                      · -- final config shares memory/nextAddr/varEnv with cfg₂
                        simpa using hih1.1
                      · have hv : wfValue cfg₂.nextAddr v_body := by
                          simpa [h_next_eq] using h_body.2
                        simpa using hv
                    · next =>
                      simp [pure] at hbeval
                      injection hbeval with h_contra _
                      cases h_contra
                    · next msg =>
                      simp [pure] at hbeval
                      injection hbeval with h_contra _
                      cases h_contra
                  · next h_body_error h_body_state =>
                    injection hbeval
        · next v =>
          simp [pure] at hbeval
          injection hbeval with h_res h_world
          injection h_res
        · next =>
          simp [pure] at hbeval
          injection hbeval with h_res h_world
          injection h_res
        · next msg =>
          simp [pure] at hbeval
          injection hbeval with h_res h_world
          injection h_res
      · next h_error1 h_state1 =>
        injection hbeval
    · next =>
      simp [pure] at hbeval
      injection hbeval with h_res h_world
      injection h_res
    · next msg =>
      simp [pure] at hbeval
      injection hbeval with h_res h_world
      injection h_res
  · next h_error2 h_state2 =>
    injection hbeval

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
lemma wfConfig_preservedW (w₀ w₁ : Void IO.RealWorld) (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesToW w₀ w₁ e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  intro hterm hwf₀
  rcases hterm with ⟨fuel, verbose, hbeval⟩
  -- Strong induction on fuel; main split is on the expression.
  -- We generalise the world parameters as well (they are irrelevant to well-formedness),
  -- so the IH can be applied to sub-evaluations that thread intermediate worlds.
  revert w₀ w₁ e cfg₀ cfg₁ v hwf₀ verbose hbeval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro w₀ w₁ e cfg₀ cfg₁ v hwf₀ verbose hbeval
      cases fuel with
      | zero =>
          -- beval 0 cannot succeed.
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          cases hbeval
      | succ fuel =>
          have ih :
              ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
                wfConfig cfg₀' →
                ∀ (w₀' w₁' : Void IO.RealWorld),
                  LeanPoison.beval fuel cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
                  wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v' := by
            intro e cfg₀' cfg₁' v' hwf₀' w₀' w₁' hbeval'
            have hlt : fuel < fuel.succ := Nat.lt_succ_self fuel
            exact IH fuel hlt w₀' w₁' e cfg₀' cfg₁' v' hwf₀' verbose hbeval'
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
            bevalOp_structure e1 e2 op (fuel + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
          rcases hstruct with
            ⟨cfg₁1, cfg₁2, v1, v2, w_mid, hbeval1', hbeval2', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀ w_mid hbeval1'
          have hih2 := ih e2 cfg₁1 cfg₁2 v2 hih1.1 w_mid w₁ hbeval2'
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
            bevalUnaryOp_structure op e1 (fuel + 1) verbose cfg₀ cfg₁ v w₀ w₁ hbeval
          rcases hstruct with ⟨cfg₁1, v1, hbeval1', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ w₀ w₁ hbeval1'
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
          have ih_strong :
              ∀ (m : Nat), m < fuel.succ →
                ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
                  wfConfig cfg₀' →
                  ∀ (w₀' w₁' : Void IO.RealWorld),
                    LeanPoison.beval m cfg₀' e verbose w₀' = EST.Out.ok (.success cfg₁' v') w₁' →
                    wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v' := by
            intro m hlt e cfg₀' cfg₁' v' hwf₀' w₀' w₁' hbeval'
            exact IH m hlt w₀' w₁' e cfg₀' cfg₁' v' hwf₀' verbose hbeval'
          exact wfConfig_preservedW_app e1 e2 fuel cfg₀ cfg₁ v verbose w₀ w₁ hbeval hwf₀ ih_strong
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

/-- Evaluation preserves config well-formedness (world-free). -/
lemma wfConfig_preserved (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  intro ⟨fuel, verbose, hbeval⟩ hwf₀
  -- Convert world-free to world-indexed by applying at defaultWorld
  have hterm_w : terminatesToW LeanProofs.defaultWorld LeanProofs.defaultWorld e cfg₀ cfg₁ v := by
    refine ⟨fuel, verbose, ?_⟩
    exact LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hbeval
  exact wfConfig_preservedW LeanProofs.defaultWorld LeanProofs.defaultWorld e cfg₀ cfg₁ v hterm_w hwf₀
