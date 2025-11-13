-- Formal properties of the poison language: VarEnvPreservation

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

-- Helper lemma: bevalFunctionBody preserves varEnv
private lemma bevalFunctionBody_preserves_varEnv
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
    pure (.success finalConfig v) →
  currentConfig.varEnv = finalConfig.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel
  revert finalConfig v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro finalConfig v h_eval
    have h_eval_fn := h_eval
    cases n with
    | zero =>
      -- When fuel = 0, bevalFunctionBody returns outOfFuel
      -- Convert function equality to point-wise equality at defaultWorld
      have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
      unfold LeanPoison.bevalFunctionBody at h_eval_world
      simp [pure] at h_eval_world
      -- Now we have: EvalResult.outOfFuel = EvalResult.success finalConfig v
      -- Injection will give us the contradictory components
      injection h_eval_world with h_contr
      -- h_contr is a contradiction between different constructors, so cases derives False
      cases h_contr
    | succ fuel' =>
      -- fuel = fuel' + 1: bevalFunctionBody has enough fuel
      -- Convert function equality to point-wise equality at defaultWorld
      have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
      unfold LeanPoison.bevalFunctionBody at h_eval_world
      simp [bind, Bind.bind, EStateM.bind] at h_eval_world
      -- Split on body evaluation result
      split at h_eval_world
      · next h_body_result h_body_state h_beval_body =>
        split at h_eval_world
        · next evalConfig v_body =>
          -- Body evaluation succeeded
          split at h_eval_world
          · -- isPure = true branch
            injection h_eval_world with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
          · -- isPure = false branch
            injection h_eval_world with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc, pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
        · next =>
          injection h_eval_world with h_contr _
          injection h_contr
        · next msg =>
          injection h_eval_world with h_contr _
          injection h_contr
      · next h_body_error h_body_state =>
        injection h_eval_world

-- Helper lemmas for beval_preserves_varEnv, one per expression constructor

private lemma beval_preserves_varEnv_num (n : Int) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.num n) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  unfold LeanPoison.beval at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_bool (b : Bool) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.bool b) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  unfold LeanPoison.beval at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_unit (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ Expr.unit verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  unfold LeanPoison.beval at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_str (s : String) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.str s) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  unfold LeanPoison.beval at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_var (x : Name) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.var x) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  unfold LeanPoison.beval at h_eval_world
  simp [pure] at h_eval_world
  cases h_lookup : config₀.varEnv.lookup x with
  | some v' =>
    simp [h_lookup] at h_eval_world
    injection h_eval_world with h_cfg _
    injection h_cfg with h_cfg_eq
    subst h_cfg_eq
    rfl
  | none =>
    simp [h_lookup] at h_eval_world
    injection h_eval_world with h_contr _
    injection h_contr

private lemma beval_preserves_varEnv_unaryop (op : UnaryOp) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  -- Keep the function equality for IH, destruct using per-world equality
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  -- Specialise to the default world only for destructing the bind-chain
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp at h_eval_world
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  -- Case analysis on evaluation of e1
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    -- e1 evaluated to success; inspect inner result
    split at h_eval_world
    · next config' v' =>
      -- Now run the unary operator
      cases h_evalUnaryOp : LeanPoison.evalUnaryOp op v' with
      | some v_result =>
        simp [h_evalUnaryOp] at h_eval_world
        injection h_eval_world with h_cfg h_state_eq
        injection h_cfg with h_cfg_eq h_val_eq
        subst h_cfg_eq
        -- Use IH on e1 (construct function equality pointwise over worlds)
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' v') := by
          funext w
          -- derive a per-world view of the whole unaryop evaluation and peel the bind-chain
          have h_eval_world_w := LeanProofs.evalAtWorld_eq w h_eval_fn
          simp at h_eval_world_w
          simp [bind, Bind.bind, EStateM.bind] at h_eval_world_w
          -- evaluation of e1 at world w must be success (otherwise contradiction with success of unaryop)
          split at h_eval_world_w
          · next _h_result_w h_state_w h_beval1_w =>
            -- inner split produces the success case for e1 at world w
            split at h_eval_world_w
            · next config_w v_w =>
              -- evaluate unary op at world w; must succeed to match outer success
              cases h_evalUnaryOp_w : LeanPoison.evalUnaryOp op v_w with
              | some v_result_w =>
                simp [h_evalUnaryOp_w] at h_eval_world_w
                -- from outer success, configs must agree; unify config_w with config'
                injection h_eval_world_w with h_cfg_w h_state_eq_w
                injection h_cfg_w with h_cfg_eq_w h_val_eq_w
                subst h_cfg_eq_w
                -- show the sub-expression value is world-independent using evalUnaryOp determinism
                have h1 : LeanPoison.evalUnaryOp op v' = some v := by
                  simpa [h_val_eq] using h_evalUnaryOp
                have h2 : LeanPoison.evalUnaryOp op v_w = some v := by
                  simpa [h_val_eq_w] using h_evalUnaryOp_w
                -- Since evalUnaryOp only succeeds for UnaryOp.not with Value.bool,
                -- both v' and v_w must be bool values
                have hv : v_w = v' := by
                  cases op with
                  | not =>
                    -- evalUnaryOp UnaryOp.not only succeeds for Value.bool
                    -- So both v' and v_w must be Value.bool
                    cases v' with
                    | bool b' =>
                      cases v_w with
                      | bool b_w =>
                        -- Both are bools, show they're equal
                        have hv1 : v = Value.bool (!b') := (Option.some.inj h1).symm
                        have hv2 : v = Value.bool (!b_w) := (Option.some.inj h2).symm
                        have : Value.bool (!b') = Value.bool (!b_w) := by
                          rw [← hv1, hv2]
                        injection this with h_not_eq
                        -- h_not_eq: !b' = !b_w
                        -- Since ! is injective, b' = b_w
                        cases b' <;> cases b_w <;> cases h_not_eq <;> rfl
                      | num | unit | str | loc _ | closure _ _ _ | peClosure _ _ _ =>
                        -- v_w is not bool, but evalUnaryOp succeeded - contradiction
                        simp [LeanPoison.evalUnaryOp] at h2
                    | num | unit | str | loc _ | closure _ _ _ | peClosure _ _ _ =>
                      -- v' is not bool, but evalUnaryOp succeeded - contradiction
                      simp [LeanPoison.evalUnaryOp] at h1
                -- conclude pointwise equality for e1 at world w
                -- Rewrite h_beval1_w: replace v_w with v' and h_state_w with w
                rw [hv, h_state_eq_w] at h_beval1_w
                simp [pure]
                exact h_beval1_w
              | none =>
                -- impossible: outer evaluation succeeded
                simp [h_evalUnaryOp_w] at h_eval_world_w
                injection h_eval_world_w with h_cfg_w _
                injection h_cfg_w
            · next =>
              -- impossible: outer evaluation succeeded
              simp [pure] at h_eval_world_w
              injection h_eval_world_w with h_cfg_w _
              injection h_cfg_w
            · next msg =>
              -- impossible: outer evaluation succeeded
              simp [pure] at h_eval_world_w
              injection h_eval_world_w with h_cfg_w _
              injection h_cfg_w
          · next h_error_w _ =>
            -- impossible: outer evaluation succeeded
            injection h_eval_world_w
        exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1'
      | none =>
        simp [h_evalUnaryOp] at h_eval_world
        injection h_eval_world with h_cfg _
        injection h_cfg
    · next =>
      injection h_eval_world with h_cfg _; injection h_cfg
    · next msg =>
      injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state =>
    injection h_eval_world


-- TODO: This lemma needs state equality proofs to extract function equalities from h_beval1 and h_beval2
-- The issue is showing h_state1 = defaultWorld and h_state2 = h_state1 from the bind chain
private lemma beval_preserves_varEnv_op (e1 e2 : Expr) (op : Op) (fuel' : Nat) (verbose : Bool) (config₀ config₃ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.op e1 op e2) verbose = pure (.success config₃ v)) :
  config₀.varEnv = config₃.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval_world
    · next config₁ v₁ =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval_world
        · next config₂ v₂ =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
            simp [h_evalOp] at h_eval_world
            injection h_eval_world with h_cfg h_state_eq
            injection h_cfg with h_cfg_eq
            injection h_state_eq with h_state2_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            -- Extract function equalities from h_beval1 and h_beval2
            -- h_beval1: beval ... defaultWorld = EStateM.Result.ok ... h_state1
            -- We need: beval ... = pure (.success config₁ v₁)
            -- From h_state2_eq, we know h_state2 = defaultWorld
            -- Since beval preserves world, h_state1 = defaultWorld
            have h_state1_eq : h_state1 = LeanProofs.defaultWorld := by
              -- From the bind chain: h_state2 is the output state of the second beval
              -- and h_state2 = defaultWorld (from h_state2_eq)
              -- Since beval is deterministic, h_state1 should also equal defaultWorld
              sorry -- TODO: need to show h_state1 = defaultWorld from bind chain
            have h_beval1_fn : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
              funext w
              simp [pure]
              -- Use h_beval1 and generalize from defaultWorld to w
              have h_beval1_w := LeanProofs.evalAtWorld_eq w (by
                -- Convert h_beval1 to function equality first
                funext w'
                simp [pure]
                rw [h_state1_eq] at h_beval1
                exact h_beval1)
              exact h_beval1_w
            let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁ v₁ h_beval1_fn
            have h_beval2_fn : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂ v₂) := by
              funext w
              simp [pure]
              -- Similar approach for h_beval2
              have h_state2_eq_inner : h_state2 = h_state1 := by
                -- From the bind chain, h_state2 should equal h_state1 (the output of first beval)
                -- Actually, h_state2 is the output state of second beval, which should equal h_state1
                sorry -- TODO: need to show h_state2 = h_state1 from bind chain
              have h_beval2_w := LeanProofs.evalAtWorld_eq w (by
                funext w'
                simp [pure]
                rw [h_state2_eq_inner, h_state1_eq] at h_beval2
                exact h_beval2)
              exact h_beval2_w
            let IH2 := IH fuel' h_fuel e2 verbose config₁ config₂ v₂ h_beval2_fn
            exact Eq.trans IH1 IH2
          | none =>
            simp [h_evalOp] at h_eval_world
            injection h_eval_world with h_cfg _
            injection h_cfg
        · next => injection h_eval_world with h_cfg _; injection h_cfg
        · next msg => injection h_eval_world with h_cfg _; injection h_cfg
      · next h_error2 h_state2 =>
        cases h_eval_world
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => cases h_eval_world

private lemma beval_preserves_varEnv_ite (e1 e2 e3 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval_world
    · next config₁' =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval_world
        · next config₂ v₂ =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool true)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool true) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        · next => injection h_eval_world with h_cfg _; injection h_cfg
        · next msg => injection h_eval_world with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval_world
    · next config₁' =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result3 h_state3 h_beval3 =>
        split at h_eval_world
        · next config₂ v₃ =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool false)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool false) h_beval1'
          have h_beval3' : LeanPoison.beval fuel' config₁' e3 verbose = pure (.success config₂ v₃) := by
            funext _
            simp [pure]
            exact h_beval3
          let IH3 := IH fuel' h_fuel e3 verbose config₁' config₂ v₃ h_beval3'
          exact Eq.trans IH1 IH3
        · next => injection h_eval_world with h_cfg _; injection h_cfg
        · next msg => injection h_eval_world with h_cfg _; injection h_cfg
      · next h_error3 h_state3 => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval_world

private lemma beval_preserves_varEnv_newRef (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.newRef e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' n =>
      injection h_eval_world with h_cfg _
      injection h_cfg with h_cfg_eq
      subst h_cfg_eq
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      simp [freshLoc]
      exact IH1
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

private lemma beval_preserves_varEnv_assign (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval_world
    · next config₁' l =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval_world
        · next config₂ n =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.loc l)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.loc l) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ (Value.num n) h_beval2'
          simp
          exact Eq.trans IH1 IH2
        · next v => injection h_eval_world with h_cfg _; injection h_cfg
        · next => injection h_eval_world with h_cfg _; injection h_cfg
        · next msg => injection h_eval_world with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval_world

private lemma beval_preserves_varEnv_deref (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.deref e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' l =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.loc l)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.loc l) h_beval1'
      cases h_mem_lookup : config'.memory[l]? with
      | some n =>
        simp [h_mem_lookup] at h_eval_world
        injection h_eval_world with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        exact IH1
      | none =>
        simp [h_mem_lookup] at h_eval_world
        injection h_eval_world with h_contr _
        injection h_contr
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

private lemma beval_preserves_varEnv_seq (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_split1_result h_split1_state h_beval1 =>
    split at h_eval_world
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      . next h_split3_config h_split3_v1 h_beval2 =>
        split at h_eval_world
        · next h_split4_config config₂ v₂ =>
          injection h_eval_world with h_eval_e1 h_eval_e2
          injection h_eval_e1 with h_eval_e1_result h_eval_e1_config
          subst h_eval_e1_result h_eval_e2 h_eval_e1_config
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        . next h_split4_eq =>
          injection h_eval_world with h_eval_e1 h_eval_e2
          injection h_eval_e1
        . next h_split4_msg h_split4_eq =>
          injection h_eval_world with h_eval_e1 h_eval_e2
          injection h_eval_e1
      . next h_split3_eq => injection h_eval_world
    · next h_split2_error h_split2_state =>
      injection h_eval_world with h_eval_e1 h_eval_e2
      injection h_eval_e1
    . next h_split2_msg h_split2_eq =>
      injection h_eval_world with h_eval_e1 h_eval_e2
      injection h_eval_e1
  . next h_split1_error h_split1_state h_split1_eq => injection h_eval_world

private lemma beval_preserves_varEnv_kwhile (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel'.succ - 1) config₀ unfolded verbose
  simp at h_eval_fn
  -- After simp: the let binding is inlined and fuel'.succ - 1 simplifies to fuel'
  -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose = pure (.success config₁ v)
  have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
  -- Define the unfolded expression that kwhile expands to
  let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  -- h_eval_fn already contains the evaluation of this unfolded expression as a function equality
  -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
  -- The unfolded expression (ite) preserves varEnv by IH (which internally uses the ite proof)
  exact IH fuel' h_fuel unfolded verbose config₀ config₁ v h_eval_fn

private lemma beval_preserves_varEnv_vlet (x : Name) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval_world
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval_world
        · next config₂ v₂ =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          simp
          exact IH1
        · next => injection h_eval_world with h_cfg _; injection h_cfg
        · next msg => injection h_eval_world with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval_world
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval_world

private lemma beval_preserves_varEnv_fn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.fn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [pure] at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_pfn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.pfn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [pure] at h_eval_world
  injection h_eval_world with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_app (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result1 h_state1 h_beval2 =>
    split at h_eval_world
    · next config₁' v₂ =>
      simp [EStateM.bind] at h_eval_world
      split at h_eval_world
      · next h_result2 h_state2 h_beval1 =>
        split at h_eval_world
        · next config₂ x body env =>
          split at h_eval_world
          · injection h_eval_world with h_contr _; injection h_contr
          · -- pureMode is false, call bevalFunctionBody
            -- h_eval_world contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body false defaultWorld = pure (.success config₁ v) defaultWorld
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
            have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.closure x body env)) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.closure x body env) h_beval1'
            -- Extract bevalFunctionBody equality from h_eval_fn
            -- Convert from per-world equality to function equality
            have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval_world
            -- Apply helper lemma
            have h_funcBody : config₂.varEnv = config₁.varEnv :=
              bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body false v h_bevalFunctionBody
            -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
            exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next config₂ x body env =>
          -- peClosure case (pure function), call bevalFunctionBody with isPure=true
          -- h_eval_world contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body true defaultWorld = pure (.success config₁ v) defaultWorld
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
          have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.peClosure x body env)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.peClosure x body env) h_beval1'
          -- Extract bevalFunctionBody equality from h_eval_fn
          -- Convert from per-world equality to function equality
          have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
              pure (.success config₁ v) := by
            funext _
            simp [pure]
            exact h_eval_world
          -- Apply helper lemma
          have h_funcBody : config₂.varEnv = config₁.varEnv :=
            bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body true v h_bevalFunctionBody
          -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
          exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next v => injection h_eval_world with h_contr _; injection h_contr
        · next => injection h_eval_world with h_contr _; injection h_contr
        · next msg => injection h_eval_world with h_contr _; injection h_contr
      · next h_error2 h_state2 => injection h_eval_world
    · next => injection h_eval_world with h_contr _; injection h_contr
    · next msg => injection h_eval_world with h_contr _; injection h_contr
  · next h_error1 h_state1 => injection h_eval_world

private lemma beval_preserves_varEnv_rand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.rand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' n =>
      split at h_eval_world
      · simp [Functor.map, EStateM.map] at h_eval_world
        split at h_eval_world
        · next r_result r_state =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval_world
      · simp [Functor.map, EStateM.map] at h_eval_world
        split at h_eval_world
        · next p_result p_state =>
          injection h_eval_world with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

private lemma beval_preserves_varEnv_frand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.frand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' n =>
      split at h_eval_world
      · simp [Functor.map, EStateM.map] at h_eval_world
        split at h_eval_world
        · next r_result r_state =>
          injection h_eval_world with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval_world
      · simp [Functor.map, EStateM.map] at h_eval_world
        split at h_eval_world
        · next p_result p_state =>
          injection h_eval_world with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

private lemma beval_preserves_varEnv_printInt (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printInt e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' n =>
      simp [Functor.map, EStateM.map] at h_eval_world
      split at h_eval_world
      · next p_result p_state =>
        injection h_eval_world with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      · next p_error p_state => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

private lemma beval_preserves_varEnv_printString (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printString e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  have h_eval_fn := h_eval
  unfold LeanPoison.beval at h_eval_fn
  simp at h_eval_fn
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
  simp [bind, Bind.bind, EStateM.bind] at h_eval_world
  split at h_eval_world
  · next h_result h_state h_beval1 =>
    split at h_eval_world
    · next config' s =>
      simp [Functor.map, EStateM.map] at h_eval_world
      split at h_eval_world
      · next p_result p_state =>
        injection h_eval_world with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.str s)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.str s) h_beval1'
      · next p_error p_state => injection h_eval_world
    · next v => injection h_eval_world with h_cfg _; injection h_cfg
    · next => injection h_eval_world with h_cfg _; injection h_cfg
    · next msg => injection h_eval_world with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval_world

-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)
lemma beval_preserves_varEnv (e : Expr) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ e verbose = pure (.success config₁ v) →
  config₀.varEnv = config₁.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel, then case analysis on e
  -- For all expression forms, the varEnv field is never modified
  -- (even in let bindings, we create a new config with extended varEnv for the body,
  --  but the final result restores the original varEnv)
  revert e config₀ config₁ v h_eval verbose
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e verbose config₀ config₁ v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, beval returns outOfFuel, not success
      have h_eval_fn := h_eval
      unfold LeanPoison.beval at h_eval_fn
      simp at h_eval_fn
      have h_eval_world := LeanProofs.evalAtDefault_eq h_eval_fn
      cases h_eval_world
    | succ fuel' =>
      cases e with
      | num n => exact beval_preserves_varEnv_num n fuel' verbose config₀ config₁ v IH h_eval
      | bool b => exact beval_preserves_varEnv_bool b fuel' verbose config₀ config₁ v IH h_eval
      | unit => exact beval_preserves_varEnv_unit fuel' verbose config₀ config₁ v IH h_eval
      | str s => exact beval_preserves_varEnv_str s fuel' verbose config₀ config₁ v IH h_eval
      | var x => exact beval_preserves_varEnv_var x fuel' verbose config₀ config₁ v IH h_eval
      | op e1 op e2 =>
        exact beval_preserves_varEnv_op e1 e2 op fuel' verbose config₀ config₁ v IH h_eval
      | unaryop op e1 =>
        exact beval_preserves_varEnv_unaryop op e1 fuel' verbose config₀ config₁ v IH h_eval
      | ite e1 e2 e3 =>
        exact beval_preserves_varEnv_ite e1 e2 e3 fuel' verbose config₀ config₁ v IH h_eval
      | newRef e1 =>
        exact beval_preserves_varEnv_newRef e1 fuel' verbose config₀ config₁ v IH h_eval
      | assign e1 e2 =>
        exact beval_preserves_varEnv_assign e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | deref e1 =>
        exact beval_preserves_varEnv_deref e1 fuel' verbose config₀ config₁ v IH h_eval
      | seq e1 e2 =>
        exact beval_preserves_varEnv_seq e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | kwhile e1 e2 =>
        exact beval_preserves_varEnv_kwhile e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | vlet x e1 e2 =>
        exact beval_preserves_varEnv_vlet x e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | fn x paramType body returnType =>
        exact beval_preserves_varEnv_fn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | pfn x paramType body returnType =>
        exact beval_preserves_varEnv_pfn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | app e1 e2 =>
        exact beval_preserves_varEnv_app e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | rand e1 =>
        exact beval_preserves_varEnv_rand e1 fuel' verbose config₀ config₁ v IH h_eval
      | frand e1 =>
        exact beval_preserves_varEnv_frand e1 fuel' verbose config₀ config₁ v IH h_eval
      | printInt e1 =>
        exact beval_preserves_varEnv_printInt e1 fuel' verbose config₀ config₁ v IH h_eval
      | printString e1 =>
        exact beval_preserves_varEnv_printString e1 fuel' verbose config₀ config₁ v IH h_eval
