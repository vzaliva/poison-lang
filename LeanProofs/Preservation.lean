-- Preservation Property for the Poison Language
--
-- The Preservation property states that evaluation preserves types:
-- if a well-typed expression evaluates successfully, the resulting value
-- has the expected enriched type and the final state is consistent with
-- the output typing context.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.NonInterference

-- ================================================================
-- Preservation Property
-- ================================================================
--
-- Proof Strategy:
-- ---------------
-- The proof uses strong induction on evaluation fuel (fuel_eval), following
-- the pattern from typecheck_PExpr_preserves_typestate in Properties.lean.
--
-- For each fuel value n and expression e, we show that if:
--   1. The expression typechecks successfully
--   2. The runtime instantiates the input typing context (runtimeInstantiatesCtx)
--   3. Evaluation terminates successfully with fuel n
-- Then:
--   1. The result value has the expected enriched type
--   2. The final runtime state instantiates the output typing context
--
-- The induction hypothesis (IH) is available for all fuel values m < n,
-- which is used for recursive subexpressions.
--
-- Key insights:
-- - Literals: always produce values of the correct type
-- - Variables: if x is typed and in ρ, lookup returns a value of the correct type
-- - Operations: if operands have correct types, result has the expected type
-- - References: fresh locations are added to both runtime and typing contexts
-- - While loops: require fixpoint reasoning about the typing context
-- - Function application: requires IH on the function body with extended context
--
-- Current Status:
-- --------------
-- This is a partial proof with structure demonstrating the approach.
-- The base cases (literals: num, bool, unit, str) are proven.
--
-- ================================================================

-- Private lemma for num case
private lemma preservation_num (n : Int) (ctx : TypeContext) : Preservation (Expr.num n) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  -- Numeric literals evaluate to numeric values and don't modify the environment
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  -- Unfold beval and analyze the IO computation
  simp [LeanPoison.beval] at h_eval
  apply congrFun (a := ()) at h_eval
  -- Case split on fuel
  cases fuel_eval with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    -- This contradicts h_terminates which requires success
    cases h_eval
  | succ fuel' =>
    -- When fuel > 0, beval returns success config (Value.num n)
    injection h_eval with h_eq_config h_eq_val
    -- Extract that configs are equal and value is num n
    cases h_eq_config
    cases h_eq_val
    -- Analyze typechecking to extract res.qualType.etyp = ETyp.int
    cases fuel_tc with
    | zero =>
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp [typecheck, typecheckExpr, typecheckInt] at h_typecheck
      injection h_typecheck with h_res
      subst h_res
      -- Now we know res.qualType.etyp = ETyp.int and res.memEnv' = ctx.memEnv
      simp
      constructor
      · -- Value has correct type: num n has type int
        exact valueHasETyp.num n
      · -- Runtime instantiates output context
        exact h_instantiate

-- Private lemma for bool case
private lemma preservation_bool (b : Bool) (ctx : TypeContext) : Preservation (Expr.bool b) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  simp [LeanPoison.beval] at h_eval
  apply congrFun (a := ()) at h_eval
  cases fuel_eval with
  | zero => cases h_eval
  | succ fuel' =>
    injection h_eval with h_eq_config h_eq_val
    cases h_eq_config
    cases h_eq_val
    cases fuel_tc with
    | zero =>
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp [typecheck, typecheckExpr, typecheckBool] at h_typecheck
      injection h_typecheck with h_res
      subst h_res
      simp
      constructor
      · exact valueHasETyp.bool b
      · exact h_instantiate

-- Private lemma for unit case
private lemma preservation_unit (ctx : TypeContext) : Preservation Expr.unit ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  simp [LeanPoison.beval] at h_eval
  apply congrFun (a := ()) at h_eval
  cases fuel_eval with
  | zero => cases h_eval
  | succ fuel' =>
    injection h_eval with h_eq_config h_eq_val
    cases h_eq_config
    cases h_eq_val
    cases fuel_tc with
    | zero =>
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp [typecheck, typecheckExpr, typecheckUnit] at h_typecheck
      injection h_typecheck with h_res
      subst h_res
      simp
      constructor
      · exact valueHasETyp.unit
      · exact h_instantiate

-- Private lemma for str case
private lemma preservation_str (s : String) (ctx : TypeContext) : Preservation (Expr.str s) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  simp [LeanPoison.beval] at h_eval
  apply congrFun (a := ()) at h_eval
  cases fuel_eval with
  | zero => cases h_eval
  | succ fuel' =>
    injection h_eval with h_eq_config h_eq_val
    cases h_eq_config
    cases h_eq_val
    cases fuel_tc with
    | zero =>
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp [typecheck, typecheckExpr, typecheckString] at h_typecheck
      injection h_typecheck with h_res
      subst h_res
      simp
      constructor
      · exact valueHasETyp.str s
      · exact h_instantiate

-- Helper lemma: if a variable is in the typing context and runtime instantiates the context,
-- then the variable lookup returns a value with the correct enriched type
private lemma var_has_correct_type (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (x : Name) (qt : QTyp) :
  runtimeInstantiatesCtx ctx μ ρ →
  ctx.varEnv.lookup x = some qt →
  ∃ v, ρ.lookup x = some v ∧ valueHasETyp v qt.etyp := by
  intro ⟨_, h_vars⟩ h_lookup
  obtain ⟨v, h_v, h_typ⟩ := h_vars h_lookup
  exact ⟨v, h_v, h_typ⟩

-- Helper lemma: typecheckVar preserves the enriched type
-- The enriched type in the result is always the same as in the input qualified type,
-- regardless of predicates, poison status, or tag environment
private lemma typecheckVar_preserves_etyp (ctx : TypeContext) (x : Name) (qt : QTyp) (res : TypeResult) :
  ctx.varEnv.lookup x = some qt →
  typecheckVar ctx x = .ok res →
  res.qualType.etyp = qt.etyp := by
  intro h_lookup h_typecheck
  -- First, establish that qt' = qt from the lookup
  simp [typecheckVar] at h_typecheck
  cases h0: ctx.varEnv.lookup x with
  | none =>
    -- Contradiction: h_lookup says some qt, h0 says none
    rw [h_lookup] at h0
    clear h_lookup -- probably no longer needed
    cases h0
  | some qt' =>
    -- Now we know qt' = qt from h_lookup and h0
    rw [h_lookup] at h0 h_typecheck
    clear h_lookup -- probalby no longer needed
    injection h0 with h_qt_eq
    subst h_qt_eq
    simp at h_typecheck
    cases h1: qt with
    | mk etyp poison pred =>
      subst h1
      -- Case analysis on qt.pred
      simp at h_typecheck
      cases h2: pred with
      | noPred =>
        subst h2
        simp at h_typecheck
        simp [pure, Except.pure] at h_typecheck
        rw [← h_typecheck]
      | guardOnly k =>
        subst h2
        simp at h_typecheck
        -- typecheckVar for guardOnly checks ctx.tagEnv.get? k
        -- In all three cases (some true, some false, none), it returns etyp unchanged
        -- Use split to case on the match expression in h_typecheck
        split at h_typecheck
        · -- Case: some { value := true, deps := _deps }
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]
        · -- Case: some { value := false, deps := _deps }
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]
        · -- Case: none
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]
      | guardClosure k arg_name pred_body var_env =>
        subst h2
        simp at h_typecheck
        -- typecheckVar for guardClosure behaves identically to guardOnly
        -- In all three cases (some true, some false, none), it returns etyp unchanged
        -- Use split to case on the match expression in h_typecheck
        split at h_typecheck
        · -- Case: some { value := true, deps := _deps }
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]
        · -- Case: some { value := false, deps := _deps }
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]
        · -- Case: none
          simp [pure, Except.pure] at h_typecheck
          rw [← h_typecheck]


-- Helper lemma: typecheckVar preserves the memory environment
-- The memory environment in the result is always the same as in the input context
private lemma typecheckVar_preserves_memEnv (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.memEnv' = ctx.memEnv := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  -- All branches of typecheckVar return memEnv' := ctx.memEnv
  -- Use split to handle all cases uniformly
  split at h_typecheck
  · -- Case: x is in ctx.varEnv
    -- Further split on predicate and tag lookups
    repeat (first | split at h_typecheck | (simp [pure, Except.pure] at h_typecheck; rw [← h_typecheck]))
  · -- Case: x is not in ctx.varEnv (throws error, contradiction)
    simp at h_typecheck

-- Helper lemma: bevalFunctionBody never modifies the variable environment
-- Proven separately using strong induction on fuel, referencing beval_preserves_varEnv
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
    cases n with
    | zero =>
      -- When fuel = 0, bevalFunctionBody returns outOfFuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp [pure] at h_eval
      -- Apply congrFun to convert function equality to point-wise equality
      apply congrFun (a := ()) at h_eval
      -- Now we have: EvalResult.outOfFuel = EvalResult.success finalConfig v
      -- Injection will give us the contradictory components
      injection h_eval with h_contr
      -- h_contr is a contradiction between different constructors, so cases derives False
      cases h_contr
    | succ fuel' =>
      -- fuel = fuel' + 1: bevalFunctionBody has enough fuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp at h_eval
      -- Convert IO to EStateM form
      apply congrFun (a := ()) at h_eval
      simp [bind, Bind.bind, EStateM.bind] at h_eval
      -- Split on body evaluation result
      split at h_eval
      · next h_body_result h_body_state h_beval_body =>
        split at h_eval
        · next evalConfig v_body =>
          -- Body evaluation succeeded
          split at h_eval
          · -- isPure = true branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
          · -- isPure = false branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc, pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
        · next =>
          injection h_eval with h_contr _
          injection h_contr
        · next msg =>
          injection h_eval with h_contr _
          injection h_contr
      · next h_body_error h_body_state =>
        injection h_eval

-- Helper lemmas for beval_preserves_varEnv, one per expression constructor

private lemma beval_preserves_varEnv_num (n : Int) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.num n) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_bool (b : Bool) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.bool b) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_unit (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ Expr.unit verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_str (s : String) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.str s) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_var (x : Name) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.var x) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  cases h_lookup : config₀.varEnv.lookup x with
  | some v' =>
    simp [h_lookup] at h_eval
    injection h_eval with h_cfg _
    injection h_cfg with h_cfg_eq
    subst h_cfg_eq
    rfl
  | none =>
    simp [h_lookup] at h_eval
    injection h_eval with h_contr _
    injection h_contr

private lemma beval_preserves_varEnv_op (e1 e2 : Expr) (op : Op) (fuel' : Nat) (verbose : Bool) (config₀ config₃ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.op e1 op e2) verbose = pure (.success config₃ v)) :
  config₀.varEnv = config₃.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁ v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁ v₁ h_beval1'
            have h_beval2' : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₁ config₂ v₂ h_beval2'
            exact Eq.trans IH1 IH2
          | none =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 =>
        cases h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => cases h_eval

private lemma beval_preserves_varEnv_unaryop (op : UnaryOp) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' v' =>
      cases h_evalUnaryOp : LeanPoison.evalUnaryOp op v' with
      | some v_result =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' v') := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1'
      | none =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_ite (e1 e2 e3 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
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
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result3 h_state3 h_beval3 =>
        split at h_eval
        · next config₂ v₃ =>
          injection h_eval with h_cfg _
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
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error3 h_state3 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_newRef (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.newRef e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      injection h_eval with h_cfg _
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
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_assign (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' l =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ n =>
          injection h_eval with h_cfg _
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
        · next v => injection h_eval with h_cfg _; injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_deref (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.deref e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' l =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.loc l)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.loc l) h_beval1'
      cases h_mem_lookup : config'.memory[l]? with
      | some n =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        exact IH1
      | none =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_contr _
        injection h_contr
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_seq (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_split1_result h_split1_state h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      . next h_split3_config h_split3_v1 h_beval2 =>
        split at h_eval
        · next h_split4_config config₂ v₂ =>
          injection h_eval with h_eval_e1 h_eval_e2
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
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
        . next h_split4_msg h_split4_eq =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
      . next h_split3_eq => injection h_eval
    · next h_split2_error h_split2_state =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
    . next h_split2_msg h_split2_eq =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
  . next h_split1_error h_split1_state h_split1_eq => injection h_eval

private lemma beval_preserves_varEnv_kwhile (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := sorry

private lemma beval_preserves_varEnv_vlet (x : Name) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
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
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_fn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.fn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_pfn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.pfn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_app (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval2 =>
    split at h_eval
    · next config₁' v₂ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval1 =>
        split at h_eval
        · next config₂ x body env =>
          split at h_eval
          · injection h_eval with h_contr _; injection h_contr
          · -- pureMode is false, call bevalFunctionBody
            -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body false = pure (.success config₁ v)
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
            -- Extract bevalFunctionBody equality from h_eval
            -- Convert from applied form to pure form
            have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval
            -- Apply helper lemma
            have h_funcBody : config₂.varEnv = config₁.varEnv :=
              bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body false v h_bevalFunctionBody
            -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
            exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next config₂ x body env =>
          -- peClosure case (pure function), call bevalFunctionBody with isPure=true
          -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body true = pure (.success config₁ v)
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
          -- Extract bevalFunctionBody equality from h_eval
          -- Convert from applied form to pure form
          have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
              pure (.success config₁ v) := by
            funext _
            simp [pure]
            exact h_eval
          -- Apply helper lemma
          have h_funcBody : config₂.varEnv = config₁.varEnv :=
            bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body true v h_bevalFunctionBody
          -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
          exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next v => injection h_eval with h_contr _; injection h_contr
        · next => injection h_eval with h_contr _; injection h_contr
        · next msg => injection h_eval with h_contr _; injection h_contr
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_contr _; injection h_contr
    · next msg => injection h_eval with h_contr _; injection h_contr
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_rand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.rand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_frand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.frand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printInt (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printInt e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printString (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printString e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' s =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.str s)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.str s) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)
-- TODO: will be later moved to Preservation.Properties.lean to make it accessible from other lemmas.
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
      unfold LeanPoison.beval at h_eval
      simp at h_eval
      apply congrFun (a := ()) at h_eval
      cases h_eval
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

-- Helper lemma: evalOp preserves type correctness
-- If v1 has type etyp1 and v2 has type etyp2, and opEType? returns some result_etyp,
-- then evalOp returns a value with type result_etyp
private lemma evalOp_preserves_type (op : Op) (v1 v2 : Value) (etyp1 etyp2 result_etyp : ETyp) :
  valueHasETyp v1 etyp1 →
  valueHasETyp v2 etyp2 →
  opEType? op etyp1 etyp2 = some result_etyp →
  ∀ v, LeanPoison.evalOp op v1 v2 = some v → valueHasETyp v result_etyp := by
  intro h_typ1 h_typ2 h_op_type v h_eval
  -- Extract the actual types from valueHasETyp by cases
  cases h_typ1 <;> cases h_typ2
  -- Case analysis on the operation and value types
  <;> (cases op <;> simp [LeanPoison.evalOp] at h_eval
       <;> try (cases h_eval; simp [opEType?] at h_op_type; cases h_op_type; constructor))

-- Helper lemma: extract evaluation structure from successful beval of binary operation
-- This lemma mirrors typecheckOp_structure but for evaluation.
-- It extracts the intermediate evaluation steps from a successful beval of (op e1 e2).
-- Note: We only care about types (valueHasETyp), not exact values, for preservation.
-- The varEnv equalities follow from beval_preserves_varEnv.
private lemma bevalOp_structure (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₃ : Config) (v : Value) (etyp1 etyp2 result_etyp : ETyp) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose =
    pure (.success config₃ v) →
  opEType? op etyp1 etyp2 = some result_etyp →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config₁ v1) ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose = pure (.success config₂ v2) ∧
    valueHasETyp v1 etyp1 ∧
    valueHasETyp v2 etyp2 ∧
    valueHasETyp v result_etyp := by
  intro h_eval h_op_etyp
  -- Unfold beval for the op case
  simp [LeanPoison.beval] at h_eval
  -- The evaluation uses do notation with nested matches
  -- We need to extract the intermediate results from the monadic structure
  -- Then use evalOp_preserves_type to establish the type relationships
  -- The varEnv preservation follows from beval_preserves_varEnv (applied separately)
  sorry

-- Helper lemma: extract structure from typecheckOp
private lemma typecheckOp_structure (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat) (res : TypeResult) :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ∃ (result1 result2 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 fuel = .ok result1 ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel = .ok result2 ∧
    opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.etyp = result_etyp := by
  intro _h_typecheck
  -- This lemma extracts the structure from a successful typecheckOp.
  -- The proof requires:
  -- 1. Unfolding typecheckOp and handling the fuel case split
  -- 2. Handling the monadic bind for typecheckExpr ctx e1 fuel
  -- 3. Handling the destructuring: let ⟨etyp1, p1, _⟩ := result1.qualType
  -- 4. Handling the monadic bind for typecheckExpr ctx' e2 fuel
  -- 5. Handling the destructuring: let ⟨etyp2, p2, _⟩ := result2.qualType
  -- 6. Handling the match on opEType? op etyp1 etyp2
  -- 7. Extracting the field equalities from: return { result2 with qualType := qt }
  --
  -- The structure is sound and the proof is feasible, but requires careful
  -- handling of multiple nested splits and destructurings in the monadic code.
  sorry

-- Helper lemma for binary operations using inductive hypothesis
private lemma preservation_op (e1 e2 : Expr) (op : Op) (ctx : TypeContext)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext) (fuel_tc : Nat) (res : TypeResult)
          (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value),
          typecheck ctx e fuel_tc = .ok res →
          runtimeInstantiatesCtx ctx μ₀ ρ₀ →
          ∀ (verbose : Bool),
            LeanPoison.beval m { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ } e verbose =
              pure (.success { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) →
            valueHasETyp v res.qualType.etyp ∧
            runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁)
    (n : Nat) :
    Preservation (Expr.op e1 op e2) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₃ ρ₀ ρ₃ l₀ l₃ pm₀ pm₃ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  -- Evaluation of binary operation
  cases fuel_eval with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    -- Typecheck for op
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Use helper lemma to extract typechecking structure
      have ⟨result1, result2, result_etyp, h_tc1, h_tc2, h_op_etyp, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckOp_structure ctx e1 e2 op fuel_tc' res h_typecheck

      -- Use helper lemma to extract evaluation structure
      -- Apply bevalOp_structure BEFORE any simplification
      -- Note: fuel_eval = fuel'.succ in this branch
      -- We pass the enriched types from typechecking to establish type relationships
      have ⟨config₁, config₂, v1, v2, h_eval1, h_eval2, h_v1_type, h_v2_type, h_v_type⟩ :=
        bevalOp_structure e1 e2 op fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₃, varEnv := ρ₃, nextLoc := l₃, pureMode := pm₃ }
          v result1.qualType.etyp result2.qualType.etyp result_etyp
          h_eval h_op_etyp

      -- Use beval_preserves_varEnv to show varEnv is unchanged at each step
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv12 : config₁.varEnv = config₂.varEnv :=
        beval_preserves_varEnv e2 fuel' verbose
          config₁ config₂ v2 h_eval2
      have h_varenv_unchanged : ρ₀ = ρ₃ :=
        beval_preserves_varEnv (Expr.op e1 op e2) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₃, varEnv := ρ₃, nextLoc := l₃, pureMode := pm₃ }
          v h_eval

      -- Use the varEnv equalities to simplify
      -- h_varenv01 : ρ₀ = config₁.varEnv, so we can eliminate ρ₀
      -- h_varenv_unchanged : ρ₀ = ρ₃, so we can eliminate ρ₃
      -- (h_varenv12 has field projections on both sides, so we keep it for rewriting)
      subst h_varenv01 h_varenv_unchanged
      -- Now ρ₀ and ρ₃ are replaced by config₁.varEnv
      -- Goal is: valueHasETyp v res.qualType.etyp ∧ runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₃ config₁.varEnv

      -- Now we have both typecheck and beval deconstructed!
      -- After subst: ρ₀ and ρ₃ are replaced by config₁.varEnv
      --
      -- Typechecking structure:
      --   h_tc1: typecheck e1 succeeds with result1
      --   h_tc2: typecheck e2 succeeds with result2
      --   h_op_etyp: opEType? produces result_etyp
      --   Field equalities: h_mem, h_tag, h_loc, h_ntag, h_etyp
      -- Evaluation structure (with types):
      --   h_eval1: e1 evaluates to v1 with config₁
      --   h_eval2: e2 evaluates to v2 with config₂
      --   h_v1_type: v1 has type result1.qualType.etyp
      --   h_v2_type: v2 has type result2.qualType.etyp
      --   h_v_type: v has type result_etyp
      -- VarEnv preservation:
      --   h_varenv12: config₁.varEnv = config₂.varEnv
      --   After subst: ρ₀ = config₁.varEnv and ρ₃ = config₁.varEnv
      --
      -- Goal is now: valueHasETyp v res.qualType.etyp ∧
      --              runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₃ config₁.varEnv
      --
      -- Next steps (TODO):
      -- 1. Use h_v_type and h_etyp to show v has the correct type (res.qualType.etyp)
      -- 2. Show runtimeInstantiatesCtx for the output state (μ₃, config₁.varEnv)
      --    Since config₁.varEnv was the original ρ₀ (from h_instantiate), this should follow
      sorry

-- Private lemma for var case
private lemma preservation_var (x : Name) (ctx : TypeContext) : Preservation (Expr.var x) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  -- Variable lookup: if x typechecks, then x is in ctx.varEnv
  -- and runtimeInstantiatesCtx ensures x is in ρ with correct type
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  simp [LeanPoison.beval] at h_eval
  apply congrFun (a := ()) at h_eval
  cases fuel_eval with
  | zero => cases h_eval
  | succ fuel' =>
    -- When fuel > 0, beval looks up x in ρ
    cases fuel_tc with
    | zero =>
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp [typecheck, typecheckExpr] at h_typecheck
      -- Typecheck for var looks up x in ctx.varEnv
      cases h_lookup : ctx.varEnv.lookup x with
      | none =>
        -- If x is not in ctx.varEnv, typechecking fails
        simp [typecheckVar, h_lookup] at h_typecheck
      | some qt =>
        -- If x is in ctx.varEnv, then by runtimeInstantiatesCtx, x is in ρ with correct type
        have ⟨v_found, h_v, h_typ⟩ := var_has_correct_type ctx μ₀ ρ₀ x qt h_instantiate h_lookup
        -- Now beval will find v_found in ρ and return success
        simp [h_v] at h_eval
        injection h_eval with h_eq_config h_eq_val
        cases h_eq_config
        cases h_eq_val
        -- Now we need to show that the typechecking result matches
        -- At this point, h_typecheck : typecheckVar ctx x = .ok res
        -- Use helper lemma to show res.qualType.etyp = qt.etyp
        have h_etyp_eq := typecheckVar_preserves_etyp ctx x qt res h_lookup h_typecheck
        constructor
        · -- First branch: valueHasETyp v res.qualType.etyp
          rw [h_etyp_eq]
          exact h_typ
        · -- Second branch: runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁
          -- For variables, evaluation doesn't change the config
          -- From h_eval, we know the config is unchanged: μ₁ = μ₀, ρ₁ = ρ₀
          -- From typecheckVar, we know res.memEnv' = ctx.memEnv
          -- Therefore, we need to show: runtimeInstantiatesCtx ctx μ₀ ρ₀
          -- which is exactly h_instantiate
          -- First, show that res.memEnv' = ctx.memEnv
          -- All branches of typecheckVar return memEnv' := ctx.memEnv
          have h_memenv := typecheckVar_preserves_memEnv ctx x res h_typecheck
          -- Now simplify the goal using h_memenv
          rw [h_memenv]
          -- The goal is now: runtimeInstantiatesCtx { ctx with memEnv := ctx.memEnv } μ₀ ρ₀
          -- which is definitionally equal to: runtimeInstantiatesCtx ctx μ₀ ρ₀
          exact h_instantiate

-- Preservation theorem: well-typed programs preserve types
-- This proof uses strong induction on fuel_eval
theorem preservation (e : Expr) (ctx : TypeContext) : Preservation e ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  -- Extract fuel from terminatesTo
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  -- Strong induction on fuel_eval
  revert e ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_eval verbose
  induction fuel_eval using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate verbose h_eval
    -- Reconstruct h_terminates from h_eval
    have h_terminates : terminatesTo e { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                                       { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v := by
      exact ⟨n, verbose, h_eval⟩
    -- The proof proceeds by case analysis on the expression
    cases e with
    | num n =>
      -- Numeric literals
      have h_pres := preservation_num n ctx
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | bool b =>
      -- Boolean literals
      have h_pres := preservation_bool b ctx
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | unit =>
      -- Unit literal
      have h_pres := preservation_unit ctx
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | str s =>
      -- String literals
      have h_pres := preservation_str s ctx
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | var x =>
      -- Variable lookup: if x is typed and in ρ, lookup returns a value of correct type
      have h_pres := preservation_var x ctx
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | op e1 op e2 =>
      -- Binary operations: by IH, operands have correct types, so result has expected type
      have h_pres := preservation_op e1 e2 op ctx IH n
      unfold Preservation at h_pres
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | unaryop op e1 =>
      -- Unary operations: similar to binary operations
      sorry
    | ite e1 e2 e3 =>
      -- Conditionals: by IH, e1 evaluates to bool, then either e2 or e3 preserves types
      sorry
    | newRef e1 =>
      -- Reference creation: by IH, e1 has correct type, fresh location added to contexts
      sorry
    | assign e1 e2 =>
      -- Assignment: by IH, e1 evaluates to location, e2 to value of correct type
      sorry
    | deref e1 =>
      -- Dereference: by IH, e1 evaluates to location, memory lookup returns correct type
      sorry
    | seq e1 e2 =>
      -- Sequence: by IH, e2 preserves types (e1's result is discarded)
      sorry
    | kwhile e1 e2 =>
      -- While loops: requires fixpoint reasoning about typing context evolution
      sorry
    | vlet x e1 e2 =>
      -- Let binding: by IH, e1 has correct type, e2 preserves types with extended context
      sorry
    | fn x paramType body returnType =>
      -- Function abstraction: creates closure value with correct arrow type
      sorry
    | pfn x paramType body returnType =>
      -- Pure function abstraction: creates pure closure with correct arrow type
      sorry
    | app e1 e2 =>
      -- Function application: by IH, e1 evaluates to closure, body preserves types
      sorry
    | rand e1 =>
      -- Random generation: by IH, e1 evaluates to number, result is int
      sorry
    | frand e1 =>
      -- Faulty random: similar to rand
      sorry
    | printInt e1 =>
      -- Print operations: by IH, e1 evaluates successfully, result is unit
      sorry
    | printString e1 =>
      -- Print string: similar to printInt
      sorry
