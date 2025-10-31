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
import LeanProofs.Properties

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

-- Parametric version of Preservation with explicit fuel
-- This is used internally for helper lemmas to avoid existential extraction issues
-- The standard Preservation uses terminatesTo (existential fuel), but for inductive
-- proofs we need explicit fuel to match the induction variable
private def PreservationWithFuel (e : Expr) (ctx : TypeContext) (n : Nat) : Prop :=
  ∀ (fuel_tc : Nat) (res : TypeResult) (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv)
    (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value) (verbose : Bool),
    -- If typechecking succeeds
    typecheck ctx e fuel_tc = .ok res →
    -- And runtime instantiates the input context
    runtimeInstantiatesCtx ctx μ₀ ρ₀ →
    -- And evaluation terminates successfully with exactly fuel n
    LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ } e verbose =
      pure (.success { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) →
    -- Then the result value has the expected enriched type
    valueHasETyp v res.qualType.etyp ∧
    -- And the final runtime state instantiates the output typing context
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁

-- Lemma: PreservationWithFuel implies Preservation
private lemma preservationWithFuel_implies_preservation (e : Expr) (ctx : TypeContext) :
    (∀ n, PreservationWithFuel e ctx n) → Preservation e ctx := by
  intro h_pwf
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  exact h_pwf fuel_eval fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose
          h_typecheck h_instantiate h_eval

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
    valueHasETyp v result_etyp ∧
    config₂.memory = config₃.memory := by
  intro h_eval h_op_etyp
  -- Case analysis on fuel: if fuel = 0, beval returns outOfFuel, not success
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, contradicting h_eval
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- fuel > 0: proceed with evaluation
    -- Unfold beval for the op case
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    -- Convert function equality to point-wise equality
    apply congrFun (a := ()) at h_eval
    -- Simplify monadic bind operations
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Split on the result of evaluating e1 (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁ v₁ =>
        -- e1 evaluated successfully to config₁, v₁
        -- Unfold the nested bind for e2
        simp [EStateM.bind] at h_eval
        -- Split on the result of evaluating e2 (outer EStateM.Result)
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ v₂ =>
            -- e2 evaluated successfully to config₂, v₂
            -- Case analysis on evalOp result
            cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
            | some v_result =>
              -- evalOp succeeded
              simp [h_evalOp] at h_eval
              -- Expand pure to Result.ok for injection
              simp [pure] at h_eval
              -- Extract that v_result = v and config₂ = config₃
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result with h_eq_cfg h_eq_val
              -- Extract memory equality before subst (for return value)
              have h_mem_eq : config₂.memory = config₃.memory := by
                rw [h_eq_cfg]
              -- Rewrite h_evalOp to use v instead of v_result
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              -- Convert h_beval1 and h_beval2 to pure form
              have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
                funext _
                simp [pure]
                exact h_beval1
              have h_beval2' : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂ v₂) := by
                funext _
                simp [pure]
                exact h_beval2
              -- Prove type information from evalOp success and opEType? match
              have h_v1_type : valueHasETyp v₁ etyp1 := by
                -- Case analysis on op to determine expected value and type constructors
                cases op with
                | add | sub | mul | div | gte | lte | gt | lt | eq | neq | bitand =>
                  cases v₁ with
                  | num =>
                    cases v₂ with
                    | num =>
                      cases etyp1 with
                      | int =>
                        cases etyp2 with
                        | int =>
                          simp [LeanPoison.evalOp] at h_evalOp
                          simp [opEType?] at h_op_etyp
                          cases h_evalOp
                          cases h_op_etyp
                          constructor
                        | bool | unit | string | ref | arrow | parrow =>
                          simp [opEType?] at h_op_etyp
                      | bool | unit | string | ref | arrow | parrow =>
                        simp [opEType?] at h_op_etyp
                    | bool | unit | str | loc | closure | peClosure =>
                      simp [LeanPoison.evalOp] at h_evalOp
                  | bool | unit | str | loc | closure | peClosure =>
                    simp [LeanPoison.evalOp] at h_evalOp
                | and | or =>
                  cases v₁ with
                  | bool =>
                    cases v₂ with
                    | bool =>
                      cases etyp1 with
                      | bool =>
                        cases etyp2 with
                        | bool =>
                          simp [LeanPoison.evalOp] at h_evalOp
                          simp [opEType?] at h_op_etyp
                          cases h_evalOp
                          cases h_op_etyp
                          constructor
                        | int | unit | string | ref | arrow | parrow =>
                          simp [opEType?] at h_op_etyp
                      | int | unit | string | ref | arrow | parrow =>
                        simp [opEType?] at h_op_etyp
                    | num | unit | str | loc | closure | peClosure =>
                      simp [LeanPoison.evalOp] at h_evalOp
                  | num | unit | str | loc | closure | peClosure =>
                    simp [LeanPoison.evalOp] at h_evalOp
              have h_v2_type : valueHasETyp v₂ etyp2 := by
                cases op with
                | add | sub | mul | div | gte | lte | gt | lt | eq | neq | bitand =>
                  cases v₁ with
                  | num =>
                    cases v₂ with
                    | num =>
                      cases etyp1 with
                      | int =>
                        cases etyp2 with
                        | int =>
                          simp [LeanPoison.evalOp] at h_evalOp
                          simp [opEType?] at h_op_etyp
                          cases h_evalOp
                          cases h_op_etyp
                          constructor
                        | bool | unit | string | ref | arrow | parrow =>
                          simp [opEType?] at h_op_etyp
                      | bool | unit | string | ref | arrow | parrow =>
                        simp [opEType?] at h_op_etyp
                    | bool | unit | str | loc | closure | peClosure =>
                      simp [LeanPoison.evalOp] at h_evalOp
                  | bool | unit | str | loc | closure | peClosure =>
                    simp [LeanPoison.evalOp] at h_evalOp
                | and | or =>
                  cases v₁ with
                  | bool =>
                    cases v₂ with
                    | bool =>
                      cases etyp1 with
                      | bool =>
                        cases etyp2 with
                        | bool =>
                          simp [LeanPoison.evalOp] at h_evalOp
                          simp [opEType?] at h_op_etyp
                          cases h_evalOp
                          cases h_op_etyp
                          constructor
                        | int | unit | string | ref | arrow | parrow =>
                          simp [opEType?] at h_op_etyp
                      | int | unit | string | ref | arrow | parrow =>
                        simp [opEType?] at h_op_etyp
                    | num | unit | str | loc | closure | peClosure =>
                      simp [LeanPoison.evalOp] at h_evalOp
                  | num | unit | str | loc | closure | peClosure =>
                    simp [LeanPoison.evalOp] at h_evalOp
              have h_v_type : valueHasETyp v result_etyp :=
                evalOp_preserves_type op v₁ v₂ etyp1 etyp2 result_etyp h_v1_type h_v2_type h_op_etyp v h_evalOp
              -- Note: fuel' + 1 - 1 = fuel' by arithmetic
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, config₂, v₁, v₂, h_beval1', h_beval2', h_v1_type, h_v2_type, h_v_type, h_mem_eq⟩
            | none =>
              -- evalOp returned none - contradiction with success
              simp [h_evalOp] at h_eval
              simp [pure] at h_eval
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result
          · next =>
            -- e2 evaluation returned outOfFuel - contradiction
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next msg =>
            -- e2 evaluation returned runtimeError - contradiction
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
        · next h_error2 h_state2 =>
          -- e2 evaluation returned error from EStateM - contradiction
          injection h_eval
      · next =>
        -- e1 evaluation returned outOfFuel - contradiction
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError - contradiction
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM - contradiction
      injection h_eval

-- Helper lemma: extract structure from typecheckOp
-- Note: The subexpression typechecks use (fuel - 1) because typecheckOp
-- decrements fuel before calling typecheckExpr internally.
-- When fuel = 0, typecheckOp returns error, so this is safe.
private lemma typecheckOp_structure (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat) (res : TypeResult) :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ∃ (result1 result2 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 (fuel - 1) = .ok result2 ∧
    opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.etyp = result_etyp := by
  intro h_typecheck
  -- Case analysis on fuel
  cases fuel with
  | zero =>
    -- When fuel = 0, typecheckOp returns error "Out of fuel", not ok
    simp [typecheckOp] at h_typecheck
  | succ fuel' =>
    -- When fuel > 0, unfold typecheckOp
    unfold typecheckOp at h_typecheck
    simp at h_typecheck
    -- Case analysis on typecheckExpr ctx e1 fuel'
    cases h_tc1_result : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      -- e1 typechecked successfully
      -- Rewrite h_typecheck with this case
      simp [h_tc1_result, bind, Except.bind] at h_typecheck
      -- The match on result1.qualType should now be visible
      -- Split on the structure of result1.qualType to reduce the match
      match h_qt1 : result1.qualType with
      | QTyp.mk etyp1 p1 pred1 =>
        -- Rewrite the match expression in h_typecheck
        rw [h_qt1] at h_typecheck
        simp at h_typecheck
        -- Now case analysis on typecheckExpr ctx' e2 fuel'
        cases h_tc2_result : typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                                       nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel' with
        | ok result2 =>
          -- e2 typechecked successfully
          simp [h_tc2_result] at h_typecheck
          -- Match on result2.qualType to reduce its match
          match h_qt2 : result2.qualType with
          | QTyp.mk etyp2 p2 pred2 =>
            rw [h_qt2] at h_typecheck
            simp at h_typecheck
            -- Case analysis on opEType? op etyp1 etyp2
            cases h_opEType_result : opEType? op etyp1 etyp2 with
            | some result_etyp =>
              -- opEType? succeeded
              simp [h_opEType_result] at h_typecheck
              -- Now h_typecheck should be: Except.ok { result2 with qualType := ... } = Except.ok res
              injection h_typecheck with h_res_eq
              -- After injection, res = { result2 with qualType := ... }
              -- Construct the existential proof
              -- Note: fuel = fuel' + 1, so fuel - 1 = fuel' (by Nat.add_sub_cancel)
              -- First prepare the opEType? equality with correct projections
              have h_opEType_final : opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp := by
                rw [h_qt1, h_qt2]
                exact h_opEType_result
              -- Now provide the existential
              simp only [Nat.add_sub_cancel]
              subst h_res_eq
              exact ⟨result1, result2, result_etyp,
                      h_tc1_result,
                      h_tc2_result,
                      h_opEType_final,
                      rfl, rfl, rfl, rfl, rfl⟩
            | none =>
              -- opEType? returned none, so typecheckOp throws error (contradiction)
              simp [h_opEType_result] at h_typecheck
        | error msg2 =>
          -- e2 typechecking failed, so the bind returns error (contradiction with ok res)
          -- After rewriting with h_tc2_result, h_typecheck simplifies to Except.error _ = Except.ok _
          simp [h_tc2_result] at h_typecheck
    | error msg =>
      -- e1 typechecking failed, so the bind returns error (contradiction with ok res)
      -- After rewriting with h_tc1_result, h_typecheck simplifies to Except.error _ = Except.ok _
      simp [h_tc1_result, bind, Except.bind] at h_typecheck


-- Helper lemma for binary operations using inductive hypothesis
-- Uses PreservationWithFuel to avoid existential extraction issues
private lemma preservation_op (e1 e2 : Expr) (op : Op) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.op e1 op e2) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₃ ρ₀ ρ₃ l₀ l₃ pm₀ pm₃ v verbose h_typecheck h_instantiate h_eval
  -- Now h_eval uses exactly fuel n (no existential extraction!)
  -- We can work directly with n throughout the proof
  -- Evaluation of binary operation
  cases n with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    -- In this branch, n = fuel'.succ (by pattern matching)
    -- So we have fuel' < fuel'.succ = n, which is exactly what we need for IH!
    -- Typecheck for op
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Use helper lemma to extract typechecking structure
      have ⟨result1, result2, result_etyp, h_tc1, h_tc2, h_op_etyp, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckOp_structure ctx e1 e2 op fuel_tc' res h_typecheck

      -- Use helper lemma to extract evaluation structure
      -- Note: n = fuel'.succ in this branch, and h_eval uses fuel n
      -- We pass the enriched types from typechecking to establish type relationships
      -- Now bevalOp_structure also returns the memory equality: config₂.memory = μ₃
      obtain ⟨config₁, config₂, v1, v2, h_eval1, h_eval2, h_v1_type, h_v2_type, h_v_type, h_mem_eq⟩ :=
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

      constructor

      -- Part 1: Prove valueHasETyp v res.qualType.etyp
      · -- We have h_v_type: valueHasETyp v result_etyp
        -- and h_etyp: res.qualType.etyp = result_etyp
        rw [h_etyp]
        exact h_v_type

      -- Part 2: Prove runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₃ config₁.varEnv
      · -- Strategy: Apply IH to e1 and e2 to get intermediate runtimeInstantiatesCtx facts,
        -- then use the fact that binary ops don't modify memory/varEnv

        -- Prove fuel constraints for IH application
        -- In this branch, n = fuel'.succ (by pattern matching on n)
        -- So fuel' < fuel'.succ = n holds definitionally
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'

        -- Convert h_tc1 to use typecheck wrapper (PreservationWithFuel expects typecheck, not typecheckExpr)
        -- Since typecheck is just typecheckExpr with the same fuel, and h_tc1 uses (fuel_tc' - 1),
        -- we just unfold typecheck and use h_tc1 directly
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1

        -- Apply IH to e1 using PreservationWithFuel with fuel (fuel_tc' - 1)
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1

        -- Convert h_tc2 similarly
        have h_tc2' : typecheck { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                           nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 (fuel_tc' - 1) = .ok result2 := by
          simp [typecheck]
          exact h_tc2

        -- Apply IH to e2 with the updated context from result1, using fuel (fuel_tc' - 1)
        let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                               nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
        have IH2 := IH fuel' h_fuel e2 ctx' (fuel_tc' - 1) result2
                      config₁.memory config₂.memory config₁.varEnv config₂.varEnv
                      config₁.nextLoc config₂.nextLoc config₁.pureMode config₂.pureMode v2 verbose
                      h_tc2' h_runtime1 h_eval2
        obtain ⟨_, h_runtime2⟩ := IH2

        -- Now h_runtime2 gives us that config₂ satisfies the context after e2
        -- We need to show that μ₃ and config₁.varEnv satisfy the final context

        -- The goal is about the context with res's fields
        -- Rewrite using field equalities: res.memEnv' = result2.memEnv', etc.
        simp only [h_mem]

        -- The goal is now: runtimeInstantiatesCtx
        --   { ctx with memEnv := result2.memEnv', ... } μ₃ config₁.varEnv
        -- We have h_runtime2: runtimeInstantiatesCtx
        --   { ctx' with memEnv := result2.memEnv' } config₂.memory config₂.varEnv

        -- Use memory monotonicity to show μ₃ contains all locations that config₂ contains
        -- Since binary operations don't allocate memory, and evalOp just computes a value,
        -- the final memory has the same locations as config₂.memory

        -- First, use h_varenv12 to change config₂.varEnv to config₁.varEnv in h_runtime2
        -- h_varenv12 : config₁.varEnv = config₂.varEnv
        rw [← h_varenv12] at h_runtime2
        -- Now h_runtime2: runtimeInstantiatesCtx {...} config₂.memory config₁.varEnv

        -- Unfold runtimeInstantiatesCtx to work with its components
        unfold runtimeInstantiatesCtx at h_runtime2 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime2
        constructor

        · -- Memory containment part: show μ₃ contains all required locations
          intro l h_memenv_contains
          have h_config2_contains := h_mem2 l h_memenv_contains

          -- Use h_mem_eq from bevalOp_structure: config₂.memory = config₃.memory
          -- Simplify to get config₂.memory = μ₃
          have h_mem_equality : config₂.memory = μ₃ := by
            simp at h_mem_eq
            exact h_mem_eq

          rw [← h_mem_equality]
          exact h_config2_contains

        · -- VarEnv part: show config₁.varEnv satisfies type requirements
          intro x qt h_lookup
          exact h_var2 h_lookup

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

-- Helper: prove PreservationWithFuel for all expressions and all fuel values
-- Combined directly into the main theorem via strong induction
private lemma preservationWithFuel_all : ∀ (n : Nat) (e : Expr) (ctx : TypeContext),
    PreservationWithFuel e ctx n := by
  intro n
  -- Strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro e ctx
    -- The proof proceeds by case analysis on the expression
    cases e with
    | num n_val =>
      -- Numeric literals - convert from Preservation to PreservationWithFuel
      unfold PreservationWithFuel
      intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
      have h_pres := preservation_num n_val ctx
      unfold Preservation at h_pres
      have h_term : terminatesTo (Expr.num n_val) _ _ v := ⟨n, verbose, h_eval⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | bool b =>
      -- Boolean literals
      unfold PreservationWithFuel
      intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
      have h_pres := preservation_bool b ctx
      unfold Preservation at h_pres
      have h_term : terminatesTo (Expr.bool b) _ _ v := ⟨n, verbose, h_eval⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | unit =>
      -- Unit literal
      unfold PreservationWithFuel
      intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
      have h_pres := preservation_unit ctx
      unfold Preservation at h_pres
      have h_term : terminatesTo Expr.unit _ _ v := ⟨n, verbose, h_eval⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | str s =>
      -- String literals
      unfold PreservationWithFuel
      intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
      have h_pres := preservation_str s ctx
      unfold Preservation at h_pres
      have h_term : terminatesTo (Expr.str s) _ _ v := ⟨n, verbose, h_eval⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | var x =>
      -- Variable lookup: if x is typed and in ρ, lookup returns a value of correct type
      unfold PreservationWithFuel
      intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
      have h_pres := preservation_var x ctx
      unfold Preservation at h_pres
      have h_term : terminatesTo (Expr.var x) _ _ v := ⟨n, verbose, h_eval⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | op e1 op e2 =>
      -- Binary operations: by IH, operands have correct types, so result has expected type
      exact preservation_op e1 e2 op ctx n IH
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

-- Preservation theorem: well-typed programs preserve types
-- This proof uses strong induction on fuel via preservationWithFuel_all
theorem preservation (e : Expr) (ctx : TypeContext) : Preservation e ctx :=
  preservationWithFuel_implies_preservation e ctx (preservationWithFuel_all · e ctx)
