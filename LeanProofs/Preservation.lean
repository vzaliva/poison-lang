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
import LeanProofs.Equality

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

-- Helper lemma: extract structure from typecheckUnaryOp
private lemma typecheckUnaryOp_structure (ctx : TypeContext) (op : UnaryOp) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckUnaryOp ctx op e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    opUnaryEType? op result1.qualType.etyp = some result_etyp ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = result_etyp := by
  intro h_typecheck
  cases fuel with
  | zero =>
    simp [typecheckUnaryOp] at h_typecheck
  | succ fuel' =>
    unfold typecheckUnaryOp at h_typecheck
    simp at h_typecheck
    cases h_tc1_result : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1_result, bind, Except.bind] at h_typecheck
      match h_qt1 : result1.qualType with
      | QTyp.mk etyp1 p1 pred1 =>
        rw [h_qt1] at h_typecheck
        simp at h_typecheck
        cases h_opEType_result : opUnaryEType? op etyp1 with
        | some result_etyp =>
          simp [h_opEType_result] at h_typecheck
          injection h_typecheck with h_res_eq
          have h_opEType_final : opUnaryEType? op result1.qualType.etyp = some result_etyp := by
            rw [h_qt1]
            exact h_opEType_result
          simp only [Nat.add_sub_cancel]
          subst h_res_eq
          exact ⟨result1, result_etyp, h_tc1_result, h_opEType_final, rfl, rfl, rfl, rfl, rfl⟩
        | none =>
          simp [h_opEType_result] at h_typecheck
    | error msg =>
      simp [h_tc1_result, bind, Except.bind] at h_typecheck

-- Helper lemma: evalUnaryOp preserves type correctness
private lemma evalUnaryOp_preserves_type (op : UnaryOp) (v1 : Value) (etyp1 result_etyp : ETyp) :
  valueHasETyp v1 etyp1 →
  opUnaryEType? op etyp1 = some result_etyp →
  ∀ v, LeanPoison.evalUnaryOp op v1 = some v → valueHasETyp v result_etyp := by
  intro h_typ1 h_op_type v h_eval
  cases op with
  | not =>
    -- opUnaryEType? only returns some for bool -> bool
    -- Case analyze etyp1 to simplify the match
    cases etyp1 with
    | bool =>
      -- opUnaryEType? UnaryOp.not ETyp.bool = some ETyp.bool
      simp [opUnaryEType?] at h_op_type
      -- Now h_op_type : some ETyp.bool = some result_etyp
      cases h_op_type
      -- Now result_etyp = ETyp.bool
      cases h_typ1 with
      | bool =>
        simp [LeanPoison.evalUnaryOp] at h_eval
        cases h_eval
        constructor
    | int | unit | string | ref _ _ | arrow _ _ _ _ | parrow _ _ _ _ =>
      -- opUnaryEType? returns none for these, contradiction
      simp [opUnaryEType?] at h_op_type

-- Helper lemma: extract evaluation structure from successful beval of unary operation
private lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) (etyp1 result_etyp : ETyp) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose =
    pure (.success config₂ v) →
  opUnaryEType? op etyp1 = some result_etyp →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config₁ v1) ∧
    valueHasETyp v1 etyp1 ∧
    valueHasETyp v result_etyp ∧
    config₁.memory = config₂.memory ∧
    config₁.varEnv = config₂.varEnv := by
  intro h_eval h_op_etyp
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config₁ v₁ =>
        cases h_evalOp : LeanPoison.evalUnaryOp op v₁ with
        | some v_result =>
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_cfg h_eq_val
          have h_mem_eq : config₁.memory = config₂.memory := by
            rw [h_eq_cfg]
          have h_varenv_eq : config₁.varEnv = config₂.varEnv := by
            rw [h_eq_cfg]
          rw [h_eq_val] at h_evalOp
          subst h_eq_cfg
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Prove type information
          -- Since evalUnaryOp succeeded, we know v₁ must be bool (only case for not)
          -- Since opUnaryEType? returned some, we know etyp1 must be bool
          have h_v1_type : valueHasETyp v₁ etyp1 := by
            cases op with
            | not =>
              -- opUnaryEType? only returns some for bool -> bool
              -- Case analyze on etyp1 to determine it must be bool
              cases etyp1 with
              | bool =>
                -- Since evalUnaryOp returned some for not, v₁ must be Value.bool
                cases v₁ with
                | bool =>
                  constructor
                | num | unit | str | loc _ | closure _ _ _ | peClosure _ _ _ =>
                  simp [LeanPoison.evalUnaryOp] at h_evalOp
              | int | unit | string | ref _ _ | arrow _ _ _ _ | parrow _ _ _ _ =>
                -- opUnaryEType? returns none for these, contradiction
                simp [opUnaryEType?] at h_op_etyp
          -- Now use the helper lemma to get v has the result type
          have h_v_type : valueHasETyp v result_etyp :=
            evalUnaryOp_preserves_type op v₁ etyp1 result_etyp h_v1_type h_op_etyp v h_evalOp
          simp only [Nat.add_sub_cancel]
          exact ⟨config₁, v₁, h_beval1', h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩
        | none =>
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result
      · next =>
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      injection h_eval


-- Helper lemma for unary operations using inductive hypothesis
private lemma preservation_unaryop (op : UnaryOp) (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.unaryop op e1) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₂ ρ₀ ρ₂ l₀ l₂ pm₀ pm₂ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, result_etyp, h_tc1, h_op_etyp, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckUnaryOp_structure ctx op e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalUnaryOp_structure op e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextLoc := l₂, pureMode := pm₂ }
          v result1.qualType.etyp result_etyp
          h_eval h_op_etyp

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv_unchanged : ρ₀ = ρ₂ :=
        beval_preserves_varEnv (Expr.unaryop op e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextLoc := l₂, pureMode := pm₂ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1
        simp only [h_mem]
        -- Use memory equality
        have h_mem_equality : config₁.memory = μ₂ := by
          exact h_mem_eq
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime1
        constructor
        · intro l h_memenv_contains
          have h_config1_contains := h_mem2 l h_memenv_contains
          rw [← h_mem_equality]
          exact h_config1_contains
        · intro x qt h_lookup
          exact h_var2 h_lookup

-- Helper lemma: extract evaluation structure from successful beval of sequence
-- This lemma mirrors typecheckSeq_structure but for evaluation.
-- For seq, e1 is evaluated and its result is discarded, then e2 is evaluated.
private lemma bevalSeq_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose =
    pure (.success config₂ v) →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config₁ v1) ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose = pure (.success config₂ v) := by
  intro h_eval
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config₁ v₁ =>
        -- e1 evaluated successfully, now e2
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          split at h_eval
          · next config₂' v₂ =>
            -- e2 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_cfg h_eq_val
            -- Convert to pure form before subst
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval2' : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Now subst to get final config and value
            subst h_eq_cfg h_eq_val
            simp only [Nat.add_sub_cancel]
            exact ⟨config₁, v₁, h_beval1', h_beval2'⟩
          · next =>
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next msg =>
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
        · next h_error2 h_state2 =>
          injection h_eval
      · next =>
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      injection h_eval

-- Helper lemma: extract structure from typecheckRand
private lemma typecheckRand_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckRand ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.int ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.int := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckRand at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckRand at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      match h_qt : result1.qualType with
      | QTyp.mk etyp poison pred =>
        rw [h_qt] at h_typecheck
        -- Now we need to check if etyp = ETyp.int or not
        by_cases h_cond : etyp = ETyp.int
        case pos =>
          -- etyp = ETyp.int, so the if-statement takes the else branch
          simp [h_cond, pure, Except.pure] at h_typecheck
          -- h_typecheck: the constructed result equals res
          -- Build the existential witness
          use result1
          constructor
          · exact h_tc1
          constructor
          · rw [h_qt]; simp; exact h_cond
          · rw [← h_typecheck]; simp
        case neg =>
          -- etyp != ETyp.int, so the if-statement takes the then branch (throws error)
          simp [h_cond, throw] at h_typecheck
    | error msg =>
      simp [h_tc1] at h_typecheck

-- Helper lemma: extract structure from typecheckFrand
private lemma typecheckFrand_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckFrand ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.int ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' + 1 ∧
    res.qualType.etyp = ETyp.int ∧
    res.qualType.poison = true := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckFrand at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckFrand at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      match h_qt : result1.qualType with
      | QTyp.mk etyp poison pred =>
        rw [h_qt] at h_typecheck
        -- Check if etyp = ETyp.int
        by_cases h_cond : etyp = ETyp.int
        case pos =>
          -- etyp = ETyp.int, so the if-statement takes the else branch
          simp only [h_cond, generateFreshTagRes] at h_typecheck
          -- The toPExpr bind will succeed for the specific expression structure
          -- After all simplification, h_typecheck should give us the structure
          cases h_toPExpr : ((Expr.op (Expr.op (Expr.var (generateFreshVar ctx "limit" 0 fuel')) Op.gte (Expr.num 0)) Op.and
                                 (Expr.op (Expr.var (generateFreshVar ctx "limit" 0 fuel')) Op.lte e1)).toPExpr) with
          | error err =>
            simp [h_toPExpr] at h_typecheck
          | ok predBody =>
            simp [h_toPExpr, pure, Except.pure] at h_typecheck
            -- Build the existential witness
            use result1
            constructor
            · exact h_tc1
            constructor
            · rw [h_qt]; simp; exact h_cond
            · rw [← h_typecheck]; simp
        case neg =>
          -- etyp != ETyp.int, so throws error
          simp [h_cond, throw] at h_typecheck
    | error msg =>
      simp [h_tc1] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of rand
private lemma bevalRand_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.rand e1) verbose =
    pure (.success config₁ v) →
  ∃ (config' : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config' v1) ∧
    valueHasETyp v1 ETyp.int ∧
    valueHasETyp v ETyp.int ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind, pure] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config' v₁ =>
        -- Check what v₁ is: must be Value.num for success path
        split at h_eval
        . next h_nonneg =>
           simp [Functor.map, EStateM.map] at h_eval
           split at h_eval
           · next p_result p_state =>
             simp [EStateM.pure] at h_eval
             rcases h_eval with ⟨⟨h_eq_cfg, h_eq_val⟩, h_eq_res⟩
             subst h_eq_cfg h_eq_val
             have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num v₁)) := by
               funext _
               simp [pure]
               exact h_beval1
             simp only [Nat.add_sub_cancel]
             exact ⟨config', Value.num v₁, h_beval1', valueHasETyp.num _, valueHasETyp.num _, rfl, rfl⟩
           · next p_error p_state =>
             -- IO operation failed, but we succeeded - contradiction
             simp [EStateM.pure] at h_eval
        . next h_neg =>
          -- After the println and return runtimeError
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval <;> simp [EStateM.pure] at h_eval
      all_goals {
        -- All error cases: simp closes the goal
        simp [EStateM.pure] at h_eval
      }
    · next h_error1 h_state1 =>
      -- EStateM.error - contradiction with success
      cases h_eval

-- Helper lemma: extract evaluation structure from successful beval of frand
private lemma bevalFrand_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.frand e1) verbose =
    pure (.success config₁ v) →
  ∃ (config' : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config' v1) ∧
    valueHasETyp v1 ETyp.int ∧
    valueHasETyp v ETyp.int ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind, pure] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config' v₁ =>
        -- Check what v₁ is: must be Value.num for success path
        split at h_eval
        . next h_nonneg =>
           simp [Functor.map, EStateM.map] at h_eval
           split at h_eval
           · next p_result p_state =>
             simp [EStateM.pure] at h_eval
             rcases h_eval with ⟨⟨h_eq_cfg, h_eq_val⟩, h_eq_res⟩
             subst h_eq_cfg h_eq_val
             have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num v₁)) := by
               funext _
               simp [pure]
               exact h_beval1
             simp only [Nat.add_sub_cancel]
             exact ⟨config', Value.num v₁, h_beval1', valueHasETyp.num _, valueHasETyp.num _, rfl, rfl⟩
           · next p_error p_state =>
             -- IO operation failed, but we succeeded - contradiction
             simp [EStateM.pure] at h_eval
        . next h_neg =>
          -- After the println and return runtimeError
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval <;> simp [EStateM.pure] at h_eval
      all_goals {
        -- All error cases: simp closes the goal
        simp [EStateM.pure] at h_eval
      }
    · next h_error1 h_state1 =>
      -- EStateM.error - contradiction with success
      cases h_eval

-- Helper lemma: extract structure from typecheckPrintInt
private lemma typecheckPrintInt_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintInt ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.int ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckPrintInt at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckPrintInt at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      match h_qt : result1.qualType with
      | QTyp.mk etyp poison pred =>
        rw [h_qt] at h_typecheck
        by_cases h_cond : etyp = ETyp.int
        case pos =>
          simp [h_cond, pure, Except.pure] at h_typecheck
          use result1
          constructor
          · exact h_tc1
          constructor
          · rw [h_qt]; simp; exact h_cond
          · rw [← h_typecheck]; simp
        case neg =>
          simp [h_cond, throw] at h_typecheck
    | error msg =>
      simp [h_tc1] at h_typecheck

-- Helper lemma: extract structure from typecheckPrintString
private lemma typecheckPrintString_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintString ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.string ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckPrintString at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckPrintString at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      match h_qt : result1.qualType with
      | QTyp.mk etyp poison pred =>
        rw [h_qt] at h_typecheck
        by_cases h_cond : etyp = ETyp.string
        case pos =>
          simp [h_cond, pure, Except.pure] at h_typecheck
          use result1
          constructor
          · exact h_tc1
          constructor
          · rw [h_qt]; simp; exact h_cond
          · rw [← h_typecheck]; simp
        case neg =>
          simp [h_cond, throw] at h_typecheck
    | error msg =>
      simp [h_tc1] at h_typecheck

-- Helper lemma: extract evaluation structure from successful beval of printInt
private lemma bevalPrintInt_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.printInt e1) verbose =
    pure (.success config₁ v) →
  ∃ (config' : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config' v1) ∧
    valueHasETyp v1 ETyp.int ∧
    valueHasETyp v ETyp.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind, pure] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config' v₁ =>
        -- After the println, we return success
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          simp [EStateM.pure] at h_eval
          rcases h_eval with ⟨⟨h_eq_cfg, h_eq_val⟩, h_eq_res⟩
          subst h_eq_cfg h_eq_val
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num v₁)) := by
            funext _
            simp [pure]
            exact h_beval1
          simp only [Nat.add_sub_cancel]
          exact ⟨config', Value.num v₁, h_beval1', valueHasETyp.num _, valueHasETyp.unit, rfl, rfl⟩
        · next p_error p_state =>
          simp [EStateM.pure] at h_eval
      all_goals {
        simp [EStateM.pure] at h_eval
      }
    · next h_error1 h_state1 =>
      cases h_eval

-- Helper lemma: extract evaluation structure from successful beval of printString
private lemma bevalPrintString_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.printString e1) verbose =
    pure (.success config₁ v) →
  ∃ (config' : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose = pure (.success config' v1) ∧
    valueHasETyp v1 ETyp.string ∧
    valueHasETyp v ETyp.unit ∧
    config'.memory = config₁.memory ∧
    config'.varEnv = config₁.varEnv := by
  intro h_eval
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind, pure] at h_eval
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      split at h_eval
      · next config' v₁ =>
        -- After the println, we return success
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          simp [EStateM.pure] at h_eval
          rcases h_eval with ⟨⟨h_eq_cfg, h_eq_val⟩, h_eq_res⟩
          subst h_eq_cfg h_eq_val
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.str v₁)) := by
            funext _
            simp [pure]
            exact h_beval1
          simp only [Nat.add_sub_cancel]
          exact ⟨config', Value.str v₁, h_beval1', valueHasETyp.str _, valueHasETyp.unit, rfl, rfl⟩
        · next p_error p_state =>
          simp [EStateM.pure] at h_eval
      all_goals {
        simp [EStateM.pure] at h_eval
      }
    · next h_error1 h_state1 =>
      cases h_eval

-- Helper lemma for printInt
private lemma preservation_printInt (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.printInt e1) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckPrintInt_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalPrintInt_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.printInt e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1
        simp only [h_mem]
        -- Use memory equality
        have h_mem_equality : config₁.memory = μ₁ := h_mem_eq
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime1
        constructor
        · intro l h_memenv_contains
          have h_config1_contains := h_mem2 l h_memenv_contains
          rw [← h_mem_equality]
          exact h_config1_contains
        · intro x qt h_lookup
          exact h_var2 h_lookup

-- Helper lemma for printString (similar to printInt)
private lemma preservation_printString (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.printString e1) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckPrintString_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalPrintString_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.printString e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1
        simp only [h_mem]
        -- Use memory equality
        have h_mem_equality : config₁.memory = μ₁ := h_mem_eq
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime1
        constructor
        · intro l h_memenv_contains
          have h_config1_contains := h_mem2 l h_memenv_contains
          rw [← h_mem_equality]
          exact h_config1_contains
        · intro x qt h_lookup
          exact h_var2 h_lookup

-- Helper lemma for rand
private lemma preservation_rand (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.rand e1) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckRand_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalRand_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.rand e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1
        simp only [h_mem]
        -- Use memory equality
        have h_mem_equality : config₁.memory = μ₁ := h_mem_eq
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime1
        constructor
        · intro l h_memenv_contains
          have h_config1_contains := h_mem2 l h_memenv_contains
          rw [← h_mem_equality]
          exact h_config1_contains
        · intro x qt h_lookup
          exact h_var2 h_lookup

-- Helper lemma for frand (similar to rand)
private lemma preservation_frand (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.frand e1) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp, h_poison⟩ :=
        typecheckFrand_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalFrand_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.frand e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1
        obtain ⟨_, h_runtime1⟩ := IH1
        simp only [h_mem]
        -- Use memory equality
        have h_mem_equality : config₁.memory = μ₁ := h_mem_eq
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem2, h_var2⟩ := h_runtime1
        constructor
        · intro l h_memenv_contains
          have h_config1_contains := h_mem2 l h_memenv_contains
          rw [← h_mem_equality]
          exact h_config1_contains
        · intro x qt h_lookup
          exact h_var2 h_lookup

-- Helper lemma: extract structure from typecheckSeq
private lemma typecheckSeq_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' := by
  intro h_typecheck
  cases fuel with
  | zero =>
    simp [typecheckSeq] at h_typecheck
  | succ fuel' =>
    unfold typecheckSeq at h_typecheck
    simp at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      cases h_qt1: result1.qualType with
      | mk _etyp1 p1 pred1 =>
        rw [h_qt1] at h_typecheck
        simp at h_typecheck
        cases h_tc2: typecheckExpr { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv, tagEnv := result1.tagEnv',
                                     nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := ctx.pureCtx } e2 fuel'
        with
        | ok result2 =>
          simp [h_tc2] at h_typecheck
          cases h_qt2: result2.qualType with
          | mk _etyp2 p2 pred2 =>
            rw [h_qt2] at h_typecheck
            simp at h_typecheck
            simp [pure, Except.pure] at h_typecheck
            rcases h_typecheck
            simp_all
        | error err =>
          simp [h_tc2] at h_typecheck
    | error err =>
      simp [h_tc1] at h_typecheck


-- Helper lemma for sequencing
private lemma preservation_seq (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.seq e1 e2) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₂ ρ₀ ρ₂ l₀ l₂ pm₀ pm₂ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure using helper lemma
      have ⟨result1, result2, ctx', h_tc1, h_ctx_eq, h_tc2, h_etyp, h_mem, h_tag, h_loc, h_ntag⟩ :=
        typecheckSeq_structure ctx e1 e2 fuel_tc' res h_typecheck
      -- Extract evaluation structure using helper lemma
      obtain ⟨config₁, v1, h_eval1, h_eval2⟩ :=
        bevalSeq_structure e1 e2 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextLoc := l₂, pureMode := pm₂ }
          v h_eval

      -- Establish fuel constraint for IH
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'

      -- Apply IH to e1
      have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
        simp [typecheck]
        exact h_tc1
      -- Use beval_preserves_varEnv to establish varEnv equality
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1
      -- Rewrite to use config₁.varEnv
      rw [h_varenv01] at h_instantiate h_eval1
      -- Convert h_eval1 to explicit config₁ structure
      have h_eval1' : LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextLoc := l₀, pureMode := pm₀ } e1 verbose =
          pure (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextLoc := config₁.nextLoc, pureMode := config₁.pureMode } v1) := by
        convert h_eval1
      have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextLoc pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1'
      obtain ⟨_, h_runtime1⟩ := IH1

      -- Apply IH to e2
      have h_runtime1' : runtimeInstantiatesCtx ctx' config₁.memory config₁.varEnv := by
        subst h_ctx_eq
        exact h_runtime1
      have h_tc2' : typecheck ctx' e2 (fuel_tc' - 1) = .ok result2 := by
        simp [typecheck]
        exact h_tc2
      have IH2 := IH fuel' h_fuel e2 ctx' (fuel_tc' - 1) result2
                      config₁.memory μ₂ config₁.varEnv ρ₂
                      config₁.nextLoc l₂ config₁.pureMode pm₂ v verbose
                      h_tc2' h_runtime1' h_eval2
      obtain ⟨h_v_type, h_runtime2⟩ := IH2

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₂ ρ₂
        simp only [h_mem]
        -- runtimeInstantiatesCtx only depends on memEnv and varEnv
        -- ctx'.varEnv = ctx.varEnv, so they're equivalent
        subst h_ctx_eq
        simp only [runtimeInstantiatesCtx] at h_runtime2 ⊢
        exact h_runtime2

-- Helper lemma for conditionals
private lemma preservation_ite (e1 e2 e3 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.ite e1 e2 e3) ctx n := by
  sorry

-- Helper lemma for reference creation
private lemma preservation_newRef (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.newRef e1) ctx n := by
  sorry

-- Helper lemma for assignment
private lemma preservation_assign (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.assign e1 e2) ctx n := by
  sorry

-- Helper lemma for dereference
private lemma preservation_deref (e1 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.deref e1) ctx n := by
  sorry

-- Helper lemma for while loops
private lemma preservation_kwhile (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.kwhile e1 e2) ctx n := by
  sorry

-- Helper lemma for let binding
private lemma preservation_vlet (x : Name) (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.vlet x e1 e2) ctx n := by
  sorry

-- Helper lemma for function abstraction
private lemma preservation_fn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.fn x paramType body returnType) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  -- Function abstraction is simple: typechecking creates arrow type, evaluation creates closure
  cases n with
  | zero =>
    -- With fuel 0, beval returns outOfFuel
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr, typecheckFn, pure, Except.pure] at h_typecheck
      -- Evaluation creates closure without changing state
      simp [LeanPoison.beval] at h_eval
      apply congrFun (a := ()) at h_eval
      simp [pure] at h_eval
      -- Extract equalities
      cases h_typecheck
      cases h_eval
      constructor
      · -- valueHasETyp: closure has arrow type
        constructor
      · -- runtimeInstantiatesCtx: contexts unchanged
        exact h_instantiate

-- Helper lemma for pure function abstraction
private lemma preservation_pfn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.pfn x paramType body returnType) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  -- Pure function abstraction is similar to fn, but converts body to PExpr
  cases n with
  | zero =>
    simp [LeanPoison.beval] at h_eval
    apply congrFun (a := ()) at h_eval
    cases h_eval
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Typecheck uses toPExpr, then returns parrow type
      unfold typecheckPfn at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      -- Split on toPExpr result
      split at h_typecheck
      · next h_toPExpr_err =>
        -- toPExpr failed, contradiction
        contradiction
      · next pbody h_toPExpr_ok =>
        simp [pure, Except.pure] at h_typecheck
        -- Evaluation creates peClosure without changing state
        simp [LeanPoison.beval] at h_eval
        apply congrFun (a := ()) at h_eval
        simp [pure] at h_eval
        -- Extract equalities
        cases h_typecheck
        cases h_eval
        constructor
        · -- valueHasETyp: peClosure has parrow type
          constructor
        · -- runtimeInstantiatesCtx: contexts unchanged
          exact h_instantiate

-- Helper lemma for function application
private lemma preservation_app (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.app e1 e2) ctx n := by
  sorry

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
      exact preservation_unaryop op e1 ctx n IH
    | ite e1 e2 e3 =>
      -- Conditionals: by IH, e1 evaluates to bool, then either e2 or e3 preserves types
      exact preservation_ite e1 e2 e3 ctx n IH
    | newRef e1 =>
      -- Reference creation: by IH, e1 has correct type, fresh location added to contexts
      exact preservation_newRef e1 ctx n IH
    | assign e1 e2 =>
      -- Assignment: by IH, e1 evaluates to location, e2 to value of correct type
      exact preservation_assign e1 e2 ctx n IH
    | deref e1 =>
      -- Dereference: by IH, e1 evaluates to location, memory lookup returns correct type
      -- This case is complex and requires reasoning about memory typing relationships
      -- TODO: Complete proof - needs to show memory lookup preserves types via runtime instantiation
      exact preservation_deref e1 ctx n IH
    | seq e1 e2 =>
      -- Sequence: by IH, e2 preserves types (e1's result is discarded)
      exact preservation_seq e1 e2 ctx n IH
    | kwhile e1 e2 =>
      -- While loops: requires fixpoint reasoning about typing context evolution
      exact preservation_kwhile e1 e2 ctx n IH
    | vlet x e1 e2 =>
      -- Let binding: by IH, e1 has correct type, e2 preserves types with extended context
      exact preservation_vlet x e1 e2 ctx n IH
    | fn x paramType body returnType =>
      -- Function abstraction: creates closure value with correct arrow type
      exact preservation_fn x paramType body returnType ctx n IH
    | pfn x paramType body returnType =>
      -- Pure function abstraction: creates pure closure with correct arrow type
      exact preservation_pfn x paramType body returnType ctx n IH
    | app e1 e2 =>
      -- Function application: by IH, e1 evaluates to closure, body preserves types
      exact preservation_app e1 e2 ctx n IH
    | rand e1 =>
      -- Random generation: by IH, e1 evaluates to number, result is int
      exact preservation_rand e1 ctx n IH
    | frand e1 =>
      -- Faulty random: similar to rand
      exact preservation_frand e1 ctx n IH
    | printInt e1 =>
      -- Print operations: by IH, e1 evaluates successfully, result is unit
      exact preservation_printInt e1 ctx n IH
    | printString e1 =>
      -- Print string: similar to printInt
      exact preservation_printString e1 ctx n IH

-- Preservation theorem: well-typed programs preserve types
-- This proof uses strong induction on fuel via preservationWithFuel_all
theorem preservation (e : Expr) (ctx : TypeContext) : Preservation e ctx :=
  preservationWithFuel_implies_preservation e ctx (preservationWithFuel_all · e ctx)
