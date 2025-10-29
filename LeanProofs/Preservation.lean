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
private lemma preservation_num (n : Int) (ctx : TypeContext) (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value)
    (h_typecheck : typecheck ctx (Expr.num n) fuel_tc = .ok res)
    (h_instantiate : runtimeInstantiatesCtx ctx μ₀ ρ₀)
    (h_terminates : terminatesTo (Expr.num n)
                      { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                      { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) :
    valueHasETyp v res.qualType.etyp ∧
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ := by
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
private lemma preservation_bool (b : Bool) (ctx : TypeContext) (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value)
    (h_typecheck : typecheck ctx (Expr.bool b) fuel_tc = .ok res)
    (h_instantiate : runtimeInstantiatesCtx ctx μ₀ ρ₀)
    (h_terminates : terminatesTo (Expr.bool b)
                      { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                      { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) :
    valueHasETyp v res.qualType.etyp ∧
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ := by
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
private lemma preservation_unit (ctx : TypeContext) (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value)
    (h_typecheck : typecheck ctx Expr.unit fuel_tc = .ok res)
    (h_instantiate : runtimeInstantiatesCtx ctx μ₀ ρ₀)
    (h_terminates : terminatesTo Expr.unit
                      { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                      { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) :
    valueHasETyp v res.qualType.etyp ∧
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ := by
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
private lemma preservation_str (s : String) (ctx : TypeContext) (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value)
    (h_typecheck : typecheck ctx (Expr.str s) fuel_tc = .ok res)
    (h_instantiate : runtimeInstantiatesCtx ctx μ₀ ρ₀)
    (h_terminates : terminatesTo (Expr.str s)
                      { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                      { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v) :
    valueHasETyp v res.qualType.etyp ∧
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ := by
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
      apply preservation_num n ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | bool b =>
      -- Boolean literals
      apply preservation_bool b ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | unit =>
      -- Unit literal
      apply preservation_unit ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | str s =>
      -- String literals
      apply preservation_str s ctx fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
    | var x =>
      -- Variable lookup: if x is typed and in ρ, lookup returns a value of correct type
      sorry
    | op e1 op e2 =>
      -- Binary operations: by IH, operands have correct types, so result has expected type
      sorry
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
