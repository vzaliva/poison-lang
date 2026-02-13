-- Progress Property Proofs for the Poison Language
--
-- The Progress property states that well-typed programs don't get stuck:
-- they either terminate (return .success) or diverge (return .outOfFuel),
-- but never encounter runtime errors (return .runtimeError).

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Progress
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties
import LeanProofs.IOHelpers

-- ================================================================
-- Progress Property Proofs
-- ================================================================
--
-- Proof Strategy:
-- ---------------
-- The proof uses strong induction on evaluation fuel (fuel_eval), following
-- the pattern from typecheck_PExpr_preserves_typestate in Properties.lean.
--
-- For each fuel value n and expression e, we show that if:
--   1. The expression typechecks successfully
--   2. The runtime instantiates the typing context (runtimeInstantiatesCtx)
-- Then evaluation with fuel n cannot return .runtimeError.
--
-- The induction hypothesis (IH) is available for all fuel values m < n,
-- which is used for recursive subexpressions.
--
-- Key insights:
-- - Literals always evaluate successfully (no dependencies)
-- - Variables: if x is typed, runtimeInstantiatesCtx ensures x ∈ ρ
-- - Operations: if operands have correct types, operations succeed
-- - Dereference: if location is typed, runtimeInstantiatesCtx ensures it's in memory
-- - While loops: may diverge (.outOfFuel) but don't get stuck
-- - Function application: requires induction hypothesis on the function body
--
-- Current Status:
-- --------------
-- This is a partial proof with structure demonstrating the approach.
-- The base cases (literals: num, bool, unit, str) have lemma stubs.
--
-- Challenge: The evaluator `beval` returns `IO EvalResult`, which makes
-- direct reasoning about its return values non-trivial in Lean. A complete
-- proof would require either:
--   1. A pure version of beval for proof purposes, or
--   2. Axioms about IO computation equality, or
--   3. Refactoring beval to be pure (using a monad for I/O effects)
--
-- The proof structure is sound; completing it requires addressing the
-- IO reasoning challenge.
-- ================================================================

/- TODO: this proof needs repairs.

-- Helper lemma: Variables in well-typed contexts have values in runtime
-- This is a weaker version of var_has_correct_type from TypeSafety.lean
-- that only proves existence, not the type
lemma var_has_value_if_typed (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (x : Name) :
  runtimeInstantiatesCtx ctx μ ρ →
  (∃ qt, ctx.varEnv.lookup x = some qt) →
  ∃ v, ρ.lookup x = some v := by
  intro h_instantiate ⟨qt, h_lookup⟩
  have ⟨v, h_v, _⟩ := var_has_correct_type ctx μ ρ x qt h_instantiate h_lookup
  exact ⟨v, h_v⟩

-- Private lemma for num case
private lemma progress_num (n : Int) (ctx : TypeContext) : Progress .normal (Expr.num n) ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  rintro ⟨fuel_eval, verbose, msg, h_contra⟩
  cases fuel_eval with
  | zero =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h
  | succ fuel' =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h

-- Private lemma for bool case
private lemma progress_bool (b : Bool) (ctx : TypeContext) : Progress .normal (Expr.bool b) ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  rintro ⟨fuel_eval, verbose, msg, h_contra⟩
  cases fuel_eval with
  | zero =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h
  | succ fuel' =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h

-- Private lemma for unit case
private lemma progress_unit (ctx : TypeContext) : Progress .normal Expr.unit ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  rintro ⟨fuel_eval, verbose, msg, h_contra⟩
  cases fuel_eval with
  | zero =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h
  | succ fuel' =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h

-- Private lemma for str case
private lemma progress_str (s : String) (ctx : TypeContext) : Progress .normal (Expr.str s) ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  rintro ⟨fuel_eval, verbose, msg, h_contra⟩
  cases fuel_eval with
  | zero =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h
  | succ fuel' =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h

-- Private lemma for var case
private lemma progress_var (x : Name) (ctx : TypeContext) : Progress .normal (Expr.var x) ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  rintro ⟨fuel_eval, verbose, msg, h_contra⟩
  -- Variable lookup: if x typechecks, then x must be in ctx.varEnv
  -- and runtimeInstantiatesCtx ensures x is in ρ, so lookup succeeds
  cases fuel_eval with
  | zero =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    simp [LeanPoison.beval] at h
    cases h
  | succ fuel' =>
    have h := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld h_contra
    -- When fuel > 0, beval looks up x in ρ
    -- From typechecking, we know x is in ctx.varEnv
    cases fuel_tc with
    | zero =>
      -- Typechecking with fuel = 0 fails
      simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      -- Typechecking with fuel > 0
      simp [typecheck, typecheckExpr] at h_typecheck
      -- The typecheck for var looks up x in ctx.varEnv
      -- If it succeeds, x must be in ctx.varEnv
      cases h_lookup : ctx.varEnv.lookup x with
      | none =>
        -- If x is not in ctx.varEnv, typechecking fails
        simp [typecheckVar, h_lookup] at h_typecheck
      | some qt =>
        -- If x is in ctx.varEnv, then by runtimeInstantiatesCtx, x is in ρ
        have ⟨v, h_v⟩ := var_has_value_if_typed ctx μ ρ x h_instantiate ⟨qt, h_lookup⟩
        -- Now beval will find v in ρ and return success
        simp [LeanPoison.beval, h_v] at h
        cases h

-- Progress theorem: well-typed programs don't get stuck
-- This proof uses strong induction on fuel_eval
-- TODO: for induction we need to switch to world-indexed format with fuel, as we did in Preservation.lean
theorem progress (e : Expr) (ctx : TypeContext) : Progress .normal e ctx := by
  unfold Progress stuck
  intro ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
  push_neg
  intro fuel_eval verbose msg
  -- Now prove by strong induction on fuel_eval
  -- Strong induction on fuel_eval
  induction fuel_eval using Nat.strong_induction_on generalizing e ctx fuel_tc res μ ρ l pm verbose msg with
  | _ n IH =>
    -- IH is available for all m < n
    cases n with
    | zero =>
      -- When fuel = 0, beval returns outOfFuel, not runtimeError
      sorry
    | succ fuel =>
      -- When fuel > 0, proceed by case analysis on expression
      cases e with
      | externVal _ _ _ => sorry
      | externFn _ _ _ _ => sorry
      | externPfn _ _ _ => sorry
      | num n =>
        -- Numeric literals never get stuck
        have h_prog := progress_num n ctx
        unfold Progress stuck at h_prog
        have h_result := h_prog ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
        push_neg at h_result
        exact h_result (fuel + 1) verbose msg
      | bool b =>
        -- Boolean literals never get stuck
        have h_prog := progress_bool b ctx
        unfold Progress stuck at h_prog
        have h_result := h_prog ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
        push_neg at h_result
        exact h_result (fuel + 1) verbose msg
      | unit =>
        -- Unit literal never gets stuck
        have h_prog := progress_unit ctx
        unfold Progress stuck at h_prog
        have h_result := h_prog ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
        push_neg at h_result
        exact h_result (fuel + 1) verbose msg
      | str s =>
        -- String literals never get stuck
        have h_prog := progress_str s ctx
        unfold Progress stuck at h_prog
        have h_result := h_prog ⟨fuel_tc, res, h_typecheck⟩ μ ρ l pm h_instantiate
        push_neg at h_result
        exact h_result (fuel + 1) verbose msg
      | var x =>
        -- Variable lookup: if x is in the typing context and runtimeInstantiatesCtx holds,
        -- then x must be in ρ, so lookup succeeds
        sorry
      | op e1 op e2 =>
        -- Binary operations: by IH, e1 and e2 don't get stuck
        -- If they both evaluate to values of correct types, the operation succeeds
        sorry
      | unaryop op e1 =>
        -- Unary operations: similar to binary operations
        sorry
      | ite e1 e2 e3 =>
        -- Conditionals: by IH, e1 doesn't get stuck and evaluates to a boolean
        -- Then either e2 or e3 is evaluated, which also don't get stuck by IH
        sorry
      | newRef e1 =>
        -- Reference creation: by IH, e1 doesn't get stuck
        -- Fresh location allocation always succeeds
        sorry
      | assign e1 e2 =>
        -- Assignment: by IH, e1 evaluates to a location and e2 to a value
        -- Memory update always succeeds
        sorry
      | deref e1 =>
        -- Dereference: by IH, e1 evaluates to a location
        -- If the location is in Γ and runtimeInstantiatesCtx holds, it's in μ
        sorry
      | seq e1 e2 =>
        -- Sequence: by IH, both e1 and e2 don't get stuck
        sorry
      | kwhile e1 e2 =>
        -- While loops: can diverge (outOfFuel) but don't get stuck
        -- The loop condition and body don't get stuck by IH
        sorry
      | vlet x e1 e2 =>
        -- Let binding: by IH, e1 and e2 don't get stuck
        sorry
      | fn x paramType body returnType =>
        -- Function abstraction: always succeeds (creates closure)
        sorry
      | pfn x paramType body returnType =>
        -- Pure function abstraction: always succeeds (creates pure closure)
        sorry
      | app e1 e2 =>
        -- Function application: by IH, e1 evaluates to a closure and e2 to a value
        -- Body evaluation doesn't get stuck by IH (with extended context)
        sorry
      | rand e1 =>
        -- Random generation: by IH, e1 evaluates to a number
        -- Random number generation always succeeds
        sorry
      | frand e1 =>
        -- Faulty random: similar to rand
        sorry
      | printInt e1 =>
        -- Print operations: by IH, e1 evaluates successfully
        -- Printing always succeeds
        sorry
      | printString e1 =>
        -- Print string: similar to printInt
        sorry
-/
