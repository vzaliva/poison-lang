-- Preservation Property Proofs for the Poison Language
--
-- The Preservation property states that evaluation preserves types:
-- if a well-typed expression evaluates successfully, the resulting value
-- has the expected enriched type and the final state is consistent with
-- the output typing context.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Preservation
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties
import LeanProofs.Properties
import LeanProofs.VarEnvPreservation
import LeanProofs.LookupUpdate
import LeanProofs.Equality
import LeanProofs.IOHelpers

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

/- TODO: this proof needs repairs.

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
    (∃ w₀ w₁, LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } e verbose w₀ =
      EST.Out.ok (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) w₁) →
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
  -- Convert h_eval from terminatesTo format (function equality) to world-indexed format
  -- h_eval: LeanPoison.beval fuel_eval ... = pure (.success ...)
  -- evalAtDefault_eq converts function equality to point equality at defaultWorld
  have h_eval_at_default := LeanProofs.evalAtDefault_eq h_eval
  -- Now h_eval_at_default: beval ... defaultWorld = pure ... defaultWorld
  -- pure expands to fun w => Result.ok ... w, so at defaultWorld it's Result.ok ... defaultWorld
  simp [pure, EStateM.pure] at h_eval_at_default
  -- Construct the existential
  have h_eval_world : ∃ w₀ w₁, LeanPoison.beval fuel_eval { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } e verbose w₀ =
      EST.Out.ok (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) w₁ :=
    ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, h_eval_at_default⟩
  exact h_pwf fuel_eval fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose
          h_typecheck h_instantiate h_eval_world

-- Private lemma for num case
private lemma preservation_num (n : Int) (ctx : TypeContext) : Preservation (Expr.num n) ctx := by
  unfold Preservation
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_terminates
  obtain ⟨fuel_eval, verbose, h_eval⟩ := h_terminates
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval
  simp [LeanPoison.beval] at h_eval_world
  cases fuel_eval with
  | zero =>
    cases h_eval_world
  | succ fuel' =>
    injection h_eval_world with h_eq_config h_eq_val
    cases h_eq_config
    cases h_eq_val
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
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval
  simp [LeanPoison.beval] at h_eval_world
  cases fuel_eval with
  | zero => cases h_eval_world
  | succ fuel' =>
    injection h_eval_world with h_eq_config h_eq_val
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
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval
  simp [LeanPoison.beval] at h_eval_world
  cases fuel_eval with
  | zero => cases h_eval_world
  | succ fuel' =>
    injection h_eval_world with h_eq_config h_eq_val
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
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval
  simp [LeanPoison.beval] at h_eval_world
  cases fuel_eval with
  | zero => cases h_eval_world
  | succ fuel' =>
    injection h_eval_world with h_eq_config h_eq_val
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
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
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
      obtain ⟨config₁, config₂, v1, v2, h_eval1_ex, h_eval2_ex, h_v1_type, h_v2_type, h_v_type, h_mem_eq⟩ :=
        bevalOp_structure e1 e2 op fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₃, varEnv := ρ₃, nextAddr := l₃, pureMode := pm₃ }
          v result1.qualType.etyp result2.qualType.etyp result_etyp
          h_eval h_op_etyp

      -- Use beval_preserves_varEnv to show varEnv is unchanged at each step
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv12 : config₁.varEnv = config₂.varEnv :=
        beval_preserves_varEnv e2 fuel' verbose
          config₁ config₂ v2 h_eval2_ex
      have h_varenv_unchanged : ρ₀ = ρ₃ :=
        beval_preserves_varEnv (Expr.op e1 op e2) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₃, varEnv := ρ₃, nextAddr := l₃, pureMode := pm₃ }
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
                      l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1_ex
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
                      config₁.nextAddr config₂.nextAddr config₁.pureMode config₂.pureMode v2 verbose
                      h_tc2' h_runtime1 h_eval2_ex
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
  have h_eval_world := LeanProofs.evalAtDefault_eq h_eval
  simp [LeanPoison.beval] at h_eval_world
  cases fuel_eval with
  | zero => cases h_eval_world
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
        simp [h_v] at h_eval_world
        injection h_eval_world with h_eq_config h_eq_val
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, result_etyp, h_tc1, h_op_etyp, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckUnaryOp_structure ctx op e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1_ex, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq, _hnext_eq, _hpure_eq⟩ :=
        bevalUnaryOp_structure op e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextAddr := l₂, pureMode := pm₂ }
          v result1.qualType.etyp result_etyp
          h_eval h_op_etyp

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv_unchanged : ρ₀ = ρ₂ :=
        beval_preserves_varEnv (Expr.unaryop op e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextAddr := l₂, pureMode := pm₂ }
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
                      l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1_ex
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckPrintInt_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1_ex, _hv1_shape, h_v_unit, h_mem_eq, h_varenv_eq⟩ :=
        bevalPrintInt_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.printInt e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp, h_v_unit]
        exact valueHasETyp.unit
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1_ex
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckPrintString_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1_ex, _hv1_shape, h_v_unit, h_mem_eq, h_varenv_eq⟩ :=
        bevalPrintString_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.printString e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      subst h_varenv01 h_varenv_unchanged
      rw [← h_varenv_eq]

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp, h_v_unit]
        exact valueHasETyp.unit
      · -- runtimeInstantiatesCtx
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_tc1' : typecheck ctx e1 (fuel_tc' - 1) = .ok result1 := by
          simp [typecheck]
          exact h_tc1
        have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                        μ₀ config₁.memory config₁.varEnv config₁.varEnv
                        l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1_ex
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp⟩ :=
        typecheckRand_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1_ex, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalRand_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.rand e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
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
                        l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1_ex
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, h_tc1, h_etyp1, h_mem, h_tag, h_loc, h_ntag, h_etyp, h_poison⟩ :=
        typecheckFrand_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, v1, h_eval1_ex, h_v1_type, h_v_type, h_mem_eq, h_varenv_eq⟩ :=
        bevalFrand_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
          v h_eval

      -- VarEnv preservation
      have h_varenv01 : ρ₀ = config₁.varEnv :=
        beval_preserves_varEnv e1 fuel' verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      have h_varenv_unchanged : ρ₀ = ρ₁ :=
        beval_preserves_varEnv (Expr.frand e1) fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ }
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
                        l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                        h_tc1' h_instantiate h_eval1_ex
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
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure using helper lemma
      have ⟨result1, result2, ctx', h_tc1, h_ctx_eq, h_tc2, h_etyp, h_mem, h_tag, h_loc, h_ntag⟩ :=
        typecheckSeq_structure ctx e1 e2 fuel_tc' res h_typecheck
      -- Extract evaluation structure using helper lemma
      obtain ⟨config₁, v1, h_eval1_ex, h_eval2_ex⟩ :=
        bevalSeq_structure e1 e2 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextAddr := l₂, pureMode := pm₂ }
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
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      -- Convert h_eval1_ex to use config₁.varEnv
      rcases h_eval1_ex with ⟨w₀', w₁', h_eval1_eq⟩
      -- Rewrite to use config₁.varEnv in h_instantiate
      rw [h_varenv01] at h_instantiate
      -- Rewrite fuel and varEnv in h_eval1_eq
      -- h_eval1_eq has fuel fuel' and varEnv ρ₀
      -- We need to rewrite ρ₀ to config₁.varEnv using h_varenv01
      have h_eval1_eq' : LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } v1) w₁' := by
        -- h_eval1_eq has ρ₀, rewrite to config₁.varEnv
        rw [h_varenv01] at h_eval1_eq
        exact h_eval1_eq
      -- Construct h_eval1' with updated varEnv
      have h_eval1' : ∃ w₀'' w₁'', LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀'' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } v1) w₁'' :=
        ⟨w₀', w₁', h_eval1_eq'⟩
      have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1'
      obtain ⟨_, h_runtime1⟩ := IH1

      -- Apply IH to e2
      have h_runtime1' : runtimeInstantiatesCtx ctx' config₁.memory config₁.varEnv := by
        subst h_ctx_eq
        exact h_runtime1
      have h_tc2' : typecheck ctx' e2 (fuel_tc' - 1) = .ok result2 := by
        simp [typecheck]
        exact h_tc2
      -- Convert h_eval2_ex to use explicit config structure
      rcases h_eval2_ex with ⟨w₀'', w₁'', h_eval2_eq⟩
      have h_eval2' : ∃ w₀''' w₁''', LeanPoison.beval fuel' { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } e2 verbose w₀''' =
          EST.Out.ok (.success { memory := μ₂, varEnv := ρ₂, nextAddr := l₂, pureMode := pm₂ } v) w₁''' :=
        ⟨w₀'', w₁'', h_eval2_eq⟩
      have IH2 := IH fuel' h_fuel e2 ctx' (fuel_tc' - 1) result2
                      config₁.memory μ₂ config₁.varEnv ρ₂
                      config₁.nextAddr l₂ config₁.pureMode pm₂ v verbose
                      h_tc2' h_runtime1' h_eval2'
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
-- Note: it migth not be provable yet becaue of isse #63
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
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₂ ρ₀ ρ₂ l₀ l₂ pm₀ pm₂ v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure
      have ⟨result1, l, etyp, h_tc1, h_fresh, h_etyp, h_mem, h_tag, h_loc, h_ntag⟩ :=
        typecheckNewRef_structure ctx e1 fuel_tc' res h_typecheck

      -- Extract evaluation structure
      obtain ⟨config₁, n_val, l_eval, h_eval1_ex, h_fresh_eval, h_config_eq, h_val_eq⟩ :=
        bevalNewRef_structure e1 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ₂, varEnv := ρ₂, nextAddr := l₂, pureMode := pm₂ }
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
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ (Value.num n_val) h_eval1_ex
      -- Convert h_eval1_ex to use config₁.varEnv
      rcases h_eval1_ex with ⟨w₀', w₁', h_eval1_eq⟩
      rw [h_varenv01] at h_instantiate
      have h_eval1_eq' : LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } (Value.num n_val)) w₁' := by
        rw [h_varenv01] at h_eval1_eq
        exact h_eval1_eq
      have h_eval1' : ∃ w₀'' w₁''', LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀'' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } (Value.num n_val)) w₁''' :=
        ⟨w₀', w₁', h_eval1_eq'⟩
      have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextAddr pm₀ config₁.pureMode (Value.num n_val) verbose
                      h_tc1' h_instantiate h_eval1'
      obtain ⟨h_v_type, h_runtime1⟩ := IH1

      -- Now we need to show:
      -- 1. valueHasETyp v res.qualType.etyp
      -- 2. runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₂ ρ₂

      constructor
      · -- valueHasETyp v res.qualType.etyp
        -- h_val_eq: v = Value.loc config₁.nextAddr
        -- h_etyp: res.qualType.etyp = ETyp.ref etyp l
        -- From h_fresh: l = result1.nextLoc' (the fresh location from typechecking)
        -- From h_fresh_eval: l_eval = config₁.nextAddr (the fresh location from evaluation)
        -- We need to show valueHasETyp (Value.loc config₁.nextAddr) (ETyp.ref etyp l)
        -- The valueHasETyp.loc constructor ignores the concrete address in the type,
        -- so we can use it directly
        rw [h_val_eq, h_etyp]
        -- Extract l from h_fresh: l = result1.nextLoc'
        injection h_fresh with h_fresh_loc h_fresh_res
        -- Extract l_eval from h_fresh_eval: l_eval = config₁.nextAddr
        injection h_fresh_eval with h_fresh_eval_loc h_fresh_eval_config
        -- We need to show result1.nextLoc' = config₁.nextAddr
        -- Both start from the same initial state (l₀ = ctx.nextLoc) and both increment by 1
        -- This should follow from the fact that e1 evaluation preserves nextLoc relationship
        -- Actually, we can use the fact that both typechecking and evaluation start from
        -- the same initial nextLoc and both increment by 1, so they should match
        -- But we need to prove this from the structure
        -- For now, let's assume they match and use valueHasETyp.loc
        -- Actually, looking at valueHasETyp.loc, it says "ignore concrete address in type",
        -- so we don't need to show l = config₁.nextAddr
        exact valueHasETyp.loc config₁.nextAddr etyp l
      · -- runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₂ ρ₂
        -- res.memEnv' = updateMemEnv result1.memEnv' l storedQt
        -- where storedQt = ⟨etyp, joinPoison ctx.pc result1.qualType.poison, result1.qualType.pred⟩
        -- μ₂ = {config'' with memory := config''.memory.update l_eval n_val}
        -- where (l_eval, config'') = freshAddr config₁
        -- We need to show that μ₂ contains l with the correct type
        -- Extract l from h_fresh: l = result1.nextLoc'
        injection h_fresh with h_fresh_loc h_fresh_res
        -- Extract l_eval from h_fresh_eval: l_eval = config₁.nextAddr
        injection h_fresh_eval with h_fresh_eval_loc h_fresh_eval_config
        -- We need to show result1.nextLoc' = config₁.nextAddr
        -- Both start from the same initial state (l₀ = ctx.nextLoc) and both increment by 1
        -- This should follow from the fact that e1 evaluation preserves nextLoc relationship
        -- Actually, we need a lemma that says if runtimeInstantiatesCtx holds,
        -- then the nextLoc counters match
        -- For now, let's assume they match: result1.nextLoc' = config₁.nextAddr
        -- This means l = l_eval
        have h_loc_match : l = l_eval := by
          -- We need to show result1.nextLoc' = config₁.nextAddr
          -- This follows from the fact that both start from l₀ and both increment by 1
          -- But we need to prove this from the structure
          -- Actually, we can use the fact that both typechecking and evaluation
          -- start from the same initial state and both increment by 1
          -- So result1.nextLoc' = config₁.nextAddr
          -- This is a key property that needs to be proven separately
          sorry  -- TODO: Prove that result1.nextLoc' = config₁.nextAddr
        -- Now we can show runtimeInstantiatesCtx
        -- We need to show:
        -- 1. All locations in res.memEnv' are in μ₂
        -- 2. All variables in the updated context are in ρ₂ with correct types
        -- From h_runtime1, we know config₁.memory satisfies result1.memEnv'
        -- We need to extend this to show μ₂ satisfies res.memEnv'
        -- res.memEnv' = updateMemEnv result1.memEnv' l storedQt
        -- Extract μ₂ from h_config_eq
        injection h_config_eq with h_mem_eq h_varenv_eq h_nextloc_eq h_puremode_eq
        -- h_mem_eq: μ₂ = config₁.memory.update config₁.nextAddr n_val
        -- From h_fresh_eval_loc: l_eval = config₁.nextAddr
        -- From h_loc_match: l = l_eval
        -- So l = config₁.nextAddr
        -- Rewrite config₁.nextAddr to l
        have h_loc_eq_nextloc : l = config₁.nextAddr := by
          rw [h_loc_match, h_fresh_eval_loc]
        rw [← h_loc_eq_nextloc] at h_mem_eq
        -- h_mem_eq: μ₂ = config₁.memory.update l n_val
        -- Now we need to show runtimeInstantiatesCtx
        -- Split into two parts: memory and variables
        constructor
        · -- Part 1: All locations in res.memEnv' are in μ₂
          -- res.memEnv' = updateMemEnv result1.memEnv' l storedQt
          -- We need to show: ∀ l', res.memEnv'.contains l' → μ₂.contains l'
          intro l' h_contains
          -- Case 1: l' = l (the new location)
          -- Case 2: l' ≠ l (existing location from result1.memEnv')
          -- For case 1: l' = l (the new location)
          -- From h_mem_eq, μ₂ = config₁.memory.update l n_val
          -- Memory.update adds the location, so μ₂.contains l
          -- For case 2: l' ≠ l (existing location from result1.memEnv')
          -- From h_runtime1, config₁.memory.contains l'
          -- And Memory.update preserves existing locations, so μ₂.contains l'
          -- We need to handle both cases
          -- res.memEnv' = updateMemEnv result1.memEnv' l storedQt
          -- So res.memEnv'.contains l' means either l' = l or result1.memEnv'.contains l'
          -- Case 1: l' = l
          -- From h_mem_eq, μ₂ = config₁.memory.update l n_val
          -- Memory.update always adds the location, so μ₂.contains l
          -- Case 2: l' ≠ l and result1.memEnv'.contains l'
          -- From h_runtime1, config₁.memory.contains l'
          -- And Memory.update preserves existing locations when l' ≠ l
          -- This requires a lemma about Memory.update preserving contains for different locations
          -- For now, let's use sorry
          sorry  -- TODO: Prove memory contains after update (need lemma: Memory.update preserves contains for different locations)
        · -- Part 2: All variables in the updated context are in ρ₂ with correct types
          -- The context doesn't change varEnv, so ctx.varEnv = { ctx with memEnv := res.memEnv' }.varEnv
          -- From h_config_eq, ρ₂ = config₁.varEnv
          -- From h_runtime1, config₁.varEnv satisfies ctx.varEnv
          -- So we can use h_runtime1 for variables
          intro x qt h_lookup
          -- From h_runtime1, we have the variable property
          obtain ⟨_, h_var⟩ := h_runtime1
          -- h_var: ∀ {x qt}, ctx.varEnv.lookup x = some qt → ∃ v, config₁.varEnv.lookup x = some v ∧ valueHasETyp v qt.etyp
          -- We need to show: ∃ v, ρ₂.lookup x = some v ∧ valueHasETyp v qt.etyp
          -- From h_varenv_eq, ρ₂ = config₁.varEnv
          rw [h_varenv_eq]
          -- Now we can use h_var
          exact h_var h_lookup

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
-- Note: it migth not be provable yet becaue of isse #64
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
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ_final ρ₀ ρ_final l₀ l_final pm₀ pm_final v verbose h_typecheck h_instantiate h_eval
  cases n with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction with success)
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_res
    cases h_res
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr] at h_typecheck
      -- Extract typechecking structure using helper lemma
      have ⟨result1, result2, ctx', h_tc1, h_ctx_eq, h_tc2, h_etyp, h_mem, h_tag, h_loc, h_ntag⟩ :=
        typecheckVlet_structure ctx x e1 e2 fuel_tc' res h_typecheck
      -- Extract evaluation structure using helper lemma
      obtain ⟨config₁, config₂, config₃, v1, h_eval1_ex, h_config2_eq, h_eval2_ex, h_config_final_eq⟩ :=
        bevalVlet_structure x e1 e2 fuel'.succ verbose
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          { memory := μ_final, varEnv := ρ_final, nextAddr := l_final, pureMode := pm_final }
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
          { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
          config₁ v1 h_eval1_ex
      -- Convert h_eval1_ex to use config₁.varEnv
      rcases h_eval1_ex with ⟨w₀', w₁', h_eval1_eq⟩
      -- Rewrite to use config₁.varEnv in h_instantiate
      rw [h_varenv01] at h_instantiate
      -- Rewrite fuel and varEnv in h_eval1_eq
      -- h_eval1_eq has fuel fuel' and varEnv ρ₀
      -- We need to rewrite ρ₀ to config₁.varEnv using h_varenv01
      have h_eval1_eq' : LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } v1) w₁' := by
        -- h_eval1_eq has ρ₀, rewrite to config₁.varEnv
        rw [h_varenv01] at h_eval1_eq
        exact h_eval1_eq
      -- Construct h_eval1' with updated varEnv
      have h_eval1' : ∃ w₀'' w₁'', LeanPoison.beval fuel' { memory := μ₀, varEnv := config₁.varEnv, nextAddr := l₀, pureMode := pm₀ } e1 verbose w₀'' =
          EST.Out.ok (.success { memory := config₁.memory, varEnv := config₁.varEnv, nextAddr := config₁.nextAddr, pureMode := config₁.pureMode } v1) w₁'' :=
        ⟨w₀', w₁', h_eval1_eq'⟩
      have IH1 := IH fuel' h_fuel e1 ctx (fuel_tc' - 1) result1
                      μ₀ config₁.memory config₁.varEnv config₁.varEnv
                      l₀ config₁.nextAddr pm₀ config₁.pureMode v1 verbose
                      h_tc1' h_instantiate h_eval1'
      obtain ⟨h_v1_type, h_runtime1⟩ := IH1

      -- Apply IH to e2 with extended context
      -- ctx' extends ctx.varEnv with x : result1.qualType
      -- config₂ extends config₁.varEnv with x : v1
      -- Note: config₂.memory = config₁.memory (only varEnv differs)
      have h_config2_mem : config₂.memory = config₁.memory := by
        subst h_config2_eq
        simp
      have h_runtime1' : runtimeInstantiatesCtx ctx' config₂.memory config₂.varEnv := by
        subst h_ctx_eq h_config2_eq
        unfold runtimeInstantiatesCtx
        constructor
        · -- Memory part: same as h_runtime1
          intro l h_memenv_contains
          obtain ⟨h_mem, _⟩ := h_runtime1
          exact h_mem l h_memenv_contains
        · -- VarEnv part: need to show config₂.varEnv instantiates extended varEnv
          intro y qt h_lookup
          -- config₂.varEnv = config₁.varEnv.update x v1
          -- If y = x, then lookup returns v1 which has type result1.qualType.etyp
          -- If y ≠ x, then lookup returns config₁.varEnv.lookup y (from original context)
          by_cases h_eq : y = x
          · -- Case: y = x
            rw [h_eq] at h_lookup ⊢
            -- Now h_lookup: (ctx.varEnv.update x result1.qualType).lookup x = some qt
            -- update prepends, so lookup x returns result1.qualType
            have h_lookup_x : (ctx.varEnv.update x result1.qualType).lookup x = some result1.qualType := by
              simp [VarTypeEnv.update, VarTypeEnv.lookup]
            have h_lookup_eq : some result1.qualType = some qt := by
              rw [← h_lookup_x, h_lookup]
            injection h_lookup_eq with h_qt_eq
            subst h_qt_eq
            -- Need to show valueHasETyp v1 result1.qualType.etyp (from h_v1_type)
            -- Also need: (config₁.varEnv.update x v1).lookup x = some v1
            simp [VarEnv.update, VarEnv.lookup]
            exact h_v1_type
          · -- Case: y ≠ x
            -- Key property: if y ≠ x, then (env.update x v).lookup y = env.lookup y
            -- Use helper lemmas
            have h_update_lookup_varType : (ctx.varEnv.update x result1.qualType).lookup y = ctx.varEnv.lookup y :=
              VarTypeEnv_lookup_update_ne ctx.varEnv x y result1.qualType h_eq
            have h_lookup_orig : ctx.varEnv.lookup y = some qt := by
              rw [← h_update_lookup_varType, h_lookup]
            -- Similarly for VarEnv
            have h_update_lookup_var : (config₁.varEnv.update x v1).lookup y = config₁.varEnv.lookup y :=
              VarEnv_lookup_update_ne config₁.varEnv x y v1 h_eq
            -- From h_runtime1: config₁.varEnv instantiates ctx.varEnv
            obtain ⟨_, h_var⟩ := h_runtime1
            have h_config_val := h_var h_lookup_orig
            -- Goal: ∃ v, (config₁.varEnv.update x v1).lookup y = some v ∧ valueHasETyp v qt.etyp
            -- h_config_val: ∃ v, config₁.varEnv.lookup y = some v ∧ valueHasETyp v qt.etyp
            -- Rewrite lookup to show they're equal
            rw [h_update_lookup_var]
            exact h_config_val
      have h_tc2' : typecheck ctx' e2 (fuel_tc' - 1) = .ok result2 := by
        simp [typecheck]
        exact h_tc2
      -- Convert h_eval2_ex to use explicit config structure
      rcases h_eval2_ex with ⟨w₀'', w₁'', h_eval2_eq⟩
      have h_eval2' : ∃ w₀''' w₁''', LeanPoison.beval fuel' { memory := config₂.memory, varEnv := config₂.varEnv, nextAddr := config₂.nextAddr, pureMode := config₂.pureMode } e2 verbose w₀''' =
          EST.Out.ok (.success { memory := config₃.memory, varEnv := config₃.varEnv, nextAddr := config₃.nextAddr, pureMode := config₃.pureMode } v) w₁''' :=
        ⟨w₀'', w₁'', h_eval2_eq⟩
      have IH2 := IH fuel' h_fuel e2 ctx' (fuel_tc' - 1) result2
                      config₂.memory config₃.memory config₂.varEnv config₃.varEnv
                      config₂.nextAddr config₃.nextAddr config₂.pureMode config₃.pureMode v verbose
                      h_tc2' h_runtime1' h_eval2'
      obtain ⟨h_v_type, h_runtime2⟩ := IH2

      constructor
      · -- valueHasETyp v res.qualType.etyp
        rw [h_etyp]
        exact h_v_type
      · -- runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ_final ρ_final
        -- Final config: { config₃ with varEnv := config₁.varEnv }
        -- From h_config_final_eq: { memory := μ_final, varEnv := ρ_final, ... } = { config₃ with varEnv := config₁.varEnv }
        -- Extract equalities
        have h_mem_final : μ_final = config₃.memory := by
          have h_mem_eq := congrArg Config.memory h_config_final_eq
          simp at h_mem_eq
          exact h_mem_eq
        have h_varenv_final : ρ_final = config₁.varEnv := by
          have h_varenv_eq := congrArg Config.varEnv h_config_final_eq
          simp at h_varenv_eq
          exact h_varenv_eq
        -- Rewrite goal with these equalities
        rw [h_mem_final, h_varenv_final, h_mem]
        -- Now goal: runtimeInstantiatesCtx { ctx with memEnv := result2.memEnv' } config₃.memory config₁.varEnv
        -- h_runtime2: runtimeInstantiatesCtx { ctx' with memEnv := result2.memEnv' } config₃.memory config₃.varEnv
        -- Key: ctx'.varEnv extends ctx.varEnv with x, but final varEnv is config₁.varEnv = config₁.varEnv (restored)
        -- We need to show config₁.varEnv instantiates ctx.varEnv, which is from h_runtime1
        subst h_ctx_eq
        -- After subst: goal is about ctx.varEnv, and h_runtime2 is about ctx'.varEnv = ctx.varEnv.update x result1.qualType
        -- But final varEnv is config₁.varEnv, which should instantiate ctx.varEnv (not ctx'.varEnv)
        -- This is provided by h_runtime1: config₁.varEnv instantiates ctx.varEnv
        unfold runtimeInstantiatesCtx at h_runtime1 ⊢
        obtain ⟨h_mem1, h_var1⟩ := h_runtime1
        constructor
        · -- Memory part: use result2.memEnv' from h_runtime2
          intro l h_memenv_contains
          -- Need to show config₃.memory.contains l
          -- From h_runtime2, we know { ctx' with memEnv := result2.memEnv' } is satisfied by config₃.memory
          -- And memory monotonicity tells us config₃.memory contains all locations from config₁.memory
          -- Since result2.memEnv' = result1.memEnv' (no new allocations in e2), locations come from result1.memEnv'
          -- Use h_runtime2's memory part
          unfold runtimeInstantiatesCtx at h_runtime2
          obtain ⟨h_mem2, _⟩ := h_runtime2
          exact h_mem2 l h_memenv_contains
        · -- VarEnv part: config₁.varEnv instantiates ctx.varEnv (from h_runtime1)
          intro y qt h_lookup
          exact h_var1 h_lookup

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
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  | succ fuel' =>
    cases fuel_tc with
    | zero => simp [typecheck, typecheckExpr] at h_typecheck
    | succ fuel_tc' =>
      simp only [typecheck, typecheckExpr, typecheckFn, pure, Except.pure] at h_typecheck
      rcases h_eval with ⟨w₀, w₁, h_eq⟩
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      -- Extract equalities
      cases h_typecheck
      injection h_eq with h_eq_result h_eq_state
      injection h_eq_result with h_eq_cfg h_eq_val
      -- Extract config and value from h_eq_cfg and h_eq_val
      injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
      -- h_eq_val is Value.closure x body ρ₀ = v, rewrite v to closure
      rw [← h_eq_val]
      constructor
      · -- valueHasETyp: closure has arrow type
        constructor
      · -- runtimeInstantiatesCtx: contexts unchanged (config unchanged for fn)
        rw [h_mem, h_varenv] at h_instantiate
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
    rcases h_eval with ⟨w₀, w₁, h_eq⟩
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
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
        rcases h_eval with ⟨w₀, w₁, h_eq⟩
        unfold LeanPoison.beval at h_eq
        simp at h_eq
        -- Extract equalities
        cases h_typecheck
        injection h_eq with h_eq_result h_eq_state
        injection h_eq_result with h_eq_cfg h_eq_val
        -- Extract config and value from h_eq_cfg and h_eq_val
        injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
        -- h_eq_val is Value.peClosure x body ρ₀ = v, rewrite v to peClosure
        rw [← h_eq_val]
        constructor
        · -- valueHasETyp: peClosure has parrow type
          constructor
        · -- runtimeInstantiatesCtx: contexts unchanged (config unchanged for pfn)
          rw [h_mem, h_varenv] at h_instantiate
          exact h_instantiate

-- Helper lemma for function application
private lemma preservation_app (e1 e2 : Expr) (ctx : TypeContext)
    (n : Nat)
    (IH : ∀ m < n, ∀ (e : Expr) (ctx : TypeContext), PreservationWithFuel e ctx m)
    :
    PreservationWithFuel (Expr.app e1 e2) ctx n := by
  sorry

-- Helper: prove PreservationWithFuel for all expressions and all fuel values
-- Helper lemmas for trivial cases (literals and variables)
private lemma preservationWithFuel_num (n_val : Int) (ctx : TypeContext) (n : Nat) :
    PreservationWithFuel (Expr.num n_val) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  have h_pres := preservation_num n_val ctx
  unfold Preservation at h_pres
  -- Convert h_eval from existential to function equality
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Extract information from h_eq first (before funext)
  -- Simplify beval to expose constructor structure
  simp [LeanPoison.beval] at h_eq
  -- Split on n = 0 to handle the if expression
  by_cases h_n_zero : n = 0
  · -- Case n = 0: contradiction since h_eq shows success
    rw [h_n_zero] at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  · -- Case n ≠ 0: beval returns success
    simp [h_n_zero, pure] at h_eq
    -- Extract equalities from h_eq
    injection h_eq with h_eq_result h_eq_state
    injection h_eq_result with h_eq_cfg h_eq_val
    -- Extract config equalities
    injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
    -- For pure expressions like num, beval doesn't depend on world state
    -- beval for num is: return .success config (Value.num n_val)
    -- This expands to: fun w => Result.ok (.success config (Value.num n_val)) w
    -- So we can construct the function equality directly
    have h_eval_func : LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } (Expr.num n_val) verbose = pure (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) := by
      funext w
      -- Simplify beval - we know n ≠ 0 from outer by_cases
      simp [LeanPoison.beval, h_n_zero, pure]
      -- beval for num doesn't depend on world, so result at w equals result at w₀
      -- Use the extracted equalities
      rw [h_mem, h_varenv, h_nextloc, h_puremode, h_eq_val]
    have h_term : terminatesTo (Expr.num n_val) _ _ v := ⟨n, verbose, h_eval_func⟩
    exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term

private lemma preservationWithFuel_bool (b : Bool) (ctx : TypeContext) (n : Nat) :
    PreservationWithFuel (Expr.bool b) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  have h_pres := preservation_bool b ctx
  unfold Preservation at h_pres
  -- Convert h_eval from existential to function equality
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Extract information from h_eq first (before funext)
  -- Simplify beval to expose constructor structure
  simp [LeanPoison.beval] at h_eq
  -- Split on n = 0 to handle the if expression
  by_cases h_n_zero : n = 0
  · -- Case n = 0: contradiction since h_eq shows success
    rw [h_n_zero] at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  · -- Case n ≠ 0: beval returns success
    simp [h_n_zero, pure] at h_eq
    -- Extract equalities from h_eq
    injection h_eq with h_eq_result h_eq_state
    injection h_eq_result with h_eq_cfg h_eq_val
    -- Extract config equalities
    injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
    have h_eval_func : LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } (Expr.bool b) verbose = pure (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) := by
      funext w
      -- Simplify beval - we know n ≠ 0 from outer by_cases
      simp [LeanPoison.beval, h_n_zero, pure]
      -- beval for bool doesn't depend on world
      rw [h_mem, h_varenv, h_nextloc, h_puremode, h_eq_val]
    have h_term : terminatesTo (Expr.bool b) _ _ v := ⟨n, verbose, h_eval_func⟩
    exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term

private lemma preservationWithFuel_unit (ctx : TypeContext) (n : Nat) :
    PreservationWithFuel Expr.unit ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  have h_pres := preservation_unit ctx
  unfold Preservation at h_pres
  -- Convert h_eval from existential to function equality
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Extract information from h_eq first (before funext)
  -- Simplify beval to expose constructor structure
  simp [LeanPoison.beval] at h_eq
  -- Split on n = 0 to handle the if expression
  by_cases h_n_zero : n = 0
  · -- Case n = 0: contradiction since h_eq shows success
    rw [h_n_zero] at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  · -- Case n ≠ 0: beval returns success
    simp [h_n_zero, pure] at h_eq
    -- Extract equalities from h_eq
    injection h_eq with h_eq_result h_eq_state
    injection h_eq_result with h_eq_cfg h_eq_val
    -- Extract config equalities
    injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
    have h_eval_func : LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } Expr.unit verbose = pure (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) := by
      funext w
      -- Simplify beval - we know n ≠ 0 from outer by_cases
      simp [LeanPoison.beval, h_n_zero, pure]
      -- beval for unit doesn't depend on world
      rw [h_mem, h_varenv, h_nextloc, h_puremode, h_eq_val]
    have h_term : terminatesTo Expr.unit _ _ v := ⟨n, verbose, h_eval_func⟩
    exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term

private lemma preservationWithFuel_str (s : String) (ctx : TypeContext) (n : Nat) :
    PreservationWithFuel (Expr.str s) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  have h_pres := preservation_str s ctx
  unfold Preservation at h_pres
  -- Convert h_eval from existential to function equality
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Extract information from h_eq first (before funext)
  -- Simplify beval to expose constructor structure
  simp [LeanPoison.beval] at h_eq
  -- Split on n = 0 to handle the if expression
  by_cases h_n_zero : n = 0
  · -- Case n = 0: contradiction since h_eq shows success
    rw [h_n_zero] at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  · -- Case n ≠ 0: beval returns success
    simp [h_n_zero, pure] at h_eq
    -- Extract equalities from h_eq
    injection h_eq with h_eq_result h_eq_state
    injection h_eq_result with h_eq_cfg h_eq_val
    -- Extract config equalities
    injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
    have h_eval_func : LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } (Expr.str s) verbose = pure (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) := by
      funext w
      -- Simplify beval - we know n ≠ 0 from outer by_cases
      simp [LeanPoison.beval, h_n_zero, pure]
      -- beval for str doesn't depend on world
      rw [h_mem, h_varenv, h_nextloc, h_puremode, h_eq_val]
    have h_term : terminatesTo (Expr.str s) _ _ v := ⟨n, verbose, h_eval_func⟩
    exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term

private lemma preservationWithFuel_var (x : Name) (ctx : TypeContext) (n : Nat) :
    PreservationWithFuel (Expr.var x) ctx n := by
  unfold PreservationWithFuel
  intro fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v verbose h_typecheck h_instantiate h_eval
  have h_pres := preservation_var x ctx
  unfold Preservation at h_pres
  -- Convert h_eval from existential to function equality
  rcases h_eval with ⟨w₀, w₁, h_eq⟩
  -- Extract information from h_eq first (before funext)
  -- Simplify beval to expose constructor structure
  simp [LeanPoison.beval] at h_eq
  -- Split on n = 0 to handle the if expression
  by_cases h_n_zero : n = 0
  · -- Case n = 0: contradiction since h_eq shows success
    rw [h_n_zero] at h_eq
    simp at h_eq
    injection h_eq with h_contr
    cases h_contr
  · -- Case n ≠ 0: beval returns success (or error if var not found)
    simp [h_n_zero] at h_eq
    -- Case analysis on variable lookup result
    cases h_lookup : ρ₀.lookup x with
    | some v_lookup =>
      -- Variable found: beval returns .success config v_lookup
      simp [h_lookup, pure] at h_eq
      -- Extract equalities from h_eq
      injection h_eq with h_eq_result h_eq_state
      injection h_eq_result with h_eq_cfg h_eq_val
      -- Extract config equalities
      injection h_eq_cfg with h_mem h_varenv h_nextloc h_puremode
      have h_eval_func : LeanPoison.beval n { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ } (Expr.var x) verbose = pure (.success { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v) := by
        funext w
        -- Simplify beval - we know n ≠ 0 from outer by_cases
        simp [LeanPoison.beval, h_n_zero]
        -- Use h_lookup from outer context
        simp [h_lookup, pure]
        -- Use the extracted equalities
        rw [h_mem, h_varenv, h_nextloc, h_puremode, h_eq_val]
      have h_term : terminatesTo (Expr.var x) _ _ v := ⟨n, verbose, h_eval_func⟩
      exact h_pres fuel_tc res μ₀ μ₁ ρ₀ ρ₁ l₀ l₁ pm₀ pm₁ v h_typecheck h_instantiate h_term
    | none =>
      -- Variable not found: beval returns runtimeError (contradiction with success)
      simp [h_lookup, pure] at h_eq
      injection h_eq with h_eq_result h_eq_state
      -- h_eq_result : .runtimeError ... = .success ...
      -- This is impossible since runtimeError and success are distinct constructors
      injection h_eq_result

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
    | externVal _ _ _ => sorry
    | externFn _ _ _ _ => sorry
    | externPfn _ _ _ => sorry
    | num n_val => exact preservationWithFuel_num n_val ctx n
    | bool b => exact preservationWithFuel_bool b ctx n
    | unit => exact preservationWithFuel_unit ctx n
    | str s => exact preservationWithFuel_str s ctx n
    | var x => exact preservationWithFuel_var x ctx n
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

-/

-- Placeholder for the main preservation theorem (to be completed later).
theorem preservation (e : Expr) (ctx : TypeContext) : Preservation e ctx := by
  sorry

-- World-indexed value-typing lemma used by FaultRobustness proofs.
-- This is a convenient form of preservation that matches the IO-friendly
-- termination relation used in the step theorem.
-- Includes wfTypeContext premise and wfTypeResult conclusion for freshness reasoning.
theorem preservation_valueW (e : Expr) (ctx : TypeContext) :
  ∀ (fuel_tc : Nat) (res : TypeResult)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (a₀ a₁ : Address) (pm₀ pm₁ : Bool) (v : Value),
    wfTypeContext ctx →
    typecheck ctx e fuel_tc = .ok res →
    wfRealizationMap θ₀ →
    wfRealizationMap θ₁ →
    wfExtendsMap θ₀ θ₁ →
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ θ₁ →
    terminatesToW e
      { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ }
      { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } v →
    valueHasETyp θ₁ v res.qualType.etyp ∧ wfTypeResult res := by
  sorry
