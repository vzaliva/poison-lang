-- Preservation Property for the Poison Language
--
-- The Preservation property states that evaluation preserves types:
-- if a well-typed expression evaluates successfully, the resulting value
-- has the expected enriched type and the final state is consistent with
-- the output typing context.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties

-- ================================================================
-- Preservation Property
-- ================================================================

-- Preservation property: evaluation preserves types
-- If an expression typechecks and evaluates successfully, the result value
-- has the expected enriched type and the final state is consistent with
-- the output typing context
def Preservation (mode : LeanPoison.EvalMode) (e : Expr) (ctx : TypeContext) : Prop :=
  ∀ (fuel_tc : Nat) (res : TypeResult) (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ : RealizationMap)
    (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value),
    -- Pre-conditions:
    wfTypeContext ctx →
    typecheck ctx e fuel_tc = .ok res →
    wfRealizationMap θ₀ →
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    terminatesTo mode e { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
                   { memory := μ₁, varEnv := ρ₁, nextAddr := l₁, pureMode := pm₁ } v →
    -- Post-conditions:
    -- (i) there exists an output realisation map that extends the initial map,
    -- (ii) the result value has the expected enriched type,
    -- (iii) the typing result is well-formed (all locs in memEnv' < nextLoc'), and
    -- (iv) the final runtime state instantiates the output typing context.
    ∃ (θ₁ : RealizationMap),
      wfExtendsMap θ₀ θ₁ ∧
      valueHasETyp θ₁ v res.qualType.etyp ∧
      wfTypeResult res ∧
      runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ θ₁
