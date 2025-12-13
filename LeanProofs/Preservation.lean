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

-- ================================================================
-- Preservation Property
-- ================================================================

-- Preservation property: evaluation preserves types
-- If an expression typechecks and evaluates successfully, the result value
-- has the expected enriched type and the final memory/variable environments
-- are consistent with the output typing context
def Preservation (e : Expr) (ctx : TypeContext) : Prop :=
  ∀ (fuel_tc : Nat) (res : TypeResult) (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ : RealizationMap)
    (l₀ l₁ : Address) (pm₀ pm₁ : Bool) (v : Value),
    -- If typechecking succeeds
    typecheck ctx e fuel_tc = .ok res →
    -- And runtime instantiates the input context
    runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀ →
    -- And evaluation terminates successfully
    terminatesTo e { memory := μ₀, varEnv := ρ₀, nextLoc := l₀, pureMode := pm₀ }
                   { memory := μ₁, varEnv := ρ₁, nextLoc := l₁, pureMode := pm₁ } v →
    -- Then there exists an output realisation map such that:
    -- (i) it extends the initial realisation map (monotone allocation),
    -- (ii) the result value has the expected enriched type, and
    -- (iii) the final runtime state instantiates the output typing context.
    ∃ (θ₁ : RealizationMap),
      RealizationMap.extendsMap θ₀ θ₁ ∧
      valueHasETyp θ₁ v res.qualType.etyp ∧
      runtimeInstantiatesCtx { ctx with memEnv := res.memEnv' } μ₁ ρ₁ θ₁
