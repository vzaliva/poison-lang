-- Progress Property for the Poison Language
--
-- The Progress property states that well-typed programs don't get stuck:
-- they either terminate (return .success) or diverge (return .outOfFuel),
-- but never encounter runtime errors (return .runtimeError).

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanProofs.TypeSafety
import LeanProofs.SemanticsProperties

-- ================================================================
-- Progress Property
-- ================================================================

-- Progress property: well-typed programs either terminate or diverge (never stuck)
-- For any well-typed expression with sufficient fuel, evaluation produces either:
-- - .success (termination)
-- - .outOfFuel (divergence)
-- but never .runtimeError (stuck state)
def Progress (mode : LeanPoison.EvalMode) (e : Expr) (ctx : TypeContext) : Prop :=
  (∃ (fuel : Nat) (res : TypeResult), typecheck mode ctx e fuel = .ok res) →
  ∀ (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (a : Address) (pm : Bool),
    wfRealizationMap θ →
    runtimeInstantiatesCtx ctx μ ρ θ →
    ¬stuck mode e { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
