import LeanProofs.FaultRobustnessProofs

-- Expected: only Lean's standard axioms propext, Classical.choice, Quot.sound
-- (no sorryAx, no project-specific axioms).
#print axioms TypeSystemEnforcesFaultRobustness
#print axioms TypeSystemEnforcesFaultRobustness_allCtx
