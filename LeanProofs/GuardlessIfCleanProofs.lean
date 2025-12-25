import LeanProofs.GuardlessIfClean
import LeanProofs.NonInterference

/-- Unpack the guardless component from the deep guardless invariant. -/
lemma guardlessIfCleanQTypDeep.guardless {qt : QTyp} :
    guardlessIfCleanQTypDeep qt → guardlessIfCleanQTyp qt := by
  intro h
  cases h with
  | intro _ hguardless _ => exact hguardless

/-- Unpack the closure-env component from the deep guardless invariant. -/
lemma guardlessIfCleanQTypDeep.closure {qt : QTyp} :
    guardlessIfCleanQTypDeep qt → guardlessIfCleanClosureEnv qt := by
  intro h
  cases h with
  | intro _ _ hclosure => exact hclosure

/-- The top-level typechecker preserves the guardless invariant on the memory environment
    and produces guardless qualified types. -/
lemma guardlessIfClean_invariant
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
    guardlessIfCleanMem ctx.memEnv →
    guardlessIfCleanVars ctx.varEnv →
    typecheck ctx e fuel = .ok res →
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  -- TODO: re-enable and repair the full proof from the archived development.
  sorry

-- Guardless-from-clean lemmas specialized to input specs.

lemma guardlessIfCleanVars_of_wfInputSpecVarsDeep {vars : VarTypeEnv} :
  wfInputSpecVarsDeep vars →
  guardlessIfCleanVars vars := by
  -- TODO: port proof from the old guardless development.
  sorry

lemma guardlessIfCleanClosureEnv_of_specVar {s : InputSpec} {x qt} :
  wfInputSpecVarsDeep s.vars →
  s.vars.lookup x = some qt →
  guardlessIfCleanClosureEnv qt := by
  intro hdeep hlookup
  have hvars : guardlessIfCleanVars s.vars :=
    guardlessIfCleanVars_of_wfInputSpecVarsDeep hdeep
  cases hvars with
  | intro _ hlookup' =>
      have hqt : guardlessIfCleanQTypDeep qt := hlookup' hlookup
      exact guardlessIfCleanQTypDeep.closure hqt

lemma guardlessIfCleanClosureEnv_of_ctxNonSpecVar {s : InputSpec} {ctx : TypeContext} {x qt} :
  ctxMatchesInputSpec s ctx →
  ctx.varEnv.lookup x = some qt →
  ¬ s.vars.hasKey x →
  guardlessIfCleanClosureEnv qt := by
  -- TODO: port proof from old guardless invariants on contexts.
  sorry
