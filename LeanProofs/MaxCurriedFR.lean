import LeanProofs.ExternProofs
import LeanProofs.ExternRegimeInt

/-!
# Program-level fault-robustness for curried `max` with a nested `captures:`

The motivating end-to-end case for extern read dependencies: the inner `@11`
declares `captures: {a}` (a clean read of the outer argument `a`), reachable
through the outer `@10`'s nested return.  Both trusted boundary specs are
complete 5-field `ExternBoundarySpec`s — `builtinMax10Spec` (whose `callFR`
returns the capture-bearing `@11` closure) and `builtinMax11CapturesSpec` (whose
`callFR` reads the captured `a` cleanly) — and the trusted registry *agrees with
the reachable declarations* (`@10` with `captures = []`, `@11` with
`captures = [a]`, the latter reached via the nested return).  Composing the
agreement witness with `TypeSystemEnforcesFaultRobustness_at` discharges the
per-context trust premise and yields program-level fault-robustness.

This is the capstone of the `captures:` work: the nested-captures program-FR
obstruction (the reachable `@11` decl carrying `[a]` so the strong, capture-aware
`@11` spec is the registry entry) is removed.
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace MaxCurriedFR

/-- Curried-`max` declaration: outer `@10` whose nested return is `@11` with
    `captures: {a}`.  The outer `@10` has no top-level captures clause (`[]`); the
    `[a]` lives on the nested `@11` inside `builtinMax10RetSpec`. -/
def maxCurriedProg : Expr :=
  Expr.externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec []

/-- Trusted registry: the outer `@10` and the capture-bearing inner `@11`, each
    with its complete `ExternBoundarySpec`. -/
def maxCurriedRegistry : TrustedRegistry :=
  [⟨builtinMax10Decl, builtinMax10Impl, builtinMax10Spec⟩,
   ⟨builtinMax11CapturesDecl, builtinMax11Impl, builtinMax11CapturesSpec⟩]

/-- Every declaration syntactically reachable in `maxCurriedProg` is matched by
    the registry: `@10` (the `externPfn` node, `captures = []`) and `@11` (the
    nested return, `captures = [a]` via `nestedPfn_here`). -/
theorem maxCurried_agreesWithProgram :
    TrustedRegistryAgreesWithProgram maxCurriedProg maxCurriedRegistry := by
  intro id d entry hprog hlookup
  unfold maxCurriedProg at hprog
  cases hprog with
  | externPfn =>
      have hl : TrustedRegistry.lookup? maxCurriedRegistry 10
          = some ⟨builtinMax10Decl, builtinMax10Impl, builtinMax10Spec⟩ := by
        simp [maxCurriedRegistry, TrustedRegistry.lookup?, builtinMax10Decl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externPfn_return hret =>
      cases hret with
      | nestedPfn_here =>
          have hl : TrustedRegistry.lookup? maxCurriedRegistry 11
              = some ⟨builtinMax11CapturesDecl, builtinMax11Impl, builtinMax11CapturesSpec⟩ := by
            simp [maxCurriedRegistry, TrustedRegistry.lookup?,
              builtinMax10Decl, builtinMax11CapturesDecl]
          rw [hl] at hlookup
          cases hlookup
          rfl
      | nestedPfn_inner hret' =>
          -- The inner `@11` return is `simple int`, which carries no further
          -- nested extern, so this branch is vacuous.
          cases hret'

/-- Per-context trust premise at the canonical empty initial context. -/
theorem maxCurried_hagrees :
    TrustedRegistryAgreesWithReachable maxCurriedProg openEmptyCtx maxCurriedRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) maxCurried_agreesWithProgram

/-- **Program-level fault-robustness for curried `max` with nested `captures:`.**
    Composing the registry-agreement witness with the top-level FR theorem yields
    the FR conclusion for the concrete `[@10, @11captures]` registry at the empty
    context. -/
theorem maxCurried_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry maxCurriedRegistry)
      maxCurriedProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at maxCurriedRegistry maxCurriedProg s obs openEmptyCtx
    maxCurried_hagrees

end MaxCurriedFR
