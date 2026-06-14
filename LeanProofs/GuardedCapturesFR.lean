import LeanProofs.MaxCurriedFR

/-!
# Program-level fault-robustness for a *guarded* `captures:` read dependency

This is the capstone for guarded extern read dependencies
(`doc/ffi-proposal.md`, `captures:` section).  Where `MaxCurriedFR`
exercises an all-clean captured dependency, here the inner-`max` extern `@11`
declares its captured `a` as a **guarded** dependency
`captures: { a :> (int :> clean { 5, v => v >= 0 }) }`.  The guard predicate
means the call gate `capturesSatisfied` admits the dependency only when the actual
`a` is clean *under the call-site regime* — literally clean, or carrying a guard
whose tag is active in the regime — exactly the regime-based satisfaction relation
used by extern argument conditions.

The trusted contract is `builtinMax11GuardedSpec` (a complete five-field
`ExternBoundarySpec`).  Its relational `callFR` field, `builtinMax11Guarded_callFR`,
discharges the captured-`a` agreement through the guarded gate: the gate-extraction
`capturesSatisfied_singleton_bareVar_guarded` yields the clean-under-regime fact,
and the (already guard-capable) agreement core — `qtypCleanUnder_of_cleanUnderRegime`
producing `qtypCleanUnder.guard`, then `agreeValueUnder.withPred_true_eq` — forces
`a₀ = a₁`.

Composing the registry-agreement witness with `TypeSystemEnforcesFaultRobustness_at`
discharges the per-context trust premise and yields program-level
fault-robustness for the registry `[@11 guarded]` at the empty context.

The program here is the bare guarded `@11` declaration (mirroring
`MaxCurriedFR.maxCurried_FR`, the declaration-node form): it establishes that the
guarded-capture trusted spec is a registry entry that agrees with the program's
reachable declarations.  Routing the guarded `callFR` through an *applied* program
that materialises a genuinely de-poisoned captured value additionally requires a
trusted guarded-value producer/routing example (the same dependency the
extern-argument guarded path carries — see
`ExternRegimeInt.open_empty_context_FR_instantiable`, which is still parameterised
over `impl`/`spec`).
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace GuardedCapturesFR

/-- The bare guarded inner-`max` declaration node: `@11` reading the captured `a`
    under the guarded contract `captures: { a :> (int :> clean { 5, v => v >= 0 }) }`. -/
def guardedCapturesProg : Expr :=
  Expr.externPfn 11 "b" Typ.int false SyntaxPredicate.noPred builtinMax11RetSpec
    [⟨CaptureTarget.bareVar "a", Typ.int, false,
      SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩]

/-- Trusted registry holding the guarded-capture inner-`max` extern with its
    complete `ExternBoundarySpec`. -/
def guardedCapturesRegistry : TrustedRegistry :=
  [⟨builtinMax11GuardedDecl, builtinMax11Impl, builtinMax11GuardedSpec⟩]

/-- The single declaration syntactically reachable in `guardedCapturesProg` — the
    top-level `@11` `externPfn` node, `captures = [a (guarded)]` — is matched by the
    registry.  The `simple int` return carries no further nested extern. -/
private theorem guardedCaptures_agreesWithProgram :
    TrustedRegistryAgreesWithProgram guardedCapturesProg guardedCapturesRegistry := by
  intro id d entry hprog hlookup
  unfold guardedCapturesProg at hprog
  cases hprog with
  | externPfn =>
      have hl : TrustedRegistry.lookup? guardedCapturesRegistry 11
          = some ⟨builtinMax11GuardedDecl, builtinMax11Impl, builtinMax11GuardedSpec⟩ := by
        simp [guardedCapturesRegistry, TrustedRegistry.lookup?, builtinMax11GuardedDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externPfn_return hret =>
      -- The `@11` return is `simple int`, which carries no nested extern.
      cases hret

/-- Per-context trust premise at the canonical empty initial context. -/
private theorem guardedCaptures_hagrees :
    TrustedRegistryAgreesWithReachable guardedCapturesProg openEmptyCtx guardedCapturesRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) guardedCaptures_agreesWithProgram

/-- **Program-level fault-robustness for a guarded `captures:` read dependency.**
    Composing the registry-agreement witness with the top-level FR theorem yields the
    FR conclusion for the `[@11 guarded]` registry at the empty context.  The trusted
    `builtinMax11Guarded_callFR` inside the registry's spec is the guarded
    call-boundary obligation: a de-poisoned captured `a` is accepted and forced to
    agree across runs under the call-site regime. -/
theorem guardedCaptures_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry guardedCapturesRegistry)
      guardedCapturesProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at guardedCapturesRegistry guardedCapturesProg s obs openEmptyCtx
    guardedCaptures_hagrees

end GuardedCapturesFR
