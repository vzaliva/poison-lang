import LeanProofs.ExternProofs
import LeanProofs.ExternRegimeInt

/-!
# Program-level fault-robustness for the shipped `abs` builtin (`@12`)

This is the program-level capstone for the trusted `abs` boundary spec.  The
runtime `abs` is `LeanPoison.ExternBuiltins.absImpl`, registered at `@12`; its
proof-side trusted contract is the complete five-field
`ExternProofs.builtinAbsSpec`.  This module makes that spec *mechanically live*:
it places `builtinAbsSpec` in a concrete `TrustedRegistry` and composes the
registry-agreement witness with the top-level FR theorem to obtain
fault-robustness for a concrete `abs` program.

The program is the bare `abs` declaration node
`extern pfn @12 x : (int :> clean {}) -> (int :> clean {})` — the
declaration-node form mirroring `MaxCurriedFR.maxCurried_FR` and
`GuardedCapturesFR.guardedCaptures_FR`.  `abs` takes no captures and returns a
plain `simple int`, so it is the simplest capstone of the family: the single
reachable declaration is the top-level `@12` node, and the `simple int` return
carries no nested extern.

This is the `abs` analogue of `MaxCurriedFR`/`MemReadCapturesFR`/
`GuardedCapturesFR`.  It consumes `builtinAbsSpec` (the spec is the registry
entry); the dirty-input obstruction `builtinAbs_cleanPost_obstruction` is a
*negative* design-justification theorem (no clean post-condition is derivable
when the input is poisoned), not a step in this proof, so it is intentionally
not referenced here.
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace AbsFR

/-- The bare `abs` declaration node: `extern pfn @12 x : int → int`, no captures,
    clean argument precondition, `simple int` return. -/
def absProg : Expr :=
  Expr.externPfn 12 "x" Typ.int false SyntaxPredicate.noPred builtinAbsRetSpec []

/-- Trusted registry holding the shipped `abs` extern with its complete
    `ExternBoundarySpec` (`builtinAbsSpec`, all five fields). -/
def absRegistry : TrustedRegistry :=
  [⟨builtinAbsDecl, builtinAbsImpl, builtinAbsSpec⟩]

/-- The single declaration syntactically reachable in `absProg` — the top-level
    `@12` `externPfn` node (`captures = []`) — is matched by the registry.  The
    `simple int` return carries no further nested extern. -/
private theorem abs_agreesWithProgram :
    TrustedRegistryAgreesWithProgram absProg absRegistry := by
  intro id d entry hprog hlookup
  unfold absProg at hprog
  cases hprog with
  | externPfn =>
      have hl : TrustedRegistry.lookup? absRegistry 12
          = some ⟨builtinAbsDecl, builtinAbsImpl, builtinAbsSpec⟩ := by
        simp [absRegistry, TrustedRegistry.lookup?, builtinAbsDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externPfn_return hret =>
      -- The `@12` return is `simple int`, which carries no nested extern.
      cases hret

/-- Per-context trust premise at the canonical empty initial context. -/
private theorem abs_hagrees :
    TrustedRegistryAgreesWithReachable absProg openEmptyCtx absRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) abs_agreesWithProgram

/-- **Program-level fault-robustness for the shipped `abs` builtin (`@12`).**
    Composing the registry-agreement witness with the top-level FR theorem yields
    the FR conclusion for the `[@12 abs]` registry at the empty context, making the
    trusted `builtinAbsSpec` a mechanically-consumed registry entry. -/
theorem abs_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry absRegistry)
      absProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at absRegistry absProg s obs openEmptyCtx
    abs_hagrees

end AbsFR
