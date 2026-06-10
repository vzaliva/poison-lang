import LeanProofs.MemReadCapturesFR

/-!
# Program-level fault-robustness for the `set_err` write effect

The capstone for extern *write effects* (doc/extern-write-effects.md step 8,
`@22`-only slice).  Where `MaxCurriedFR` / `GuardedCapturesFR` /
`MemReadCapturesFR` exercise *read* dependencies of pure externs, here the
impure extern `@22` declares the write effect
`effects: { !errno :> (int :> clean {}) }`: a successful call writes its (clean,
gated) integer argument through the declaration-captured `errno` reference.

The trusted contract is `builtinSetErrSpec` — the first complete five-field
`ExternBoundarySpec` for a `.fn` (memory-writing) extern.  Its relational
`callFR` field, `builtinSetErr_callFR`, is the genuinely new obligation: the
clean argument condition forces the two runs' written values to agree, the
clean captured `errno` reference forces them to write a **common logical cell**
(`agreeValueUnder_ref_common_loc`), and every other clean location is untouched
by the single-address writes (realization-map injectivity), so `agreeOnClean`
survives the effect.

Composing the registry-agreement witness with
`TypeSystemEnforcesFaultRobustness_at` discharges the per-context trust premise
and yields program-level fault-robustness for the registry `[@22 set_err]` at
the empty context.  The program here is the bare `@22` declaration node
(mirroring `memReadCaptures_FR`'s bare-declaration form); the end-to-end
behavioural examples live in `examples/extern_set_err*.poison`.

The `@21`/`@22` *combined* scenario registry — adding the `errno` extern value
itself — stays blocked on the deferred `@21` operational work
(doc/extern-write-effects.md steps 6-7).
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace SetErrWriteEffectFR

/-- The bare write-effect declaration node: `@22` taking a clean integer `n`
    and declaring the write effect `effects: { !errno :> (int :> clean {}) }`. -/
def setErrProg : Expr :=
  Expr.externFn 22 "n" Typ.int false SyntaxPredicate.noPred builtinSetErrRetSpec
    [builtinSetErrEffect] []

/-- Trusted registry holding the write-effect extern with its complete
    `ExternBoundarySpec`. -/
def setErrRegistry : TrustedRegistry :=
  [⟨builtinSetErrDecl, builtinSetErrImpl, builtinSetErrSpec⟩]

/-- The single declaration syntactically reachable in `setErrProg` — the
    top-level `@22` `externFn` node — is matched by the registry.  The
    `simple unit` return carries no nested extern. -/
theorem setErr_agreesWithProgram :
    TrustedRegistryAgreesWithProgram setErrProg setErrRegistry := by
  intro id d entry hprog hlookup
  unfold setErrProg at hprog
  cases hprog with
  | externFn =>
      have hl : TrustedRegistry.lookup? setErrRegistry 22
          = some ⟨builtinSetErrDecl, builtinSetErrImpl, builtinSetErrSpec⟩ := by
        simp [setErrRegistry, TrustedRegistry.lookup?, builtinSetErrDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externFn_return hret =>
      -- The `@22` return is `simple unit`, which carries no nested extern.
      cases hret

/-- Per-context trust premise at the canonical empty initial context. -/
theorem setErr_hagrees :
    TrustedRegistryAgreesWithReachable setErrProg openEmptyCtx setErrRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) setErr_agreesWithProgram

/-- **Program-level fault-robustness for the `set_err` write effect.**
    Composing the registry-agreement witness with the top-level FR theorem
    yields the FR conclusion for the `[@22 set_err]` registry at the empty
    context — the first program-level FR result whose trusted registry contains
    a memory-writing extern. -/
theorem setErrWriteEffect_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry setErrRegistry)
      setErrProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at setErrRegistry setErrProg s obs openEmptyCtx
    setErr_hagrees

end SetErrWriteEffectFR
