import LeanProofs.ExternProofs
import LeanProofs.ExternRegimeInt

/-!
# Program-level fault-robustness for an *impure* (`extern fn`) call boundary

This is the fn-side counterpart of `MaxCurriedFR` / `MemReadCapturesFR`: where
those route program-level FR through *pure* (`extern pfn`) trusted specs, this
file routes it through the first trusted **`kind = .fn`** spec,
`ExternProofs.builtinImpureIdSpec` (`@13`, the minimal impure extern
`impure_id n : (int) -> int`).

It is the program-level capstone of the fn-boundary narrowing
(`doc/ffi-proposal.md`): once `ExternBoundaryTyping.Call` covers only real
extern dispatch (`fnExternMember`/`pfnExternMember`), a `kind = .fn` spec's
`callFR`/`callSingle` are provable, so a trusted fn entry can sit in a registry
that *agrees with a program's reachable declarations* and discharge the
per-context trust premise of `TypeSystemEnforcesFaultRobustness_at`.

Scope, honestly stated: `@13` declares **no `captures:`** (`captures = []`) and
performs **no memory effect** (`effects = []`; it threads memory/`nextAddr`
unchanged), so it exercises the `fn` *call boundary and kind dispatch* but neither
extern read-dependencies nor memory effects.

Additional coverage examples are (1) a captures-bearing `fn` spec, mirroring the
pfn `builtinMax11CapturesSpec` capture→value-equality chain; and (2) a
memory-effecting `fn` spec — it would exercise the effect machinery but breaks
the `cf = callConfig` collapse that keeps this first spec's `callFR` a mirror of
the pure side (and `set_err`'s fixed `errnoAddr`-above-cursor write is not
universally operational-safe).
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace FnExternFR

/-- The bare impure declaration node: `extern fn @13 x : (int) -> int`
    (`effects = []`, `captures = []`). -/
def fnExternProg : Expr :=
  Expr.externFn 13 "x" Typ.int false SyntaxPredicate.noPred builtinImpureIdRetSpec [] []

/-- Trusted registry holding the impure-identity extern with its complete
    `ExternBoundarySpec` (the first trusted `kind = .fn` entry). -/
def fnExternRegistry : TrustedRegistry :=
  [⟨builtinImpureIdDecl, builtinImpureIdImpl, builtinImpureIdSpec⟩]

/-- The single declaration syntactically reachable in `fnExternProg` — the
    top-level `@13` `externFn` node — is matched by the registry.  The `simple int`
    return carries no further nested extern. -/
theorem fnExtern_agreesWithProgram :
    TrustedRegistryAgreesWithProgram fnExternProg fnExternRegistry := by
  intro id d entry hprog hlookup
  unfold fnExternProg at hprog
  cases hprog with
  | externFn =>
      have hl : TrustedRegistry.lookup? fnExternRegistry 13
          = some ⟨builtinImpureIdDecl, builtinImpureIdImpl, builtinImpureIdSpec⟩ := by
        simp [fnExternRegistry, TrustedRegistry.lookup?, builtinImpureIdDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externFn_return hret =>
      -- The `@13` return is `simple int`, which carries no nested extern.
      cases hret

/-- Per-context trust premise at the canonical empty initial context. -/
theorem fnExtern_hagrees :
    TrustedRegistryAgreesWithReachable fnExternProg openEmptyCtx fnExternRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) fnExtern_agreesWithProgram

/-- **Program-level fault-robustness for the bare impure (`extern fn`) declaration.**
    Composing the registry-agreement witness with the top-level FR theorem yields
    the FR conclusion for the `[@13 impure_id]` registry at the empty context —
    the first program-level FR routed through a trusted `kind = .fn` spec. -/
theorem fnExtern_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry fnExternRegistry)
      fnExternProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at fnExternRegistry fnExternProg s obs openEmptyCtx
    fnExtern_hagrees

/-! ## Fully exercised: the applied program `(extern fn @13 …) 7`

`fnExtern_FR` above is over the bare `@13` declaration node.  The *applied*
program below additionally applies `@13` to a numeral, so the generic FR theorem
routes that application through the registry's `builtinImpureIdSpec.callFR` — the
first relational **`fn`** call boundary.  The reachable declarations are unchanged
(`@13`): the argument `7` is a numeral carrying no extern declaration. -/

/-- Applied impure-identity: `(extern fn @13 x : (int) -> int) 7`.  Applying `@13`
    to a numeral routes the FR derivation through the impure `callFR`. -/
def appliedFnExternProg : Expr :=
  Expr.app
    (Expr.externFn 13 "x" Typ.int false SyntaxPredicate.noPred builtinImpureIdRetSpec [] [])
    (Expr.num 7)

/-- The reachable declarations of the applied program are exactly `@13`, matched
    by its registry entry.  The function position reaches it (`@13` via
    `externFn`); the argument `7` reaches none (a numeral). -/
theorem appliedFnExtern_agreesWithProgram :
    TrustedRegistryAgreesWithProgram appliedFnExternProg fnExternRegistry := by
  intro id d entry hprog hlookup
  unfold appliedFnExternProg at hprog
  cases hprog with
  | app_fun hb1 =>
      cases hb1 with
      | externFn =>
          have hl : TrustedRegistry.lookup? fnExternRegistry 13
              = some ⟨builtinImpureIdDecl, builtinImpureIdImpl, builtinImpureIdSpec⟩ := by
            simp [fnExternRegistry, TrustedRegistry.lookup?, builtinImpureIdDecl]
          rw [hl] at hlookup
          cases hlookup
          rfl
      | externFn_return hret => cases hret
  | app_arg hb1 =>
      -- `7` is a numeral: no extern declarations.
      cases hb1

/-- Per-context trust premise for the applied program at the empty context. -/
theorem appliedFnExtern_hagrees :
    TrustedRegistryAgreesWithReachable appliedFnExternProg openEmptyCtx fnExternRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) appliedFnExtern_agreesWithProgram

/-! **Non-vacuity (why `appliedFnExtern_FR` is not vacuous).** `openEmptyCtx` is
    impure (`pureCtx = false`) — the same empty, impure context the interpreter
    typechecks a top-level program in (`Main.initialTypeContext`; it differs only
    in the initial tag counter `nextTag`, immaterial to typeability since `@13`'s
    `simple`/`noPred` return allocates no guard tags).  So the impure
    `extern fn @13` application is well-typed here: the `extern_fn_impure_id`
    example is *this exact program* (`(extern fn @13 x …) 7` = `appliedFnExternProg`)
    and typechecks and runs to `7`.  Because the program *applies* the extern,
    those well-typed runs route through `builtinImpureIdSpec.callFR`.  (A Lean-level
    `typecheckExpr … = .ok _` witness would need `native_decide` — `typecheckExpr`
    is well-founded-recursive and does not reduce by `rfl`; the FR theorems below
    already carry the engine's pre-existing `native_decide` baseline, so adding one
    would not introduce a new *kind* of axiom, but we avoid extra instances and
    rely on the interpreter check, as every other program-FR artifact here does.) -/

/-- **Fully-exercised program-level FR for the applied impure extern.** For the
    program `(extern fn @13 …) 7`, the trusted registry agrees with the reachable
    decls, so `TypeSystemEnforcesFaultRobustness_at` yields fault-robustness — and
    because the program applies `@13`, the derivation routes that application
    through `builtinImpureIdSpec.callFR`, the first relational `fn` call boundary. -/
theorem appliedFnExtern_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry fnExternRegistry)
      appliedFnExternProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at fnExternRegistry appliedFnExternProg s obs openEmptyCtx
    appliedFnExtern_hagrees

end FnExternFR
