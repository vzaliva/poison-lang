/-
  ExternProofs.lean - Concrete validation attempts for built-in externs.

  This file is intentionally not a public constructor framework.  It records
  direct proof-side evidence for the interpreter's built-in externs and, when a
  declaration is too strong, the smallest failed FR obligation exposed by the
  direct validation attempt.
-/
import LeanProofs.ExternBoundary

open Std

namespace ExternProofs

/-- The return type currently declared by examples for built-in `abs` (`@12`). -/
def builtinAbsReturnQTyp : QTyp :=
  { etyp := ETyp.int, poison := false, pred := Predicate.noPred }

/-- The return descriptor currently used by the built-in `abs` declaration. -/
def builtinAbsRetSpec : ExternReturn :=
  .simple .int false .noPred

/-- Proof-side declaration for the interpreter's built-in `abs` extern (`@12`). -/
def builtinAbsDecl : ExternDeclaration :=
  { id := 12
    kind := .pfn
    typ := .int
    argName := some "x"
    retSpec := some builtinAbsRetSpec
    effects := []
    preds := collectExternPreds builtinAbsRetSpec []
    argPoison := false }

/-- Proof-side copy of the interpreter's built-in `abs` implementation. -/
def builtinAbsPfn : VarEnv → Value → Memory → Except ExternError Value
  | _, Value.num n, _ => .ok (Value.num (Int.ofNat n.natAbs))
  | _, _, _ => .error (.implFailure 12 "expected int argument")

/-- Runtime implementation shape for the built-in `abs` extern (`@12`). -/
def builtinAbsImpl : ExternImpl :=
  .pfn builtinAbsPfn

theorem builtinAbsPfn_negOne :
    builtinAbsPfn emptyVarEnv (Value.num (-1)) emptyMemory = .ok (Value.num 1) := by
  rfl

theorem builtinAbsPfn_two :
    builtinAbsPfn emptyVarEnv (Value.num 2) emptyMemory = .ok (Value.num 2) := by
  rfl

private theorem not_agreeValueUnder_builtinAbsReturn_num_ne
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (hne : n₀ ≠ n₁) :
    ¬ agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ builtinAbsReturnQTyp
      (Value.num n₀) (Value.num n₁) := by
  intro hagree
  cases hagree with
  | clean_eq_nonref_nonarrow _hpoison _hnotfun _hnotref heq =>
      simp only [Value.num.injEq] at heq
      exact hne heq
  | clean_internal_arrow _hclean_internal hetyp _htcl _hmatch _hcap _hmv1 _hmc1
      _hmv2 _hmc2 _htyping1 _htyping2 _hv1 _hv2 =>
      cases hetyp
  | clean_internal_arrow_extern _hclean_internal hetyp _htcl _hmatch _hcap _hmv1
      _hmc1 _hmv2 _hmc2 _htyping1 _htyping2 _hv1 _hv2 =>
      cases hetyp
  | dirty_internal_arrow _hdirty_internal hisArrow _htyp1 _htyp2 =>
      simp [builtinAbsReturnQTyp, ETyp.isArrow] at hisArrow
  | clean_internal_parrow _hclean_internal hetyp _htcl _hmatch _hcap _hmv1 _hmc1
      _hmv2 _hmc2 _htyping1 _htyping2 _hv1 _hv2 =>
      cases hetyp
  | clean_internal_parrow_extern _hclean_internal hetyp _htcl _hmatch _hcap _hmv1
      _hmc1 _hmv2 _hmc2 _htyping1 _htyping2 _hv1 _hv2 =>
      cases hetyp
  | dirty_internal_parrow _hdirty_internal hisParrow _htyp1 _htyp2 =>
      simp [builtinAbsReturnQTyp, ETyp.isParrow] at hisParrow
  | clean_ref _hpoison hetyp _hlookup1 _hin _hv1 _hlookup2 _hv2 =>
      cases hetyp
  | withPred_true_eq _k htag _hregime _hnotfun _hnotref _heq =>
      simp [builtinAbsReturnQTyp, qtypGuardTag] at htag
  | withPred_true_ref _k _htag _hregime hetyp _hlookup1 _hin _hv1 _hlookup2 _hv2 =>
      cases hetyp

private theorem not_resultAgreesIfClean_builtinAbsReturn_num_ne
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (hne : n₀ ≠ n₁) :
    ¬ resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ builtinAbsReturnQTyp
      (Value.num n₀) (Value.num n₁) := by
  intro hresult
  exact not_agreeValueUnder_builtinAbsReturn_num_ne hne
    (hresult (qtypCleanUnder.clean (qt := builtinAbsReturnQTyp) rfl))

/-- Current `abs` declaration obstruction.

If the `abs` result is typed as a clean integer, `StepFRPost` requires clean
output agreement.  But the implementation is input-sensitive, and dirty
integer inputs are not required to agree.  In particular, `abs (-1) = 1` and
`abs 2 = 2`, so the clean-result post demanded by `ExternBoundarySpec.callFR`
cannot be produced for the current declaration.
-/
theorem builtinAbs_cleanPost_obstruction
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning} {θ₀ θ₁ : RealizationMap}
    {cf₀ cf₁ : Config}
    (hres : res.qualType = builtinAbsReturnQTyp) :
    ¬ StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁
      (Value.num 1) (Value.num 2) := by
  intro hpost
  rcases hpost with
    ⟨_tm', _htag, _hlaws, _hrespects, _θ₀', _θ₁', _hθ₀, _hθ₁, _htyp₀, _htyp₁,
      _hwftm, _hwfctx, _hbounded, _hwfcfg₀, _hwfcfg₁, _hric₀, _hric₁, _hreg,
      _hcons₀, _hcons₁, _hagree, _hvalc₀, _hvalc₁, hresult⟩
  exact not_resultAgreesIfClean_builtinAbsReturn_num_ne (by norm_num : (1 : Int) ≠ 2)
    (by simpa [hres] using hresult)

end ExternProofs
