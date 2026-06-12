/-
  ExternProofs.lean - Concrete validation attempts for built-in externs.

  This file is intentionally not a public constructor framework.  It records
  direct proof-side evidence for the interpreter's built-in externs and, when a
  declaration is too strong, the smallest failed FR obligation exposed by the
  direct validation attempt.
-/
import LeanPoison.ExternBuiltins
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

/-- Runtime implementation shape for the built-in `abs` extern (`@12`): the
    interpreter's shared `absImpl` (`LeanPoison.ExternBuiltins`), so the running
    interpreter and this proof-side spec reference the same function. -/
def builtinAbsImpl : ExternImpl :=
  .pfn absImpl

theorem absImpl_negOne :
    absImpl emptyVarEnv (Value.num (-1)) emptyMemory = .ok (Value.num 1) := by
  rfl

theorem absImpl_two :
    absImpl emptyVarEnv (Value.num 2) emptyMemory = .ok (Value.num 2) := by
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
      _hcons₀, _hcons₁, _hagree, _hvalc₀, _hvalc₁, hresult, _hrdA, _hrdB⟩
  exact not_resultAgreesIfClean_builtinAbsReturn_num_ne (by norm_num : (1 : Int) ≠ 2)
    (by simpa [hres] using hresult)

/-! ## Direct clean-input validation for built-in `abs` (`@12`)

The declaration is intentionally clean-input to clean-output:

```poison
extern pfn @12 x : (int :> clean {}) -> ((int :> clean {}))
```

The obstruction above only rules out a *dirty*-input reading.  The lemmas below
build the clean-input case: `abs`'s implementation is a function of its integer
argument, so two clean-agreeing integer arguments produce equal absolute values,
which satisfies the clean-integer-return `resultAgreesIfClean`.
-/

/-- The exact computation performed by `absImpl` on an integer argument. -/
private theorem absImpl_num (env : VarEnv) (n : Int) (mem : Memory) :
    absImpl env (Value.num n) mem = .ok (Value.num (Int.ofNat n.natAbs)) :=
  rfl

/-- `absImpl` succeeds only on integer arguments, returning the integer
    absolute value as a clean `Value.num`. -/
private theorem absImpl_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : absImpl env vArg mem = .ok vRaw) :
    ∃ n : Int, vArg = Value.num n ∧ vRaw = Value.num (Int.ofNat n.natAbs) := by
  cases vArg with
  | num n =>
      simp only [absImpl, Except.ok.injEq] at h
      exact ⟨n, rfl, h.symm⟩
  | _ => simp [absImpl] at h

/-- Helper 1: `absImpl` is a function of its integer argument, so equal
    integer inputs produce equal outputs. -/
private theorem absImpl_output_eq_of_arg_eq
    {n₀ n₁ : Int} (hn : n₀ = n₁) :
    Value.num (Int.ofNat n₀.natAbs) = Value.num (Int.ofNat n₁.natAbs) := by
  rw [hn]

/-- Helper 3: equal `abs` outputs satisfy `resultAgreesIfClean` for the clean
    integer return type.  Mirrors `agreeValueUnder.clean_eq_nonref_nonarrow`
    specialized to the `abs` return `QTyp`. -/
private theorem resultAgreesIfClean_builtinAbsReturn_of_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {n₀ n₁ : Int}
    (heq : n₀ = n₁) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ builtinAbsReturnQTyp
      (Value.num n₀) (Value.num n₁) := by
  intro _hclean
  cases heq
  exact
    agreeValueUnder.clean_eq_nonref_nonarrow (hpoison := rfl) (hnotfun := rfl)
      (hnotref := by rintro ⟨ls, hls⟩; cases hls) rfl

/-- Helper 4: the built-in `abs` extern satisfies the operational-safety
    contract.  The pure branch returns a well-formed `Value.num`; the impure and
    value branches are impossible by `ExternImpl` constructor discrimination.

    This is a complete `ExternBoundarySpec.operational` field for `@12`. -/
theorem builtinAbsImpl_operationalSafe :
    ExternOperationalSafe builtinAbsDecl builtinAbsImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- impure `fn` branch: `builtinAbsImpl` is a `pfn`, so this is vacuous.
    intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinAbsImpl] at himpl
  · -- pure `pfn` branch: the returned raw value is a well-formed `num`.
    intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinAbsImpl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨n, _harg, hraw⟩ := absImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · -- `val` branch: impossible.
    intro v himpl _ _
    simp [builtinAbsImpl] at himpl
  · -- fn mem-mono: `builtinAbsImpl` is a `pfn`, so the fn branch is vacuous.
    intro implFn himpl
    simp [builtinAbsImpl] at himpl

/-! ### Argument equality from clean agreement (Helper 2 core)

These lemmas are independent of any extern boundary plumbing.  Together they
say: at a call boundary whose body context binds the argument to a *clean
integer* type, the two clean-agreeing runs supply equal integer arguments. -/

/-- A clean integer agreement forces value equality: for a `QTyp` of `int`
    enriched type, `agreeValueUnder` on two `Value.num`s gives equal integers.
    Every closure/reference constructor is ruled out by the `int` enriched type;
    the two equality constructors carry the value equation directly. -/
private theorem agreeValueUnder_num_int_imp_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {n₀ n₁ : Int}
    (hInt : qt.etyp = ETyp.int)
    (hagree : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁)) :
    n₀ = n₁ := by
  cases hagree with
  | clean_eq_nonref_nonarrow _hpoison _hnotfun _hnotref heq => simpa using heq
  | clean_internal_arrow _hci hetyp _ _ _ _ _ _ _ _ _ _ _ => simp [hInt] at hetyp
  | clean_internal_arrow_extern _hci hetyp _ _ _ _ _ _ _ _ _ _ _ => simp [hInt] at hetyp
  | dirty_internal_arrow _hci hisArrow _ _ => simp [hInt, ETyp.isArrow] at hisArrow
  | clean_internal_parrow _hci hetyp _ _ _ _ _ _ _ _ _ _ _ => simp [hInt] at hetyp
  | clean_internal_parrow_extern _hci hetyp _ _ _ _ _ _ _ _ _ _ _ => simp [hInt] at hetyp
  | dirty_internal_parrow _hci hisParrow _ _ => simp [hInt, ETyp.isParrow] at hisParrow
  | clean_ref _hpoison hetyp _ _ _ _ _ => simp [hInt] at hetyp
  | withPred_true_eq _k _htag _hregime _hnotfun _hnotref heq => simpa using heq
  | withPred_true_ref _k _htag _hregime hetyp _ _ _ _ _ => simp [hInt] at hetyp

/-- Reference agreement forces a *common* logical location.  Given clean
    agreement of two `Value.loc` runtime values at a reference type `ref ls`,
    there is a single `l ∈ ls` that both realisation maps send to the respective
    runtime addresses.  Both the literally-clean (`clean_ref`) and
    guarded-active (`withPred_true_ref`) reference cases supply this shared `l`;
    every other constructor contradicts `qt.etyp = ref ls`.  This is the linchpin
    that makes a memory-read read-dependency fault-robust: the argument condition
    on the reference forces both runs to read *the same* cell. -/
private theorem agreeValueUnder_ref_common_loc
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {ls : LocSet} {addr₀ addr₁ : Address}
    (hetyp : qt.etyp = ETyp.ref ls)
    (hval : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.loc addr₀) (Value.loc addr₁)) :
    ∃ l, l ∈ ls ∧ θ₀.lookup l = some addr₀ ∧ θ₁.lookup l = some addr₁ := by
  cases hval with
  | clean_ref _hpoison hetyp' hlk1 hin hv1 hlk2 hv2 =>
      rename_i ls' l a₁ a₂
      have hls : ls' = ls := ETyp.ref.inj (hetyp'.symm.trans hetyp)
      subst hls
      have ha1 : a₁ = addr₀ := (Value.loc.inj hv1).symm
      have ha2 : a₂ = addr₁ := (Value.loc.inj hv2).symm
      exact ⟨l, hin, by rw [← ha1]; exact hlk1, by rw [← ha2]; exact hlk2⟩
  | withPred_true_ref _k _htag _hreg hetyp' hlk1 hin hv1 hlk2 hv2 =>
      rename_i ls' l a₁ a₂
      have hls : ls' = ls := ETyp.ref.inj (hetyp'.symm.trans hetyp)
      subst hls
      have ha1 : a₁ = addr₀ := (Value.loc.inj hv1).symm
      have ha2 : a₂ = addr₁ := (Value.loc.inj hv2).symm
      exact ⟨l, hin, by rw [← ha1]; exact hlk1, by rw [← ha2]; exact hlk2⟩
  | clean_eq_nonref_nonarrow _hp _hnf hnotref _ => exact absurd ⟨ls, hetyp⟩ hnotref
  | withPred_true_eq _k _htag _hreg _hnf hnotref _ => exact absurd ⟨ls, hetyp⟩ hnotref
  | clean_internal_arrow _hci het _ _ _ _ _ _ _ _ _ _ _ => rw [hetyp] at het; simp at het
  | clean_internal_arrow_extern _hci het _ _ _ _ _ _ _ _ _ _ _ => rw [hetyp] at het; simp at het
  | dirty_internal_arrow _hci hisA _ _ => rw [hetyp] at hisA; simp [ETyp.isArrow] at hisA
  | clean_internal_parrow _hci het _ _ _ _ _ _ _ _ _ _ _ => rw [hetyp] at het; simp at het
  | clean_internal_parrow_extern _hci het _ _ _ _ _ _ _ _ _ _ _ => rw [hetyp] at het; simp at het
  | dirty_internal_parrow _hci hisP _ _ => rw [hetyp] at hisP; simp [ETyp.isParrow] at hisP

/-- Helper 2: clean agreement at a call-body entry forces the two integer
    arguments to be equal.  Given two clean-agreeing runs whose shared body
    context binds `x` to a clean integer type, and whose runtime environments
    bind `x` to `Value.num n₀` / `Value.num n₁`, we get `n₀ = n₁`. -/
private theorem builtinAbs_arg_eq_of_bodyAgree
    {predSat : PredSat} {ctx : TypeContext}
    {entry₀ entry₁ : ExternCallEntry} {θ₀ θ₁ : RealizationMap}
    {x : Name} {qtArg : QTyp} {n₀ n₁ : Int}
    (hagree : BodyEntryInputsAgree predSat ctx entry₀ entry₁ θ₀ θ₁)
    (hbind : ctx.varEnv.lookup x = some qtArg)
    (hclean : qtypCleanUnder ctx.regime qtArg)
    (hInt : qtArg.etyp = ETyp.int)
    (hv₀ : entry₀.bodyConfig.varEnv.lookup x = some (Value.num n₀))
    (hv₁ : entry₁.bodyConfig.varEnv.lookup x = some (Value.num n₁)) :
    n₀ = n₁ := by
  have hvar := hagree.agree.2 x qtArg hbind hclean
  cases hvar with
  | agree_values _x _qt v₀' v₁' hl0 hl1 hval =>
      have e0 : v₀' = Value.num n₀ := Option.some.inj (hl0.symm.trans hv₀)
      have e1 : v₁' = Value.num n₁ := Option.some.inj (hl1.symm.trans hv₁)
      subst e0; subst e1
      exact agreeValueUnder_num_int_imp_eq hInt hval
  | both_none _x _qt hl0 _hl1 => simp [hv₀] at hl0

/-! ### Argument-condition gate ⇒ clean argument

When the declared precondition is clean (`declared.poison = false`), the
typechecker's argument-condition gate (`argConditionSatisfied`,
`LeanPoison/Typecheck.lean`) can pass only if the actual (pc-joined) argument is
clean under the body regime.  This is the typechecking-side fact that lets the
clean-input reading of `abs` dodge `builtinAbs_cleanPost_obstruction`. -/

/-- Gate passing with a clean-declared precondition forces the actual argument
    clean under the regime (Bool level). -/
private theorem argConditionSatisfied_cleanRegime_of_declClean
    {declared actual : QTyp} {R : Regime} {fuel : Nat}
    (hgate : argConditionSatisfied declared actual R fuel = true)
    (hdecl : declared.poison = false) :
    qtypCleanUnderRegime actual R = true := by
  unfold argConditionSatisfied at hgate
  simp only [Bool.and_eq_true] at hgate
  have hmid := hgate.1.2
  rw [hdecl] at hmid
  simpa using hmid

/-- Bridge from the Bool-level `qtypCleanUnderRegime` to the Prop-level
    `qtypCleanUnder` for non-function types. -/
private theorem qtypCleanUnder_of_cleanUnderRegime
    {qt : QTyp} {R : Regime}
    (hbool : qtypCleanUnderRegime qt R = true)
    (hnotfun : qt.etyp.isFunctionType = false) :
    qtypCleanUnder R qt := by
  unfold qtypCleanUnderRegime at hbool
  rw [Bool.or_eq_true] at hbool
  rcases hbool with hp | hmatch
  · exact qtypCleanUnder.clean (by simpa using hp)
  · cases hpred : qt.pred with
    | noPred => simp [hpred] at hmatch
    | guardOnly k =>
        refine qtypCleanUnder.guard k (by simp [qtypGuardTag, hpred]) ?_ hnotfun
        rw [hpred] at hmatch; simpa using hmatch
    | guardClosure k _a _b _e =>
        refine qtypCleanUnder.guard k (by simp [qtypGuardTag, hpred]) ?_ hnotfun
        rw [hpred] at hmatch; simpa using hmatch

/-! ### Call-boundary output and the clean-result conjunct

A successful pure `abs` dispatch returns `Value.num (Int.ofNat n.natAbs)` for an
integer argument `Value.num n`, with memory/config unchanged.  In the
content-bearing *clean-result* case (`res.qualType.poison = false`), the
`resultAgreesIfClean` conjunct of `StepFRPost`—the only conjunct carrying
`abs`-specific content—then follows from argument equality.  (When the result is
dirty, `resultAgreesIfClean` is vacuous via
`resultAgreesIfClean_of_poison_noPred`, since the return predicate is `noPred`.) -/

/-- The output of a successful `abs` call boundary, computed through
    `validateExternReturn`.  A pure dispatch leaves the configuration unchanged
    (`cf = entry.callConfig`). -/
private theorem builtinAbs_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinAbsDecl builtinAbsImpl entry res cf o) :
    ∃ n : Int, entry.argValue = Value.num n ∧
      o = Value.num (Int.ofNat n.natAbs) ∧ cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  simp only [builtinAbsImpl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinAbsRetSpec := by
    simp only [builtinAbsDecl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨n, harg, hraw⟩ := absImpl_ok_shape hrun
  refine ⟨n, harg, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinAbsRetSpec, validateExternReturn, valueMatchesTyp,
    if_true, Except.ok.injEq] at hvalRet
  exact hvalRet.symm

/-! ### Inversion of the `abs` pfn call witness

The newly-landed `Call.pfnExternMember` poison pin lets us extract, from the
typing witness, the shared call-boundary structure: the clean integer result
shape, `ctxAfter = ctx`, and—crucially—the clean argument binding (gate passes
with a clean-declared precondition). -/

/-- A `Value.num` can only be typed at `ETyp.int`. -/
private theorem valueHasETyp_num_etyp
    {θ : RealizationMap} {n : Int} {et : ETyp}
    (h : valueHasETyp θ (Value.num n) et) : et = ETyp.int := by
  cases h
  rfl

/-- The extern tag batch for a single `noPred` return allocates nothing. -/
private theorem collectAndAllocExternTags_noPred (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.noPred] nextTag = .ok ({}, nextTag) :=
  rfl

/-- Shared structure extracted from a pure `abs` call boundary typing witness:
    the result is a clean integer, the post context equals the body context, and
    the body context binds the argument `x` to a type that is clean under the
    body regime (because the argument-condition gate passed against the clean
    declared precondition). -/
private theorem builtinAbs_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinAbsDecl typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      ∃ argQt : QTyp,
        entry.bodyCtx.varEnv.lookup "x" = some argQt ∧
        qtypCleanUnderRegime argQt entry.bodyCtx.regime = true := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinAbsDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hcap' : captures = [] := by simpa [builtinAbsDecl] using hcap.symm
      subst hcap'
      have hx : x = "x" := by
        have : some x = some "x" := by simpa [builtinAbsDecl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have : some retSpec = some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) := by
          simpa [builtinAbsDecl, builtinAbsRetSpec] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hpin' : declaredArgQt.poison = false := by simpa [builtinAbsDecl] using hpin
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp only [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i hgate
          have hcond :
              argConditionSatisfied declaredArgQt
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ bodyState.regime' fuel' = true := by
            simpa [capturesSatisfied] using hgate
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_, ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ?_, ?_⟩
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]; simp only [ctxAfter, applyExternRegimePolicy]; rfl
          · rw [hbody]; exact VarTypeEnv_lookup_update_eq _ "x" _
          · rw [hbody]
            exact argConditionSatisfied_cleanRegime_of_declClean hcond hpin'

/-! ## The `abs` `callFR` field

`builtinAbs_callFR` below proves `ExternCallBoundaryFR builtinAbsDecl
builtinAbsImpl` outright.  The proof rests on the `declaredArgQt.poison =
d.argPoison` premise now carried by `ExternBoundaryTyping.Call.pfnExternMember`
(threaded through the pure trust boundary in `StepFRApp.lean`).  Inverting that
witness (`builtinAbs_call_clean_shape`) gives `declaredArgQt.poison =
builtinAbsDecl.argPoison = false`; the argument-condition gate then forces the
body argument binding clean under the body regime
(`argConditionSatisfied_cleanRegime_of_declClean` →
`qtypCleanUnder_of_cleanUnderRegime`), so `builtinAbs_arg_eq_of_bodyAgree`
(Helper 2) yields argument equality and `resultAgreesIfClean_int_noPred_of_eq`
discharges the only `abs`-specific `StepFRPost` conjunct.

A pure extern allocates nothing, so the rest of `StepFRPost` collapses: take
`tm' = tm`, `θ' = θ`; `ctxAfter entry.bodyCtx res = entry.bodyCtx` and
`entry.bodyOutputConfig cf = entry.bodyConfig` (since `cf = callConfig`), and
every well-formedness / `runtimeInstantiatesCtx` / `regimeConsistentWithCtx` /
`consistentWithRegime` / `agreeOnClean` conjunct is then a `BodyEntryInputsAgree`
field, with `valueHasETyp` / `valueConsistentWithRegime` holding for the
`Value.num` output at the clean integer type.

`builtinAbs_cleanPost_obstruction` (above) remains the guardrail for the
*dirty*-input reading; the clean-input contract proved here does not weaken the
declaration.  The impure mirror runs through `Call.fnExternMember`, which already
carries the arg-poison pin (`declaredArgQt.poison = d.argPoison`); the
regular-closure-extern-body route is rejected at `typecheckFn`. Concrete fn specs
are handled separately; a meaningful shipped `kind = .fn` spec should cover
effecting behavior such as `set_err`, rather than a no-effect identity shim. -/

/-- A successful `abs` call boundary returns `Value.num (Int.ofNat n.natAbs)` for
    an integer argument; the impure branch is impossible (`kind = .pfn`). -/
private theorem builtinAbs_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinAbsDecl builtinAbsImpl entry res cf o) :
    ∃ n : Int, entry.argValue = Value.num n ∧
      o = Value.num (Int.ofNat n.natAbs) ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinAbsDecl] at h
  | pfn hfacts => exact builtinAbs_call_output hfacts

/-- The body-entry environment of a successful `abs` call binds `"x"` to the
    runtime argument value. -/
private theorem builtinAbs_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinAbsDecl builtinAbsImpl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "x" = some entry.argValue := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinAbsDecl] at h
  | pfn hfacts =>
      have hargName : entry.argName = "x" := by
        have h := hfacts.argName
        simp only [builtinAbsDecl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- Argument equality for `abs`: clean body agreement plus the clean argument
    binding (gate passed against the clean precondition) force the two integer
    arguments equal.  This supplies the `hAeq` hypothesis of
    `builtinAbs_call_resultAgrees_of_arg_eq`. -/
private theorem builtinAbs_callRun_argEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinAbsDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinAbsDecl builtinAbsImpl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinAbsDecl builtinAbsImpl entry₁ res cf₁ o₁)
    {m₀ m₁ : Int}
    (hm₀ : entry₀.argValue = Value.num m₀) (hm₁ : entry₁.argValue = Value.num m₁) :
    m₀ = m₁ := by
  obtain ⟨_, _, _, argQt, hbind, hcleanB⟩ := builtinAbs_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "x" = some (Value.num m₀) := by
    rw [builtinAbs_callRun_bodyVar hrun₀, hm₀]
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "x" = some (Value.num m₁) := by
    rw [builtinAbs_callRun_bodyVar hrun₁, hm₁]
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbind
  have hv : v = Value.num m₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : argQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime argQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanB (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbind hcleanP hInt hrv₀ hrv₁

/-- Equal integers give `resultAgreesIfClean` for any clean-int / `noPred` type
    (vacuous when the type is dirty).  Generalizes Helper 3 off the literal
    `builtinAbsReturnQTyp`, so it applies to the actual `res.qualType` whose
    poison varies with the call-site provenance. -/
private theorem resultAgreesIfClean_int_noPred_of_eq
    {predSat : PredSat} {R : Regime} {qt : QTyp}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {m₀ m₁ : Int}
    (hetyp : qt.etyp = ETyp.int) (hpred : qt.pred = Predicate.noPred)
    (heq : m₀ = m₁) :
    resultAgreesIfClean predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.num m₀) (Value.num m₁) := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      cases heq
      exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl)
        (by intro href; rcases href with ⟨ls, hls⟩; simp [hetyp] at hls) rfl
  | guard k htag _hregime _hnotfun =>
      have hnone : qtypGuardTag qt = none := by simp [qtypGuardTag, hpred]
      simp [hnone] at htag

/-- The pure call-boundary FR field for built-in `abs` (`@12`), now provable
    because `Call.pfnExternMember` carries `declaredArgQt.poison = d.argPoison`.
    Most of `StepFRPost` is inherited from `BodyEntryInputsAgree` (a pure extern
    allocates nothing, so `tm' = tm`, `θ' = θ`, `ctxAfter = ctx`); the only
    `abs`-specific conjunct is `resultAgreesIfClean`, split on the result poison:
    dirty is vacuous (`noPred` return), clean runs the argument-equality chain. -/
theorem builtinAbs_callFR : ExternCallBoundaryFR builtinAbsDecl builtinAbsImpl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨hetyp, hpred, hctxAfter, _argQt, _hbind, _hcleanB⟩ := builtinAbs_call_clean_shape htyped₀
  obtain ⟨n₀, harg₀, ho₀, hcf₀⟩ := builtinAbs_callRun_output hrun₀
  obtain ⟨n₁, harg₁, ho₁, hcf₁⟩ := builtinAbs_callRun_output hrun₁
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hvc : ∀ (μ : Memory) (θ : RealizationMap) (n : Int),
      valueConsistentWithRegime predSat ctx.regime res.qualType μ θ (Value.num n) := by
    intro μ θ n
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num n) (by rw [hetyp]; rfl)
  rw [hboc₀, hboc₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hd_res]; exact hbody.reserved₀), (by rw [hd_res]; exact hbody.reserved₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho₀, hetyp]; exact valueHasETyp.num _
  · rw [ho₁, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter']; exact hwfTm
  · rw [hctxAfter']; exact hbody.wfCtx
  · rw [hctxAfter']; exact hbody.tagBounded
  · exact hbody.wfConfig₀
  · exact hbody.wfConfig₁
  · rw [hctxAfter']; exact hbody.runtime₀
  · rw [hctxAfter']; exact hbody.runtime₁
  · rw [hctxAfter']; exact hbody.regime
  · rw [hctxAfter']; exact hbody.consistent₀
  · rw [hctxAfter']; exact hbody.consistent₁
  · rw [hctxAfter']; exact hbody.agree
  · rw [hctxAfter', ho₀]; exact hvc _ _ _
  · rw [hctxAfter', ho₁]; exact hvc _ _ _
  · rw [hctxAfter', ho₀, ho₁]
    exact resultAgreesIfClean_int_noPred_of_eq hetyp hpred
      (by rw [builtinAbs_callRun_argEq htyped₀ hbody hrun₀ hrun₁ harg₀ harg₁])

/-! ## The `abs` `callSingle` field

The single-run clean-pc call boundary post.  Same call shape as `callFR`, but one
run and no relational output-equality: every `ExternBoundarySinglePost` conjunct
is either a single-run hypothesis (transported through `ctxAfter = ctx` and
`bodyOutputConfig cf = bodyConfig`) or reflexive/vacuous (`tm' = tm`, `θ' = θ`). -/
theorem builtinAbs_callSingle : ExternCallBoundarySingle builtinAbsDecl builtinAbsImpl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨hetyp, hpred, hctxAfter, _argQt, _hbind, _hcleanB⟩ := builtinAbs_call_clean_shape htyped
  obtain ⟨n, _harg, ho, hcf⟩ := builtinAbs_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hboc, ho]
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num _) (by rw [hetyp]; rfl)
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

/-! ## The `abs` declaration-boundary fields: `declSingle` and `declFR`

The declaration `extern pfn @12 …` typechecks (via `typecheckExternPfn`) to an
extern *closure* type: a `parrow` whose single `PFnTClosure.extern` captures the
declaration context's type environment.  `resolveArgCondQTyp` allocates no tags,
so `ctxAfter ctx res = ctx` and the post collapses exactly as in the call fields.
The closure obligations (`valueHasETyp`, `valueConsistentWithRegime`) mirror
`StepFRFnPfn.stepFR_pfn` but use the *extern* constructors (`peClosure_extern`,
`deepValueQTypProperty.peClosure_extern`), which need no `toPExpr` purity witness.

`builtinAbs_declSingle` (single run) and `builtinAbs_declFR` (paired) are both
complete below.  `declFR` relies on the expression-coupled runs
(`ExternDeclBoundaryRunForExpr`) that pin both outputs to the closure of the shared
declaration expression — see `builtinAbs_declFR`. -/

/-- The extern closure stored in the `abs` declaration's `parrow` type: it
    captures the declaration context's type environment together with the
    argument precondition `argQt`.  `argQt` is left abstract because the `Decl`
    relation does not pin the syntactic argument predicate; every extern-closure
    constructor takes the precondition as an *implicit*, so declaration-boundary
    well-typedness/consistency is independent of it (it gates only at call time).
    `retSpec` is kept folded as `builtinAbsRetSpec` so the closure matches both
    `typecheckExternPfn`'s output and the extern constructors without reduction. -/
private def builtinAbsExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 12 "x" builtinAbsRetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt []

/-- The exact `TypeResult` produced by typechecking `extern pfn @12 …` in `ctx`
    (with resolved argument precondition `argQt`).  The `parrow` return slot stays
    `parseReturnType builtinAbsRetSpec` (folded); every context field is inherited
    unchanged (no tags/locs allocated, `nextTag` threaded through). -/
private def builtinAbsDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow Typ.int (parseReturnType builtinAbsRetSpec) ctx.pc
        [builtinAbsExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

/-- Inverting an `abs` declaration typing witness pins the result to
    `builtinAbsDeclResult ctx argQt` for some argument precondition `argQt`.  The
    `val`/`fn` constructors are impossible by `kind` mismatch (auto-eliminated);
    the `pfn` constructor reduces through the existing `typecheckExternPfn_ok_res_eq`
    inversion. -/
private theorem builtinAbs_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinAbsDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinAbsDeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 12 "x" Typ.int false argPred builtinAbsRetSpec [] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 12 "x" Typ.int false argPred builtinAbsRetSpec res htcPfn
          exact ⟨argQt, hres⟩

/-- The declaration expression typed against `builtinAbsDecl` is `externPfn @12`
    with the clean integer signature; only its argument predicate is free. -/
private theorem builtinAbs_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinAbsDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

/-- The `abs` declaration's extern closure value is well-typed at the declared
    `parrow` type.  The captured runtime environment `ρ` types against the
    captured type environment `VarTypeEnv.toCaptured ctx.varEnv` via the runtime
    instantiation of `ctx` (mirrors `stepFR_pfn`'s `peClosure` `henv`/`hcover`
    blocks, using the extern constructor which needs no `toPExpr`). -/
private theorem builtinAbs_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures) ρ)
      (builtinAbsDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinAbsRetSpec) ctx.pc
        [builtinAbsExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := []) (htcl := by simp [builtinAbsExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

/-- The `abs` declaration's extern closure value is regime-consistent.  The
    closure carries no guard tag (the result `pred` is `noPred`); its captured-env
    regime/typing property is supplied by the declaration context's
    `consistentWithRegime` (mirrors `stepFR_pfn`'s `valueConsistentWithRegime.noTag`
    + `deepValueQTypProperty` block, using the extern constructor). -/
private theorem builtinAbs_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinAbsDeclResult ctx argQt).qualType μ θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinAbsDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt) (memberCap := []) 12 "x" "x" Typ.int builtinAbsRetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinAbsExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinAbsExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

/-- A successful `abs` declaration boundary leaves the config unchanged and emits
    the extern closure value.  The `val`/`fn` branches are impossible (`kind = .pfn`). -/
private theorem builtinAbs_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinAbsDecl builtinAbsImpl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinAbsDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinAbsDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinAbsDecl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "x" := by
        have h := hargName; simp [builtinAbsDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinAbsRetSpec := by
        have h := hretSpec; simp [builtinAbsDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinAbsDecl] using hval⟩

/-- The `abs` single-run declaration-boundary field.  Mirrors `callSingle`'s
    `ExternBoundarySinglePost` assembly (`tm' = tm`, `θ' = θ`, `ctxAfter = ctx`,
    `PreservesInherited…refl`, `FreshClean…vacuous`), with the extern closure's
    `QTypRespectsTagMeaning` / `valueHasETyp` / `valueConsistentWithRegime`
    obligations discharged by `QTypRespectsTagMeaning_pfn_extern` and the two
    shared extern-closure helpers above. -/
theorem builtinAbs_declSingle : ExternDeclBoundarySingle builtinAbsDecl builtinAbsImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinAbs_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinAbs_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinAbsDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 12 "x" Typ.int (parseReturnType builtinAbsRetSpec)
      ctx.pc builtinAbsRetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinAbs_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinAbs_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

/-! ## The `abs` paired declaration-boundary field `declFR`

`ExternDeclBoundaryFR` now consumes *expression-coupled* runs
(`ExternDeclBoundaryRunForExpr postExpr …`), so both outputs are known to be the
closure of the **same** declaration expression `postExpr` — hence
`o₀ = Value.peClosure "x" postExpr ρ₀` and `o₁ = Value.peClosure "x" postExpr ρ₁`
share the argument predicate `argPredT`.  The two clean extern parrows then agree
via `agreeValueUnder.clean_internal_parrow_extern` (whose `hv₁`/`hv₂` bind one
`argPred` for both sides).  The remaining `StepFRPost` conjuncts mirror
`StepFRFnPfn.stepFR_pfn`'s declaration assembly, discharged by the shared
extern-closure helpers (`builtinAbs_decl_valueHasETyp` / `_valueConsistent`) and
`QTypRespectsTagMeaning_pfn_extern`. -/

theorem builtinAbs_declFR : ExternDeclBoundaryFR builtinAbsDecl builtinAbsImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinAbs_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinAbs_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinAbs_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinAbs_declRun_shape hrun₁.run
  -- Both outputs are the closure of the shared `postExpr`, hence share `argPredT`.
  have ho₀ : o₀ = Value.peClosure "x"
      (Expr.externPfn 12 "x" Typ.int false argPredT builtinAbsRetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "x"
      (Expr.externPfn 12 "x" Typ.int false argPredT builtinAbsRetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinAbsDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 12 "x" Typ.int (parseReturnType builtinAbsRetSpec)
      ctx.pc builtinAbsRetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinAbs_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinAbs_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinAbs_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinAbs_decl_valueConsistent hric₁ hcwr₁
  · -- resultAgreesIfClean: the two extern parrows agree (shared argPredT)
    rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinAbsDeclResult ctx argQt).qualType.etyp =
            ETyp.parrow Typ.int (parseReturnType builtinAbsRetSpec) ctx.pc
              [builtinAbsExternClosure ctx argQt] := rfl
        have htcl : builtinAbsExternClosure ctx argQt ∈ [builtinAbsExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinAbsDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinAbsDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinAbsDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinAbsDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinAbsDeclResult]
        simp [hnone] at htag

/-- The complete trusted-extern-entry boundary contract for the built-in `abs`
    extern (`@12`): all five `ExternBoundarySpec` fields.  This is the roadmap's
    first fully proven trusted entry. -/
theorem builtinAbsSpec : ExternBoundarySpec builtinAbsDecl builtinAbsImpl where
  declFR := builtinAbs_declFR
  callFR := builtinAbs_callFR
  declSingle := builtinAbs_declSingle
  callSingle := builtinAbs_callSingle
  operational := builtinAbsImpl_operationalSafe

/-! ## The inner curried-`max` extern (`@11`)

`@11` is the inner stage of curried `max`: `extern pfn @11 b : (int :> clean {}) ->
((int :> clean {}))`.  It has the *same declared shape* as `abs` (`@12`), so its
declaration-boundary fields reuse the abs machinery (`retSpec` is generic).  The
difference is the implementation: `@11` reads the captured outer argument `a` from
its environment and returns `Value.num (max a b)`.  The call-boundary clean
agreement therefore rests on both the argument `b` (agreeing via the gate) and the
captured `a` (agreeing via the body-entry `agreeOnClean`). -/

/-- The return descriptor for inner `max` (`@11`) — a clean integer, as for `abs`. -/
def builtinMax11RetSpec : ExternReturn :=
  .simple .int false .noPred

/-- Proof-side declaration for the inner curried-`max` extern (`@11`). -/
def builtinMax11Decl : ExternDeclaration :=
  { id := 11
    kind := .pfn
    typ := .int
    argName := some "b"
    retSpec := some builtinMax11RetSpec
    effects := []
    preds := collectExternPreds builtinMax11RetSpec []
    argPoison := false }

/-- Capture-bearing declaration for the inner curried-`max` extern (`@11`), carrying
    the read dependency `captures: { a :> (int :> clean {}) }` (`doc/ffi-proposal.md`).
    This is the trusted contract under which `@11`'s clean `max a b` result is
    fault-robust: the captured `a` is a declared clean integer dependency.  It is a
    *distinct* declaration from `builtinMax11Decl` (captures `[]`): the captures=`[]`
    declaration cannot close the relational call boundary (that was the gap), and a
    top-level declaration with this `captures` list is not produced by the current AST
    (`doc/ffi-proposal.md`), so only the call-boundary field is proved here. -/
def builtinMax11CapturesDecl : ExternDeclaration :=
  { id := 11
    kind := .pfn
    typ := .int
    argName := some "b"
    retSpec := some builtinMax11RetSpec
    effects := []
    preds := collectExternPreds builtinMax11RetSpec []
    argPoison := false
    captures := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩] }

/-- Runtime implementation shape for the inner-`max` extern (`@11`): the
    interpreter's shared `innerMaxImpl` (`LeanPoison.ExternBuiltins`). -/
def builtinMax11Impl : ExternImpl :=
  .pfn innerMaxImpl

/-- `innerMaxImpl` succeeds only on an integer argument `b` with a captured
    integer `a`, returning the clean `Value.num (max a b)`. -/
private theorem innerMaxImpl_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : innerMaxImpl env vArg mem = .ok vRaw) :
    ∃ a b : Int, vArg = Value.num b ∧ VarEnv.lookup env "a" = some (Value.num a) ∧
      vRaw = Value.num (max a b) := by
  cases vArg with
  | num b =>
      simp only [innerMaxImpl] at h
      cases ha : VarEnv.lookup env "a" with
      | none => rw [ha] at h; simp at h
      | some va =>
          cases va with
          | num a =>
              rw [ha] at h
              simp only [Except.ok.injEq] at h
              exact ⟨a, b, rfl, rfl, h.symm⟩
          | _ => rw [ha] at h; simp at h
  | _ => simp [innerMaxImpl] at h

/-- The inner-`max` extern (`@11`) satisfies the operational-safety contract: the
    pure branch returns a well-formed `Value.num`; the impure and value branches are
    impossible by `ExternImpl` constructor discrimination. -/
theorem builtinMax11Impl_operationalSafe :
    ExternOperationalSafe builtinMax11Decl builtinMax11Impl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMax11Impl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨a, b, _harg, _ha, hraw⟩ := innerMaxImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · intro v himpl _ _
    simp [builtinMax11Impl] at himpl
  · intro implFn himpl
    simp [builtinMax11Impl] at himpl

/-! ### `@11` declaration-boundary fields (reuse of the abs machinery)

`@11` has the same clean-int `pfn` declaration shape as `abs`, so its
declaration-boundary fields are a verbatim adaptation of `builtinAbs_decl*`
(every underlying extern-closure lemma is `retSpec`-generic). -/

private def builtinMax11ExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 11 "b" builtinMax11RetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt []

private def builtinMax11DeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11ExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

private theorem builtinMax11_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11Decl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinMax11DeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 11 "b" Typ.int false argPred builtinMax11RetSpec [] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 11 "b" Typ.int false argPred builtinMax11RetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMax11_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11Decl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

private theorem builtinMax11_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (builtinMax11DeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11ExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := []) (htcl := by simp [builtinMax11ExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

private theorem builtinMax11_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMax11DeclResult ctx argQt).qualType μ θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMax11DeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt) (memberCap := []) 11 "b" "b" Typ.int builtinMax11RetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinMax11ExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinMax11ExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

private theorem builtinMax11_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinMax11Decl builtinMax11Impl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMax11Decl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinMax11Decl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11Decl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "b" := by
        have h := hargName; simp [builtinMax11Decl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMax11RetSpec := by
        have h := hretSpec; simp [builtinMax11Decl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinMax11Decl] using hval⟩

theorem builtinMax11_declSingle : ExternDeclBoundarySingle builtinMax11Decl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMax11_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinMax11_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinMax11DeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinMax11_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinMax11_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

theorem builtinMax11_declFR : ExternDeclBoundaryFR builtinMax11Decl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMax11_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinMax11_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMax11_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMax11_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinMax11DeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinMax11_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinMax11_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinMax11_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinMax11_decl_valueConsistent hric₁ hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinMax11DeclResult ctx argQt).qualType.etyp =
            ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
              [builtinMax11ExternClosure ctx argQt] := rfl
        have htcl : builtinMax11ExternClosure ctx argQt ∈ [builtinMax11ExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinMax11DeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinMax11DeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinMax11DeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinMax11DeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinMax11DeclResult]
        simp [hnone] at htag

/-! ### `@11` call-boundary fields

`@11`'s call output is `Value.num (max a b)`, reading the captured `a`.  The
clean-int result shape and clean argument binding mirror `abs`; the relational
`callFR` additionally needs the captured `a` to agree.  That dependency is not
expressible by the current extern summary alone; the precise model should add an
explicit captured-dependency contract rather than tainting by the whole captured
environment. -/

/-- The output of a successful `@11` call: `Value.num (max a b)` for the integer
    argument `b` and the captured integer `a`.  A pure dispatch leaves the config
    unchanged. -/
private theorem builtinMax11_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinMax11Decl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinMax11RetSpec := by
    simp only [builtinMax11Decl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨a, b, harg, ha, hraw⟩ := innerMaxImpl_ok_shape hrun
  refine ⟨a, b, harg, ha, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinMax11RetSpec, validateExternReturn, valueMatchesTyp,
    if_true, Except.ok.injEq] at hvalRet
  exact hvalRet.symm

/-- A successful `@11` call returns `Value.num (max a b)`; the impure branch is
    impossible (`kind = .pfn`). -/
private theorem builtinMax11_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11Decl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11Decl] at h
  | pfn hfacts => exact builtinMax11_call_output hfacts

/-- The body-entry environment of a successful `@11` call binds `"b"` to the
    runtime argument value. -/
private theorem builtinMax11_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11Decl builtinMax11Impl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "b" = some entry.argValue := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11Decl] at h
  | pfn hfacts =>
      have hargName : entry.argName = "b" := by
        have h := hfacts.argName
        simp only [builtinMax11Decl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- Shared structure from a `@11` call typing witness: clean integer result, post
    context equals body context, and the argument `"b"` is bound clean (gate
    passed against the clean precondition).  Identical to the `abs` inversion up to
    the argument name and declaration. -/
private theorem builtinMax11_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinMax11Decl typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      ∃ argQt : QTyp,
        entry.bodyCtx.varEnv.lookup "b" = some argQt ∧
        qtypCleanUnderRegime argQt entry.bodyCtx.regime = true := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinMax11Decl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hcap' : captures = [] := by simpa [builtinMax11Decl] using hcap.symm
      subst hcap'
      have hx : x = "b" := by
        have : some x = some "b" := by simpa [builtinMax11Decl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have : some retSpec = some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) := by
          simpa [builtinMax11Decl, builtinMax11RetSpec] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hpin' : declaredArgQt.poison = false := by simpa [builtinMax11Decl] using hpin
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp only [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i hgate
          have hcond :
              argConditionSatisfied declaredArgQt
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ bodyState.regime' fuel' = true := by
            simpa [capturesSatisfied] using hgate
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_, ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ?_, ?_⟩
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]; simp only [ctxAfter, applyExternRegimePolicy]; rfl
          · rw [hbody]; exact VarTypeEnv_lookup_update_eq _ "b" _
          · rw [hbody]
            exact argConditionSatisfied_cleanRegime_of_declClean hcond hpin'

/-- The `@11` single-run call-boundary field.  Mirrors `abs`'s `callSingle`: the
    output is a clean integer (`Value.num (max a b)`), so every
    `ExternBoundarySinglePost` conjunct is a single-run hypothesis or
    reflexive/vacuous.  No relational agreement, so the captured `a` is irrelevant. -/
theorem builtinMax11_callSingle : ExternCallBoundarySingle builtinMax11Decl builtinMax11Impl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨hetyp, hpred, hctxAfter, _argQt, _hbind, _hcleanB⟩ := builtinMax11_call_clean_shape htyped
  obtain ⟨a, b, _harg, _ha, ho, hcf⟩ := builtinMax11_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hboc, ho]
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num _) (by rw [hetyp]; rfl)
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

/-! ### `@11` call-boundary FR field — the captured-`a` dependency (the crux)

`builtinMax11_callFR` proves `ExternCallBoundaryFR builtinMax11CapturesDecl
builtinMax11Impl`: the inner curried-`max` call returns the clean integer
`max a b`, reading the captured outer argument `a`.  The relational obligation
needs both the explicit argument `b` (clean via the argument-condition gate) and
the captured `a` (clean via the `captures: { a :> (int :> clean {}) }` contract).
Inverting `Call.pfnExternMember` for `builtinMax11CapturesDecl` pins
`captures = [a]`, so the combined call gate `capturesSatisfied [a] …` extracts
that the captured `a` is clean in the body-entry environment.  Body-entry
`agreeOnClean` then forces `a₀ = a₁`, the argument gate forces `b₀ = b₁`, and
`max a₀ b₀ = max a₁ b₁` discharges the only content-bearing `StepFRPost`
conjunct.  This is what the plain `@11` summary (captures `[]`) could not do. -/

/-- Output of a successful `@11` capture-decl call: `Value.num (max a b)`. -/
private theorem builtinMax11Captures_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinMax11CapturesDecl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinMax11RetSpec := by
    simp only [builtinMax11CapturesDecl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨a, b, harg, ha, hraw⟩ := innerMaxImpl_ok_shape hrun
  refine ⟨a, b, harg, ha, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinMax11RetSpec, validateExternReturn, valueMatchesTyp,
    if_true, Except.ok.injEq] at hvalRet
  exact hvalRet.symm

private theorem builtinMax11Captures_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11CapturesDecl] at h
  | pfn hfacts => exact builtinMax11Captures_call_output hfacts

/-- A successful `@11` capture-decl call binds `"b"` to the runtime argument value
    in the body-entry environment. -/
private theorem builtinMax11Captures_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "b" = some entry.argValue := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11CapturesDecl] at h
  | pfn hfacts =>
      have hargName : entry.argName = "b" := by
        have h := hfacts.argName; simp only [builtinMax11CapturesDecl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- The body-entry environment of a successful `@11` capture-decl call equals the
    unified environment, so the captured `"a"` reads through to its runtime value. -/
private theorem builtinMax11Captures_callRun_bodyConfigVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry res cf o) :
    entry.bodyConfig.varEnv = entry.unifiedEnv := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11CapturesDecl] at h
  | pfn _ => simp [ExternCallEntry.bodyConfig]

/-- A satisfied singleton bare `captures:` dependency `[⟨a, ty, clean, noPred⟩]` means
    the dependency target resolves in the callable environment to a qualified type that
    is clean under the regime. -/
private theorem capturesSatisfied_singleton_bareVar
    {v : Name} {ty : Typ} {u : VarTypeEnv} {m : MemoryTypeEnv} {r : Regime}
    (h : capturesSatisfied
        [⟨CaptureTarget.bareVar v, ty, false, SyntaxPredicate.noPred⟩] u m r = true) :
    ∃ qt : QTyp, u.lookup v = some qt ∧ qtypCleanUnderRegime qt r = true := by
  simp only [capturesSatisfied, List.all_cons, List.all_nil, Bool.and_true,
    captureSatisfied] at h
  cases hlk : u.lookup v with
  | none => rw [hlk] at h; simp at h
  | some qt =>
      rw [hlk] at h
      simp only [captureCondSatisfied, captureSyntaxPredShapeMatches,
        Bool.and_true, Bool.and_eq_true] at h
      exact ⟨qt, rfl, h.2⟩

/-- Shared structure from a `@11` *capture-decl* call typing witness: clean integer
    result, post context equals body context, the argument `"b"` is bound clean (the
    argument gate), and—crucially—the captured `"a"` is bound clean under the body
    regime (the `captures:` gate, extracted from the combined call gate). -/
private theorem builtinMax11Captures_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinMax11CapturesDecl typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      (∃ argQt : QTyp,
        entry.bodyCtx.varEnv.lookup "b" = some argQt ∧
        qtypCleanUnderRegime argQt entry.bodyCtx.regime = true) ∧
      (∃ aQt : QTyp,
        entry.bodyCtx.varEnv.lookup "a" = some aQt ∧
        qtypCleanUnderRegime aQt entry.bodyCtx.regime = true) := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinMax11CapturesDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hcap' : captures =
          [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩] := by
        simpa [builtinMax11CapturesDecl] using hcap.symm
      subst hcap'
      have hx : x = "b" := by
        have : some x = some "b" := by simpa [builtinMax11CapturesDecl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have : some retSpec = some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) := by
          simpa [builtinMax11CapturesDecl, builtinMax11RetSpec] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hpin' : declaredArgQt.poison = false := by simpa [builtinMax11CapturesDecl] using hpin
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp only [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i hgate
          rw [Bool.not_eq_true, Bool.not_eq_false'] at hgate
          rw [Bool.and_eq_true] at hgate
          obtain ⟨hcondArg, hcapGate⟩ := hgate
          obtain ⟨aQt, haLookup, haClean⟩ := capturesSatisfied_singleton_bareVar hcapGate
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_, ⟨⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ?_, ?_⟩,
            ⟨aQt, ?_, ?_⟩⟩
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]; simp only [ctxAfter, applyExternRegimePolicy]; rfl
          · rw [hbody]; exact VarTypeEnv_lookup_update_eq _ "b" _
          · rw [hbody]
            exact argConditionSatisfied_cleanRegime_of_declClean hcondArg hpin'
          · rw [hbody]; exact haLookup
          · rw [hbody]; exact haClean

/-- Captured-`a` equality across the two runs: the captured `"a"` is bound clean in
    the shared body context, so `agreeOnClean` forces the two integer values equal. -/
private theorem builtinMax11Captures_callRun_aEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinMax11CapturesDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry₁ res cf₁ o₁)
    {a₀ a₁ : Int}
    (ha₀ : VarEnv.lookup entry₀.unifiedEnv "a" = some (Value.num a₀))
    (ha₁ : VarEnv.lookup entry₁.unifiedEnv "a" = some (Value.num a₁)) :
    a₀ = a₁ := by
  obtain ⟨_, _, _, _, aQt, hbindA, hcleanA⟩ := builtinMax11Captures_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "a" = some (Value.num a₀) := by
    rw [builtinMax11Captures_callRun_bodyConfigVar hrun₀]; exact ha₀
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "a" = some (Value.num a₁) := by
    rw [builtinMax11Captures_callRun_bodyConfigVar hrun₁]; exact ha₁
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbindA
  have hv : v = Value.num a₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : aQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime aQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanA (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbindA hcleanP hInt hrv₀ hrv₁

/-- Explicit-argument `"b"` equality across the two runs (the argument gate), mirroring
    `builtinAbs_callRun_argEq`. -/
private theorem builtinMax11Captures_callRun_bEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinMax11CapturesDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinMax11CapturesDecl builtinMax11Impl entry₁ res cf₁ o₁)
    {b₀ b₁ : Int}
    (hb₀ : entry₀.argValue = Value.num b₀) (hb₁ : entry₁.argValue = Value.num b₁) :
    b₀ = b₁ := by
  obtain ⟨_, _, _, ⟨argQt, hbindB, hcleanB⟩, _⟩ := builtinMax11Captures_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "b" = some (Value.num b₀) := by
    rw [builtinMax11Captures_callRun_bodyVar hrun₀, hb₀]
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "b" = some (Value.num b₁) := by
    rw [builtinMax11Captures_callRun_bodyVar hrun₁, hb₁]
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbindB
  have hv : v = Value.num b₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : argQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime argQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanB (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbindB hcleanP hInt hrv₀ hrv₁

theorem builtinMax11_callFR : ExternCallBoundaryFR builtinMax11CapturesDecl builtinMax11Impl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨hetyp, hpred, hctxAfter, _, _⟩ := builtinMax11Captures_call_clean_shape htyped₀
  obtain ⟨a₀, b₀, harg₀, ha₀, ho₀, hcf₀⟩ := builtinMax11Captures_callRun_output hrun₀
  obtain ⟨a₁, b₁, harg₁, ha₁, ho₁, hcf₁⟩ := builtinMax11Captures_callRun_output hrun₁
  have hbeq : b₀ = b₁ :=
    builtinMax11Captures_callRun_bEq htyped₀ hbody hrun₀ hrun₁ harg₀ harg₁
  have haeq : a₀ = a₁ :=
    builtinMax11Captures_callRun_aEq htyped₀ hbody hrun₀ hrun₁ ha₀ ha₁
  have hmaxeq : max a₀ b₀ = max a₁ b₁ := by rw [hbeq, haeq]
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hvc : ∀ (μ : Memory) (θ : RealizationMap) (n : Int),
      valueConsistentWithRegime predSat ctx.regime res.qualType μ θ (Value.num n) := by
    intro μ θ n
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num n) (by rw [hetyp]; rfl)
  rw [hboc₀, hboc₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hd_res]; exact hbody.reserved₀), (by rw [hd_res]; exact hbody.reserved₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho₀, hetyp]; exact valueHasETyp.num _
  · rw [ho₁, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter']; exact hwfTm
  · rw [hctxAfter']; exact hbody.wfCtx
  · rw [hctxAfter']; exact hbody.tagBounded
  · exact hbody.wfConfig₀
  · exact hbody.wfConfig₁
  · rw [hctxAfter']; exact hbody.runtime₀
  · rw [hctxAfter']; exact hbody.runtime₁
  · rw [hctxAfter']; exact hbody.regime
  · rw [hctxAfter']; exact hbody.consistent₀
  · rw [hctxAfter']; exact hbody.consistent₁
  · rw [hctxAfter']; exact hbody.agree
  · rw [hctxAfter', ho₀]; exact hvc _ _ _
  · rw [hctxAfter', ho₁]; exact hvc _ _ _
  · rw [hctxAfter', ho₀, ho₁]
    exact resultAgreesIfClean_int_noPred_of_eq hetyp hpred hmaxeq

/-! ### `@11` capture-decl boundary fields — assembling `builtinMax11CapturesSpec`

The capture-bearing declaration `builtinMax11CapturesDecl` (captures `[a]`) needs
all five `ExternBoundarySpec` fields.  The relational `callFR` field is the crux
proved above (`builtinMax11_callFR`).  The remaining four fields are verbatim
mirrors of the captures-`[]` `builtinMax11_*` machinery with the member/type-level
captures list `[]` replaced by `[a] = [⟨CaptureTarget.bareVar "a", Typ.int, false,
SyntaxPredicate.noPred⟩]`.  The `[a]`-threading through `peClosure_extern` /
`deepValueQTypProperty.peClosure_extern` mirrors the `@10` call helpers
(`builtinMax10_call_valueHasETyp` / `_call_valueConsistent`), which thread the same
member list at the call boundary. -/

private def builtinMax11CapturesExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 11 "b" builtinMax11RetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt
    [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]

private def builtinMax11CapturesDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11CapturesExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

private theorem builtinMax11Captures_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11CapturesDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinMax11CapturesDeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 11 "b" Typ.int false argPred builtinMax11RetSpec
                [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 11 "b" Typ.int false argPred builtinMax11RetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMax11Captures_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11CapturesDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

private theorem builtinMax11Captures_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (builtinMax11CapturesDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11CapturesExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩])
      (htcl := by simp [builtinMax11CapturesExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

private theorem builtinMax11Captures_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMax11CapturesDeclResult ctx argQt).qualType μ θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMax11CapturesDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt)
      (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩])
      11 "b" "b" Typ.int builtinMax11RetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinMax11CapturesExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinMax11CapturesExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

private theorem builtinMax11Captures_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinMax11CapturesDecl builtinMax11Impl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMax11CapturesDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinMax11CapturesDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11CapturesDecl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "b" := by
        have h := hargName; simp [builtinMax11CapturesDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMax11RetSpec := by
        have h := hretSpec; simp [builtinMax11CapturesDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinMax11CapturesDecl] using hval⟩

theorem builtinMax11Captures_declSingle :
    ExternDeclBoundarySingle builtinMax11CapturesDecl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMax11Captures_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinMax11Captures_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMax11CapturesDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinMax11Captures_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinMax11Captures_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

theorem builtinMax11Captures_declFR :
    ExternDeclBoundaryFR builtinMax11CapturesDecl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMax11Captures_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinMax11Captures_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMax11Captures_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMax11Captures_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMax11CapturesDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinMax11Captures_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinMax11Captures_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinMax11Captures_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinMax11Captures_decl_valueConsistent hric₁ hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinMax11CapturesDeclResult ctx argQt).qualType.etyp =
            ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
              [builtinMax11CapturesExternClosure ctx argQt] := rfl
        have htcl : builtinMax11CapturesExternClosure ctx argQt ∈
            [builtinMax11CapturesExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinMax11CapturesDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinMax11CapturesDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinMax11CapturesDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinMax11CapturesDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinMax11CapturesDeclResult]
        simp [hnone] at htag

theorem builtinMax11Captures_callSingle :
    ExternCallBoundarySingle builtinMax11CapturesDecl builtinMax11Impl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨hetyp, hpred, hctxAfter, _argQt, _hbind, _hcleanB⟩ := builtinMax11Captures_call_clean_shape htyped
  obtain ⟨a, b, _harg, _ha, ho, hcf⟩ := builtinMax11Captures_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hboc, ho]
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num _) (by rw [hetyp]; rfl)
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

/-- `builtinMax11Impl`'s operational-safety contract restated against the
    capture-bearing declaration `builtinMax11CapturesDecl`.  The proof body only
    discriminates on `builtinMax11Impl`'s constructor shape and never mentions the
    declaration, so it is a verbatim copy of `builtinMax11Impl_operationalSafe`. -/
theorem builtinMax11CapturesImpl_operationalSafe :
    ExternOperationalSafe builtinMax11CapturesDecl builtinMax11Impl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMax11Impl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨a, b, _harg, _ha, hraw⟩ := innerMaxImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · intro v himpl _ _
    simp [builtinMax11Impl] at himpl
  · intro implFn himpl
    simp [builtinMax11Impl] at himpl

/-- The complete trusted-extern-entry boundary contract for the capture-bearing
    inner curried-`max` extern (`@11`, captures `[a]`): all five
    `ExternBoundarySpec` fields.  The relational `callFR` field is the crux
    (`builtinMax11_callFR`); the other four mirror the captures-`[]` machinery. -/
theorem builtinMax11CapturesSpec :
    ExternBoundarySpec builtinMax11CapturesDecl builtinMax11Impl where
  declFR := builtinMax11Captures_declFR
  callFR := builtinMax11_callFR
  declSingle := builtinMax11Captures_declSingle
  callSingle := builtinMax11Captures_callSingle
  operational := builtinMax11CapturesImpl_operationalSafe

/-! ## Guarded read dependency: the inner `@11` with a *guarded* captured `a`

The `captures:` section of `doc/ffi-proposal.md` specifies that `captures:` accepts
a guarded (de-poisoned-under-regime) dependency under exactly the regime-based
satisfaction relation used by extern argument conditions: a declared-clean
dependency is satisfied when the actual is clean *under the call-site regime*
(literally clean, or its guard tag is active in `R`).  `builtinMax11GuardedDecl`
declares the read dependency `captures: { a :> (int :> clean { 5, v => v >= 0 }) }`
— the same inner-`max` shape and `innerMaxImpl`, but the capture now carries a guard
predicate, so the call gate `capturesSatisfied` admits the dependency only when the
actual `a` is clean *under the regime* and carries a matching guard shape.

The call-boundary proof is the curried-`max` proof with the gate-extraction
(`capturesSatisfied_singleton_bareVar_guarded`) generalised to the guarded shape;
the agreement core is unchanged — it was already guard-capable
(`qtypCleanUnder_of_cleanUnderRegime` emits `qtypCleanUnder.guard`, and
`agreeValueUnder_num_int_imp_eq` closes the `withPred_true_eq` arm).  The
declaration-boundary fields carry the capture only as data (threaded as the
closure's member capture list) and never inspect its predicate, so they mirror the
captures-`[a]` machinery verbatim with the member capture list updated. -/

/-- Gate-extraction for a singleton *guarded* bare `captures:` dependency
    `[⟨a, ty, clean, guardClosure ..⟩]`: the dependency target resolves in the
    callable environment to a qualified type that is clean under the regime (the
    declared guard-shape requirement is the third gate conjunct; the conclusion only
    needs the clean-under-regime fact, which the existing agreement chain consumes). -/
private theorem capturesSatisfied_singleton_bareVar_guarded
    {v name : Name} {ty : Typ} {idx : TagIndex} {body : Expr}
    {u : VarTypeEnv} {m : MemoryTypeEnv} {r : Regime}
    (h : capturesSatisfied
        [⟨CaptureTarget.bareVar v, ty, false, SyntaxPredicate.guardClosure idx name body⟩]
        u m r = true) :
    ∃ qt : QTyp, u.lookup v = some qt ∧ qtypCleanUnderRegime qt r = true := by
  simp only [capturesSatisfied, List.all_cons, List.all_nil, Bool.and_true,
    captureSatisfied] at h
  cases hlk : u.lookup v with
  | none => rw [hlk] at h; simp at h
  | some qt =>
      rw [hlk] at h
      simp only [captureCondSatisfied, Bool.and_eq_true] at h
      exact ⟨qt, rfl, h.1.2⟩

/-- Capture-bearing inner `@11` whose read dependency is *guarded*: the declared
    capture `a :> (int :> clean { 5, v => v >= 0 })` carries a guard predicate, so
    the call gate admits the dependency only when the actual `a` is clean under the
    call-site regime (the regime-based satisfaction model of extern arguments). -/
def builtinMax11GuardedDecl : ExternDeclaration :=
  { id := 11
    kind := .pfn
    typ := .int
    argName := some "b"
    retSpec := some builtinMax11RetSpec
    effects := []
    preds := collectExternPreds builtinMax11RetSpec []
    argPoison := false
    captures := [⟨CaptureTarget.bareVar "a", Typ.int, false,
      SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩] }

private def builtinMax11GuardedExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 11 "b" builtinMax11RetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt
    [⟨CaptureTarget.bareVar "a", Typ.int, false,
      SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩]

private def builtinMax11GuardedDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11GuardedExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

private theorem builtinMax11Guarded_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11GuardedDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinMax11GuardedDeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 11 "b" Typ.int false argPred builtinMax11RetSpec
                [⟨CaptureTarget.bareVar "a", Typ.int, false,
                  SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩]
                = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 11 "b" Typ.int false argPred builtinMax11RetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMax11Guarded_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11GuardedDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

private theorem builtinMax11Guarded_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (builtinMax11GuardedDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11GuardedExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false,
        SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩])
      (htcl := by simp [builtinMax11GuardedExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

private theorem builtinMax11Guarded_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMax11GuardedDeclResult ctx argQt).qualType μ θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMax11GuardedDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt)
      (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false,
        SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩])
      11 "b" "b" Typ.int builtinMax11RetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinMax11GuardedExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinMax11GuardedExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

private theorem builtinMax11Guarded_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinMax11GuardedDecl builtinMax11Impl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMax11GuardedDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinMax11GuardedDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11GuardedDecl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "b" := by
        have h := hargName; simp [builtinMax11GuardedDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMax11RetSpec := by
        have h := hretSpec; simp [builtinMax11GuardedDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinMax11GuardedDecl] using hval⟩

theorem builtinMax11Guarded_declSingle :
    ExternDeclBoundarySingle builtinMax11GuardedDecl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMax11Guarded_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinMax11Guarded_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMax11GuardedDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinMax11Guarded_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinMax11Guarded_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

theorem builtinMax11Guarded_declFR :
    ExternDeclBoundaryFR builtinMax11GuardedDecl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMax11Guarded_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinMax11Guarded_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMax11Guarded_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMax11Guarded_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMax11GuardedDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinMax11Guarded_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinMax11Guarded_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinMax11Guarded_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinMax11Guarded_decl_valueConsistent hric₁ hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinMax11GuardedDeclResult ctx argQt).qualType.etyp =
            ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
              [builtinMax11GuardedExternClosure ctx argQt] := rfl
        have htcl : builtinMax11GuardedExternClosure ctx argQt ∈
            [builtinMax11GuardedExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinMax11GuardedDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinMax11GuardedDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinMax11GuardedDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinMax11GuardedDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinMax11GuardedDeclResult]
        simp [hnone] at htag

/-! ### Guarded `@11` call-boundary fields

The call boundary is where the guarded `captures:` contract bites: inverting the
typing witness for `builtinMax11GuardedDecl` runs the fused gate
`argConditionSatisfied … && capturesSatisfied [a :> clean { 5, v => v >= 0 }] …`,
and the guarded gate-extraction (`capturesSatisfied_singleton_bareVar_guarded`)
yields the clean-under-regime fact for the captured `a`.  From there the proof is
identical to curried `max`: the agreement core consumes the clean-under-regime fact
through `qtypCleanUnder_of_cleanUnderRegime` (which produces `qtypCleanUnder.guard`
for an actually-guarded `a`) and `agreeValueUnder.withPred_true_eq`, forcing
`a₀ = a₁`. -/

/-- Output of a successful `@11` guarded-capture-decl call: `Value.num (max a b)`. -/
private theorem builtinMax11Guarded_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinMax11GuardedDecl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinMax11RetSpec := by
    simp only [builtinMax11GuardedDecl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨a, b, harg, ha, hraw⟩ := innerMaxImpl_ok_shape hrun
  refine ⟨a, b, harg, ha, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinMax11RetSpec, validateExternReturn, valueMatchesTyp,
    if_true, Except.ok.injEq] at hvalRet
  exact hvalRet.symm

private theorem builtinMax11Guarded_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry res cf o) :
    ∃ a b : Int, entry.argValue = Value.num b ∧
      VarEnv.lookup entry.unifiedEnv "a" = some (Value.num a) ∧
      o = Value.num (max a b) ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11GuardedDecl] at h
  | pfn hfacts => exact builtinMax11Guarded_call_output hfacts

/-- A successful `@11` guarded-capture-decl call binds `"b"` to the runtime argument
    value in the body-entry environment. -/
private theorem builtinMax11Guarded_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "b" = some entry.argValue := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11GuardedDecl] at h
  | pfn hfacts =>
      have hargName : entry.argName = "b" := by
        have h := hfacts.argName; simp only [builtinMax11GuardedDecl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- The body-entry environment of a successful `@11` guarded-capture-decl call equals
    the unified environment, so the captured `"a"` reads through to its runtime value. -/
private theorem builtinMax11Guarded_callRun_bodyConfigVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry res cf o) :
    entry.bodyConfig.varEnv = entry.unifiedEnv := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11GuardedDecl] at h
  | pfn _ => simp [ExternCallEntry.bodyConfig]

/-- Shared structure from a `@11` *guarded*-capture-decl call typing witness: clean
    integer result, post context equals body context, the argument `"b"` is bound
    clean (the argument gate), and the captured `"a"` is bound clean *under the body
    regime* — extracted from the guarded `captures:` gate via
    `capturesSatisfied_singleton_bareVar_guarded` (the declared guard-shape forces the
    actual `a` to be a guard-shaped clean-under-regime dependency). -/
private theorem builtinMax11Guarded_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinMax11GuardedDecl typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      (∃ argQt : QTyp,
        entry.bodyCtx.varEnv.lookup "b" = some argQt ∧
        qtypCleanUnderRegime argQt entry.bodyCtx.regime = true) ∧
      (∃ aQt : QTyp,
        entry.bodyCtx.varEnv.lookup "a" = some aQt ∧
        qtypCleanUnderRegime aQt entry.bodyCtx.regime = true) := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinMax11GuardedDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hcap' : captures =
          [⟨CaptureTarget.bareVar "a", Typ.int, false,
            SyntaxPredicate.guardClosure ⟨5⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.num 0))⟩] := by
        simpa [builtinMax11GuardedDecl] using hcap.symm
      subst hcap'
      have hx : x = "b" := by
        have : some x = some "b" := by simpa [builtinMax11GuardedDecl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have : some retSpec = some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) := by
          simpa [builtinMax11GuardedDecl, builtinMax11RetSpec] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hpin' : declaredArgQt.poison = false := by simpa [builtinMax11GuardedDecl] using hpin
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp only [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i hgate
          rw [Bool.not_eq_true, Bool.not_eq_false'] at hgate
          rw [Bool.and_eq_true] at hgate
          obtain ⟨hcondArg, hcapGate⟩ := hgate
          obtain ⟨aQt, haLookup, haClean⟩ := capturesSatisfied_singleton_bareVar_guarded hcapGate
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_, ⟨⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ?_, ?_⟩,
            ⟨aQt, ?_, ?_⟩⟩
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]; simp only [ctxAfter, applyExternRegimePolicy]; rfl
          · rw [hbody]; exact VarTypeEnv_lookup_update_eq _ "b" _
          · rw [hbody]
            exact argConditionSatisfied_cleanRegime_of_declClean hcondArg hpin'
          · rw [hbody]; exact haLookup
          · rw [hbody]; exact haClean

/-- Captured-`a` equality across the two runs for the guarded decl: the captured `"a"`
    is bound clean under the body regime (literally clean, or guarded with active tag),
    so the agreement core forces the two integer values equal. -/
private theorem builtinMax11Guarded_callRun_aEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinMax11GuardedDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry₁ res cf₁ o₁)
    {a₀ a₁ : Int}
    (ha₀ : VarEnv.lookup entry₀.unifiedEnv "a" = some (Value.num a₀))
    (ha₁ : VarEnv.lookup entry₁.unifiedEnv "a" = some (Value.num a₁)) :
    a₀ = a₁ := by
  obtain ⟨_, _, _, _, aQt, hbindA, hcleanA⟩ := builtinMax11Guarded_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "a" = some (Value.num a₀) := by
    rw [builtinMax11Guarded_callRun_bodyConfigVar hrun₀]; exact ha₀
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "a" = some (Value.num a₁) := by
    rw [builtinMax11Guarded_callRun_bodyConfigVar hrun₁]; exact ha₁
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbindA
  have hv : v = Value.num a₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : aQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime aQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanA (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbindA hcleanP hInt hrv₀ hrv₁

/-- Explicit-argument `"b"` equality across the two runs (the argument gate). -/
private theorem builtinMax11Guarded_callRun_bEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinMax11GuardedDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinMax11GuardedDecl builtinMax11Impl entry₁ res cf₁ o₁)
    {b₀ b₁ : Int}
    (hb₀ : entry₀.argValue = Value.num b₀) (hb₁ : entry₁.argValue = Value.num b₁) :
    b₀ = b₁ := by
  obtain ⟨_, _, _, ⟨argQt, hbindB, hcleanB⟩, _⟩ := builtinMax11Guarded_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "b" = some (Value.num b₀) := by
    rw [builtinMax11Guarded_callRun_bodyVar hrun₀, hb₀]
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "b" = some (Value.num b₁) := by
    rw [builtinMax11Guarded_callRun_bodyVar hrun₁, hb₁]
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbindB
  have hv : v = Value.num b₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : argQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime argQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanB (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbindB hcleanP hInt hrv₀ hrv₁

/-- **The guarded `@11` `callFR` field** (`doc/ffi-proposal.md`, `captures:`
    section): the inner-`max` call boundary returns the clean integer
    `max a b`, reading the captured `a` whose declared dependency is *guarded*.  The
    captured-`a` equality is sourced through the guarded gate (the declared
    `clean { 5, v => v >= 0 }` requirement is satisfied because the actual `a` is
    clean under the call-site regime), then the already-guard-capable agreement core
    forces `a₀ = a₁`.  This is what makes `captures:` support de-poisoned read
    dependencies at extern call time. -/
theorem builtinMax11Guarded_callFR : ExternCallBoundaryFR builtinMax11GuardedDecl builtinMax11Impl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨hetyp, hpred, hctxAfter, _, _⟩ := builtinMax11Guarded_call_clean_shape htyped₀
  obtain ⟨a₀, b₀, harg₀, ha₀, ho₀, hcf₀⟩ := builtinMax11Guarded_callRun_output hrun₀
  obtain ⟨a₁, b₁, harg₁, ha₁, ho₁, hcf₁⟩ := builtinMax11Guarded_callRun_output hrun₁
  have hbeq : b₀ = b₁ :=
    builtinMax11Guarded_callRun_bEq htyped₀ hbody hrun₀ hrun₁ harg₀ harg₁
  have haeq : a₀ = a₁ :=
    builtinMax11Guarded_callRun_aEq htyped₀ hbody hrun₀ hrun₁ ha₀ ha₁
  have hmaxeq : max a₀ b₀ = max a₁ b₁ := by rw [hbeq, haeq]
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hvc : ∀ (μ : Memory) (θ : RealizationMap) (n : Int),
      valueConsistentWithRegime predSat ctx.regime res.qualType μ θ (Value.num n) := by
    intro μ θ n
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num n) (by rw [hetyp]; rfl)
  rw [hboc₀, hboc₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hd_res]; exact hbody.reserved₀), (by rw [hd_res]; exact hbody.reserved₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho₀, hetyp]; exact valueHasETyp.num _
  · rw [ho₁, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter']; exact hwfTm
  · rw [hctxAfter']; exact hbody.wfCtx
  · rw [hctxAfter']; exact hbody.tagBounded
  · exact hbody.wfConfig₀
  · exact hbody.wfConfig₁
  · rw [hctxAfter']; exact hbody.runtime₀
  · rw [hctxAfter']; exact hbody.runtime₁
  · rw [hctxAfter']; exact hbody.regime
  · rw [hctxAfter']; exact hbody.consistent₀
  · rw [hctxAfter']; exact hbody.consistent₁
  · rw [hctxAfter']; exact hbody.agree
  · rw [hctxAfter', ho₀]; exact hvc _ _ _
  · rw [hctxAfter', ho₁]; exact hvc _ _ _
  · rw [hctxAfter', ho₀, ho₁]
    exact resultAgreesIfClean_int_noPred_of_eq hetyp hpred hmaxeq

theorem builtinMax11Guarded_callSingle :
    ExternCallBoundarySingle builtinMax11GuardedDecl builtinMax11Impl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨hetyp, hpred, hctxAfter, _argQt, _hbind, _hcleanB⟩ := builtinMax11Guarded_call_clean_shape htyped
  obtain ⟨a, b, _harg, _ha, ho, hcf⟩ := builtinMax11Guarded_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hboc, ho]
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num _) (by rw [hetyp]; rfl)
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

theorem builtinMax11GuardedImpl_operationalSafe :
    ExternOperationalSafe builtinMax11GuardedDecl builtinMax11Impl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMax11Impl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨a, b, _harg, _ha, hraw⟩ := innerMaxImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · intro v himpl _ _
    simp [builtinMax11Impl] at himpl
  · intro implFn himpl
    simp [builtinMax11Impl] at himpl

/-- The complete trusted-extern-entry boundary contract for the *guarded*-capture
    inner curried-`max` extern (`@11`, `captures: { a :> (int :> clean { 5, v => v >= 0 }) }`):
    all five `ExternBoundarySpec` fields.  The relational `callFR` field
    (`builtinMax11Guarded_callFR`) is the crux — it discharges the captured-`a`
    agreement through the guarded gate; the other four mirror the captures-`[a]`
    machinery (the capture is carried as data and its predicate never inspected). -/
theorem builtinMax11GuardedSpec :
    ExternBoundarySpec builtinMax11GuardedDecl builtinMax11Impl where
  declFR := builtinMax11Guarded_declFR
  callFR := builtinMax11Guarded_callFR
  declSingle := builtinMax11Guarded_declSingle
  callSingle := builtinMax11Guarded_callSingle
  operational := builtinMax11GuardedImpl_operationalSafe

/-! ## The outer curried-`max` extern (`@10`)

`@10` is the outer stage of curried `max`: `extern pfn @10 a : (int :> clean {}) ->
(extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})))`.  Applying `@10` to a
clean integer `a` returns the inner `@11` pure closure, capturing `a` in its runtime
environment.  `@10` is the first *nested-returning* extern spec, but every
declaration-boundary helper is `retSpec`-generic, so its fields mirror `@11`'s with the
nested return descriptor `builtinMax10RetSpec`. -/

/-- The nested return descriptor for outer `max` (`@10`): returns the `@11` pure closure
    (a clean integer `pfn`), matching the inner `@11` node produced by the shared
    `outerMaxImpl` (`LeanPoison.ExternBuiltins`). -/
def builtinMax10RetSpec : ExternReturn :=
  .nestedPfn 11 "b" .int false .noPred builtinMax11RetSpec
    [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]

/-- Proof-side declaration for the outer curried-`max` extern (`@10`). -/
def builtinMax10Decl : ExternDeclaration :=
  { id := 10
    kind := .pfn
    typ := .int
    argName := some "a"
    retSpec := some builtinMax10RetSpec
    effects := []
    preds := collectExternPreds builtinMax10RetSpec []
    argPoison := false }

/-- Runtime implementation shape for the outer-`max` extern (`@10`): the
    interpreter's shared `outerMaxImpl` (`LeanPoison.ExternBuiltins`). -/
def builtinMax10Impl : ExternImpl :=
  .pfn outerMaxImpl

/-- `outerMaxImpl` succeeds only on an integer argument, returning the `@11` pure
    closure over the (unchanged) call environment. -/
private theorem outerMaxImpl_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : outerMaxImpl env vArg mem = .ok vRaw) :
    ∃ a : Int, vArg = Value.num a ∧
      vRaw = Value.peClosure "b"
        (Expr.externPfn 11 "b" .int false .noPred builtinMax11RetSpec []) env := by
  cases vArg with
  | num a =>
      simp only [outerMaxImpl] at h
      simp only [Except.ok.injEq] at h
      exact ⟨a, rfl, h.symm⟩
  | _ => simp [outerMaxImpl] at h

/-- The outer-`max` extern (`@10`) satisfies operational safety: the pure branch returns
    a well-formed closure — closure well-formedness reduces to the supplied
    `wfVarEnv` for the captured environment — and the impure/value branches are
    impossible by `ExternImpl` constructor discrimination. -/
theorem builtinMax10Impl_operationalSafe :
    ExternOperationalSafe builtinMax10Decl builtinMax10Impl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMax10Impl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem henv _harg
    simp only [builtinMax10Impl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨a, _harg, hraw⟩ := outerMaxImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.peClosure _ _ _ henv
  · intro v himpl _ _
    simp [builtinMax10Impl] at himpl
  · intro implFn himpl
    simp [builtinMax10Impl] at himpl

private def builtinMax10ExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 10 "a" builtinMax10RetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt []

private def builtinMax10DeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow Typ.int (parseReturnType builtinMax10RetSpec) ctx.pc
        [builtinMax10ExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

private theorem builtinMax10_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax10Decl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinMax10DeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 10 "a" Typ.int false argPred builtinMax10RetSpec [] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 10 "a" Typ.int false argPred builtinMax10RetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMax10_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax10Decl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

private theorem builtinMax10_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "a" (Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures) ρ)
      (builtinMax10DeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "a" (Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinMax10RetSpec) ctx.pc
        [builtinMax10ExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := []) (htcl := by simp [builtinMax10ExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

private theorem builtinMax10_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMax10DeclResult ctx argQt).qualType μ θ
      (Value.peClosure "a" (Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMax10DeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt) (memberCap := []) 10 "a" "a" Typ.int builtinMax10RetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinMax10ExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinMax10ExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

private theorem builtinMax10_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinMax10Decl builtinMax10Impl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "a" (Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMax10Decl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinMax10Decl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax10Decl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "a" := by
        have h := hargName; simp [builtinMax10Decl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMax10RetSpec := by
        have h := hretSpec; simp [builtinMax10Decl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinMax10Decl] using hval⟩

theorem builtinMax10_declSingle : ExternDeclBoundarySingle builtinMax10Decl builtinMax10Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMax10_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinMax10_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinMax10DeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 10 "a" Typ.int (parseReturnType builtinMax10RetSpec)
      ctx.pc builtinMax10RetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "a" (Expr.externPfn 10 "a" Typ.int false argPred builtinMax10RetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinMax10_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinMax10_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

theorem builtinMax10_declFR : ExternDeclBoundaryFR builtinMax10Decl builtinMax10Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMax10_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinMax10_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMax10_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMax10_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "a"
      (Expr.externPfn 10 "a" Typ.int false argPredT builtinMax10RetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "a"
      (Expr.externPfn 10 "a" Typ.int false argPredT builtinMax10RetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinMax10DeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 10 "a" Typ.int (parseReturnType builtinMax10RetSpec)
      ctx.pc builtinMax10RetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinMax10_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinMax10_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinMax10_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinMax10_decl_valueConsistent hric₁ hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinMax10DeclResult ctx argQt).qualType.etyp =
            ETyp.parrow Typ.int (parseReturnType builtinMax10RetSpec) ctx.pc
              [builtinMax10ExternClosure ctx argQt] := rfl
        have htcl : builtinMax10ExternClosure ctx argQt ∈ [builtinMax10ExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinMax10DeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinMax10DeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinMax10DeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinMax10DeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinMax10DeclResult]
        simp [hnone] at htag

/-! ### `@10` call-boundary fields

Calling `@10` on a clean integer `a` returns the inner `@11` pure closure
`Value.peClosure "b" (externPfn 11 "b" …) entry.unifiedEnv`, whose captured
environment is the `@10` call's unified environment (holding `a`).  The
result is therefore a *closure value* of `parrow` type, so the content-bearing
`StepFRPost` conjunct is a closure agreement (`agreeValueUnder.clean_internal_parrow_extern`,
exercised at `captures = []`, exactly as in `builtinMax10_declFR`) rather than the
integer equality used by `@11`/`abs`. -/

/-- Output of a successful `@10` call: the `@11` pure closure over the unified
    environment.  This exercises `validateExternReturn`'s `nestedPfn` branch — the
    inner `@11` node produced by `outerMaxImpl` matches the decl-reconstructed `@11`
    node (`[]` captures, `noPred`), so `beqExpr` closes and the validated output is
    the raw closure. -/
private theorem builtinMax10_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinMax10Decl builtinMax10Impl entry res cf o) :
    ∃ a : Int, entry.argValue = Value.num a ∧
      o = Value.peClosure "b"
        (Expr.externPfn 11 "b" Typ.int false SyntaxPredicate.noPred builtinMax11RetSpec [])
        entry.unifiedEnv ∧
      cf = entry.callConfig := by
  rcases hfacts.impl_success with ⟨implFn, retSpec, vRaw, himpl, hretSpec, _hvalMatch, hrun, hvalRet⟩
  simp only [builtinMax10Impl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinMax10RetSpec := by
    simp only [builtinMax10Decl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨a, harg, hraw⟩ := outerMaxImpl_ok_shape hrun
  refine ⟨a, harg, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinMax10Decl, builtinMax10RetSpec, validateExternReturn] at hvalRet
  rw [if_pos (by decide)] at hvalRet
  simp only [Except.ok.injEq] at hvalRet
  exact hvalRet.symm

/-- `builtinMax10` call output over `ExternCallBoundaryRun` (the `fn` branch is
    impossible since `@10` is a `pfn`). -/
private theorem builtinMax10_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMax10Decl builtinMax10Impl entry res cf o) :
    ∃ a : Int, entry.argValue = Value.num a ∧
      o = Value.peClosure "b"
        (Expr.externPfn 11 "b" Typ.int false SyntaxPredicate.noPred builtinMax11RetSpec [])
        entry.unifiedEnv ∧
      cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax10Decl] at h
  | pfn hfacts => exact builtinMax10_call_output hfacts

/-- Shared structure from an `@10` call typing witness: the result is the inner
    `@11` pure-closure type (a `parrow` whose single `PFnTClosure` carries the body
    context's captured environment, holding the outer argument `a`), the result
    predicate is `noPred`, the post context equals the body context, and (in the
    clean case) the recorded function `pc` is `false`.  Inverts `pfnExternMember`
    through the `nestedPfn` branch of `applyPFnTClosureAtCursor`. -/
private theorem builtinMax10_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinMax10Decl typedExpr entry res) :
    ∃ (pc : Poison) (innerArgQt : QTyp),
      res.qualType.etyp = ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) pc
        [PFnTClosure.extern 11 "b" builtinMax11RetSpec
          (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) innerArgQt
          [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]] ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      (res.qualType.poison = false → pc = false) := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinMax10Decl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hx : x = "a" := by
        have : some x = some "a" := by simpa [builtinMax10Decl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = builtinMax10RetSpec := by
        have : some retSpec = some builtinMax10RetSpec := by
          simpa [builtinMax10Decl] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hcap' : captures = [] := by simpa [builtinMax10Decl] using hcap.symm
      subst hcap'
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          simp only [applyPFnTClosureAtCursor, builtinMax10RetSpec, resolveArgCondQTyp,
            resolveArgCondQTyp', argTypToETyp, capturesSatisfied, List.all_nil, Bool.and_true,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i _hgate
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨ctx.pc, ⟨ETyp.int, false, Predicate.noPred⟩, ?_, ?_, ?_, ?_⟩
          · by_cases hprov : (joinPoison p1 p) = true <;>
              simp [normalizeAppResultByProvenance, hprov, hbody]
          · by_cases hprov : (joinPoison p1 p) = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · simp [ctxAfter, hbody]
          · intro hpoison
            by_contra hpc
            rw [Bool.not_eq_false] at hpc
            simp [normalizeAppResultByProvenance, joinPoison, hpc] at hpoison

/-- Poison-generic form of `QTypInQTyp_pfn_extern_root_or_self`: the root qtyp's
    poison field is decoupled from the parrow's function `pc`.  Needed at the call
    boundary because the `@10`-call result carries a provenance-tainted poison that
    can differ from the recorded `pc`.  The descent cases only inspect `qtOuter.etyp`,
    so they are poison-independent. -/
private lemma QTypInQTyp_pfn_extern_root_or_self_anyPoison
    (ctx : TypeContext) (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p poison : Poison)
    (retSpec : ExternReturn) {argQt : QTyp} {captures : List Capture}
    {qt target : QTyp}
    (h : QTypInQTyp qt target)
    (htarget : target =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt captures],
        poison, Predicate.noPred⟩) :
    qt =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt captures],
        poison, Predicate.noPred⟩
    ∨ ∃ y qtRoot, ctx.varEnv.lookup y = some qtRoot ∧ QTypInQTyp qt qtRoot := by
  induction h generalizing ctx id x st₁ st₂ p retSpec argQt with
  | self qt0 =>
      subst qt0; left; rfl
  | in_arrow qtInner qtOuter _ _ _ _ _ _ houterEtyp _ _ =>
      subst qtOuter; simp at houterEtyp
  | in_parrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      let tcl0 : PFnTClosure :=
        PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt captures
      have hEtyp : ETyp.parrow st1 st2 p0 tcls = ETyp.parrow st₁ st₂ p [tcl0] := by
        simpa [tcl0] using houterEtyp.symm
      have htcls : tcls = [tcl0] := by injection hEtyp with _ _ _ htcls
      have htcl0 : tcl = tcl0 := by
        have hmem : tcl ∈ [tcl0] := by simpa [htcls] using htcl
        simpa using hmem
      have hcap' : (y, qtInner) ∈ VarTypeEnv.toCaptured ctx.varEnv := by
        simpa [pfnCapturedEnv, tcl0, htcl0] using hcap
      right
      exact ⟨y, qtInner, VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv y qtInner hcap',
             QTypInQTyp.self qtInner⟩
  | trans qt1 qt2 qt3 h12 _ ih12 ih23 =>
      rcases ih23 (ctx := ctx) (id := id) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p)
               (retSpec := retSpec) (argQt := argQt) htarget with
        hEq | ⟨y, qtRoot, hlookup, hIn⟩
      · exact ih12 (ctx := ctx) (id := id) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p)
               (retSpec := retSpec) (argQt := argQt) hEq
      · right; exact ⟨y, qtRoot, hlookup, QTypInQTyp.trans qt1 qt2 qtRoot h12 hIn⟩

/-- Poison-generic form of `QTypRespectsTagMeaning_pfn_extern`: tag-meaning respect
    for an extern `pfn` parrow result holds at any root poison (the predicate is
    `noPred`, so the root self-inclusion is vacuous and only the captured-variable
    descents matter). -/
private lemma QTypRespectsTagMeaning_pfn_extern_anyPoison
    (tm : TagMeaning) (ctx : TypeContext)
    (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p poison : Poison) (retSpec : ExternReturn)
    {argQt : QTyp} {captures : List Capture}
    (h : wfTagMeaningCtx tm ctx) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt captures],
        poison, Predicate.noPred⟩ := by
  intro qt k d hinq hqd
  rcases QTypInQTyp_pfn_extern_root_or_self_anyPoison ctx id x st₁ st₂ p poison retSpec hinq rfl with
    hEq | ⟨y, qtRoot, hlookup, hInRoot⟩
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · exact (wfTagMeaningCtx_var_lookup_qtyp tm ctx y qtRoot h hlookup) hInRoot hqd

/-- `valueHasETyp` for the `@11` closure returned by an `@10` call, at the inner
    `parrow` type recorded in `res` (pc-generic: the recorded function `pc` is the
    outer call's, not the body context's, so this cannot reuse the decl helper).
    The closure's captured runtime environment is `entry.unifiedEnv`, related to the
    body context's type-env via the body-entry instantiation `hric`. -/
private theorem builtinMax10_call_valueHasETyp
    {entry : ExternCallEntry} {μ : Memory} {θ : RealizationMap}
    {pc : Poison} {innerArgQt : QTyp}
    (hric : runtimeInstantiatesCtx entry.bodyCtx μ entry.unifiedEnv θ) :
    valueHasETyp θ
      (Value.peClosure "b"
        (Expr.externPfn 11 "b" Typ.int false SyntaxPredicate.noPred builtinMax11RetSpec [])
        entry.unifiedEnv)
      (ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) pc
        [PFnTClosure.extern 11 "b" builtinMax11RetSpec
          (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]]) := by
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured entry.bodyCtx.varEnv)
      (argQTyp := innerArgQt) (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩])
      (htcl := by simp) (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : entry.bodyCtx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : entry.bodyCtx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

/-- `valueConsistentWithRegime` for the `@11` closure returned by an `@10` call
    (concrete qualified type, `pc`/`poison`-generic).  Mirrors the decl-boundary
    `valueConsistent`, instantiated at the body context. -/
private theorem builtinMax10_call_valueConsistent
    {predSat : PredSat} {entry : ExternCallEntry} {μ : Memory} {θ : RealizationMap}
    {pc poison : Poison} {innerArgQt : QTyp}
    (hric : runtimeInstantiatesCtx entry.bodyCtx μ entry.unifiedEnv θ)
    (hcwr : consistentWithRegime predSat entry.bodyCtx.regime entry.bodyCtx μ
      entry.unifiedEnv θ) :
    valueConsistentWithRegime predSat entry.bodyCtx.regime
      ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) pc
        [PFnTClosure.extern 11 "b" builtinMax11RetSpec
          (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]],
        poison, Predicate.noPred⟩ μ θ
      (Value.peClosure "b"
        (Expr.externPfn 11 "b" Typ.int false SyntaxPredicate.noPred builtinMax11RetSpec [])
        entry.unifiedEnv) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := innerArgQt)
      (memberCap := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]) 11 "b" "b" Typ.int
      builtinMax11RetSpec entry.unifiedEnv (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) pc
      [PFnTClosure.extern 11 "b" builtinMax11RetSpec
        (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]]
  · rfl
  · rfl
  · simp
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst entry.bodyCtx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup entry.bodyCtx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

/-- `@10` single-run call-boundary field: a single `@10` call produces the `@11`
    pure closure satisfying `ExternBoundarySinglePost` (closure result; tag-meaning
    respect via the poison-generic `pfn`-extern lemma). -/
theorem builtinMax10_callSingle : ExternCallBoundarySingle builtinMax10Decl builtinMax10Impl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨pc, innerArgQt, hetyp, hpred, hctxAfter, _hpcclean⟩ := builtinMax10_call_clean_shape htyped
  obtain ⟨_a, _harg, ho, hcf⟩ := builtinMax10_callRun_output hrun
  have hbcv : entry.bodyConfig.varEnv = entry.unifiedEnv := by simp [ExternCallEntry.bodyConfig]
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hricN : runtimeInstantiatesCtx entry.bodyCtx entry.bodyConfig.memory entry.unifiedEnv θ := by
    rw [← hbcv]; exact hric
  have hconsN : consistentWithRegime predSat entry.bodyCtx.regime entry.bodyCtx
      entry.bodyConfig.memory entry.unifiedEnv θ := by
    rw [← hbcv]; exact hcons
  have qeta : ∀ q : QTyp, q = ⟨q.etyp, q.poison, q.pred⟩ := fun q => by cases q; rfl
  have hqt : res.qualType = ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) pc
      [PFnTClosure.extern 11 "b" builtinMax11RetSpec
        (VarTypeEnv.toCaptured entry.bodyCtx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]],
      res.qualType.poison, Predicate.noPred⟩ := by
    have h := qeta res.qualType
    rw [hetyp, hpred] at h
    exact h
  have hrespects : QTypRespectsTagMeaning tm res.qualType := by
    rw [hqt]
    exact QTypRespectsTagMeaning_pfn_extern_anyPoison tm entry.bodyCtx 11 "b" Typ.int
      (parseReturnType builtinMax11RetSpec) pc res.qualType.poison builtinMax11RetSpec
      (argQt := innerArgQt) (captures := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]) hwfTm
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact builtinMax10_call_valueHasETyp hricN
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hctxAfter', hboc, ho, hqt]
    exact builtinMax10_call_valueConsistent (pc := pc) (poison := res.qualType.poison)
      (innerArgQt := innerArgQt) hricN hconsN
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

/-- `@10` relational call-boundary field (the curried-`max` outer crux): two `@10`
    calls produce two `@11` pure closures that agree.  The content-bearing
    `StepFRPost` conjunct is the *closure* agreement
    `agreeValueUnder.clean_internal_parrow_extern` (exercised at `captures = []`),
    whose captured-environment agreement comes from the body-entry `agreeOnClean`
    over the shared body context — exactly the decl-boundary pattern transported to
    the call boundary (`ctx := entry₀.bodyCtx`, `hric := hbody.runtime₀/₁`). -/
theorem builtinMax10_callFR : ExternCallBoundaryFR builtinMax10Decl builtinMax10Impl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨pc, innerArgQt, hetyp, hpred, hctxAfter, hpcclean⟩ := builtinMax10_call_clean_shape htyped₀
  obtain ⟨_a₀, _harg₀, ho₀, hcf₀⟩ := builtinMax10_callRun_output hrun₀
  obtain ⟨_a₁, _harg₁, ho₁, hcf₁⟩ := builtinMax10_callRun_output hrun₁
  have hbcv₀ : entry₀.bodyConfig.varEnv = entry₀.unifiedEnv := by simp [ExternCallEntry.bodyConfig]
  have hbcv₁ : entry₁.bodyConfig.varEnv = entry₁.unifiedEnv := by simp [ExternCallEntry.bodyConfig]
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hric₀ : runtimeInstantiatesCtx ctx entry₀.bodyConfig.memory entry₀.unifiedEnv θ₀ := by
    rw [← hbcv₀]; exact hbody.runtime₀
  have hric₁ : runtimeInstantiatesCtx ctx entry₁.bodyConfig.memory entry₁.unifiedEnv θ₁ := by
    rw [← hbcv₁]; exact hbody.runtime₁
  have hcons₀ : consistentWithRegime predSat ctx.regime ctx
      entry₀.bodyConfig.memory entry₀.unifiedEnv θ₀ := by rw [← hbcv₀]; exact hbody.consistent₀
  have hcons₁ : consistentWithRegime predSat ctx.regime ctx
      entry₁.bodyConfig.memory entry₁.unifiedEnv θ₁ := by rw [← hbcv₁]; exact hbody.consistent₁
  have hric₁B : runtimeInstantiatesCtx entry₁.bodyCtx entry₁.bodyConfig.memory entry₁.unifiedEnv θ₁ := by
    rw [hctx₁]; exact hric₁
  have hcons₁B : consistentWithRegime predSat entry₁.bodyCtx.regime entry₁.bodyCtx
      entry₁.bodyConfig.memory entry₁.unifiedEnv θ₁ := by rw [hctx₁]; exact hcons₁
  have qeta : ∀ q : QTyp, q = ⟨q.etyp, q.poison, q.pred⟩ := fun q => by cases q; rfl
  have hqt : res.qualType = ⟨ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) pc
      [PFnTClosure.extern 11 "b" builtinMax11RetSpec (VarTypeEnv.toCaptured ctx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]],
      res.qualType.poison, Predicate.noPred⟩ := by
    have h := qeta res.qualType; rw [hetyp, hpred] at h; exact h
  have hrespects : QTypRespectsTagMeaning tm res.qualType := by
    rw [hqt]
    exact QTypRespectsTagMeaning_pfn_extern_anyPoison tm ctx 11 "b" Typ.int
      (parseReturnType builtinMax11RetSpec) pc res.qualType.poison builtinMax11RetSpec
      (argQt := innerArgQt) (captures := [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]) hwfTm
  rw [hboc₀, hboc₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hd_res]; exact hbody.reserved₀), (by rw [hd_res]; exact hbody.reserved₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho₀, hetyp]
    exact builtinMax10_call_valueHasETyp (entry := entry₀) (pc := pc) (innerArgQt := innerArgQt) hric₀
  · rw [ho₁, hetyp]
    have hvh := builtinMax10_call_valueHasETyp (entry := entry₁) (pc := pc)
      (innerArgQt := innerArgQt) hric₁B
    rw [hctx₁] at hvh; exact hvh
  · rw [hctxAfter']; exact hwfTm
  · rw [hctxAfter']; exact hbody.wfCtx
  · rw [hctxAfter']; exact hbody.tagBounded
  · exact hbody.wfConfig₀
  · exact hbody.wfConfig₁
  · rw [hctxAfter']; exact hbody.runtime₀
  · rw [hctxAfter']; exact hbody.runtime₁
  · rw [hctxAfter']; exact hbody.regime
  · rw [hctxAfter']; exact hbody.consistent₀
  · rw [hctxAfter']; exact hbody.consistent₁
  · rw [hctxAfter']; exact hbody.agree
  · rw [hctxAfter', ho₀, hqt]
    exact builtinMax10_call_valueConsistent (entry := entry₀) (pc := pc)
      (poison := res.qualType.poison) (innerArgQt := innerArgQt) hric₀ hcons₀
  · rw [hctxAfter', ho₁, hqt]
    have hvc := builtinMax10_call_valueConsistent (entry := entry₁) (pc := pc)
      (poison := res.qualType.poison) (innerArgQt := innerArgQt) hric₁B hcons₁B
    rw [hctx₁] at hvc; exact hvc
  · rw [hctxAfter']
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hpc_clean : pc = false := hpcclean hpoison
        have htcl : PFnTClosure.extern 11 "b" builtinMax11RetSpec
            (VarTypeEnv.toCaptured ctx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩] ∈
            [PFnTClosure.extern 11 "b" builtinMax11RetSpec
              (VarTypeEnv.toCaptured ctx.varEnv) innerArgQt [⟨CaptureTarget.bareVar "a", Typ.int, false, SyntaxPredicate.noPred⟩]] := by simp
        have hclean_internal : internalPoisonClean res.qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime entry₀.bodyConfig.memory
            entry₁.bodyConfig.memory θ₀ θ₁ (VarTypeEnv.toCaptured ctx.varEnv)
            entry₀.unifiedEnv entry₁.unifiedEnv :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx entry₀.bodyConfig.memory
            entry₁.bodyConfig.memory entry₀.unifiedEnv entry₁.unifiedEnv θ₀ θ₁ hric₀ hric₁ hbody.agree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime entry₀.bodyConfig.memory
            (VarTypeEnv.toCaptured ctx.varEnv) entry₀.unifiedEnv :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := entry₀.bodyConfig.memory) (ρ := entry₀.unifiedEnv) (θ := θ₀) hcons₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime entry₁.bodyConfig.memory
            (VarTypeEnv.toCaptured ctx.varEnv) entry₁.unifiedEnv :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := entry₁.bodyConfig.memory) (ρ := entry₁.unifiedEnv) (θ := θ₁) hcons₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime entry₀.bodyConfig.memory θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) entry₀.unifiedEnv :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := entry₀.bodyConfig.memory) (ρ := entry₀.unifiedEnv) (θ := θ₀) hcons₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime entry₁.bodyConfig.memory θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) entry₁.unifiedEnv :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := entry₁.bodyConfig.memory) (ρ := entry₁.unifiedEnv) (θ := θ₁) hcons₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv)
            entry₀.unifiedEnv :=
          capturedVarsTypingProperty_of_toCaptured ctx entry₀.bodyConfig.memory entry₀.unifiedEnv θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv)
            entry₁.unifiedEnv :=
          capturedVarsTypingProperty_of_toCaptured ctx entry₁.bodyConfig.memory entry₁.unifiedEnv θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := innerArgQt)
          (ρcap₁ := entry₀.unifiedEnv) (ρcap₂ := entry₁.unifiedEnv) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        simp [qtypGuardTag, hpred] at htag

/-- The complete trusted-extern-entry boundary contract for the outer curried-`max`
    extern (`@10`): all five `ExternBoundarySpec` fields.  This is the first
    *nested-returning* trusted entry — its call returns the inner `@11` pure
    closure rather than a base value. -/
theorem builtinMax10Spec : ExternBoundarySpec builtinMax10Decl builtinMax10Impl where
  declFR := builtinMax10_declFR
  callFR := builtinMax10_callFR
  declSingle := builtinMax10_declSingle
  callSingle := builtinMax10_callSingle
  operational := builtinMax10Impl_operationalSafe

/-! ## Interpreter-registry agreement

The interpreter ships `defaultRegistry` (`LeanPoison.ExternBuiltins`).  These
build-checked lemmas confirm that it resolves `@10`/`@11`/`@12` to *exactly* the
trusted impls (`builtinMax10Impl`, `builtinMax11Impl`, `builtinAbsImpl`) that the
boundary specs above are proved about.  Together with the definitional identity
`builtinMax10Impl = .pfn outerMaxImpl` (the interpreter's own `outerMaxImpl`),
this closes the gap between "the running interpreter" and "the proof-side trusted
entries": they reference the *same* runtime functions, not textually-equal
copies. -/

theorem defaultRegistry_lookup_max10 :
    defaultRegistry.get? 10 = some builtinMax10Impl := by
  simp [defaultRegistry, defaultInitialState, regInsert, register, builtinMax10Impl,
    Std.HashMap.getElem_insert, Std.HashMap.contains_insert, Std.HashMap.contains_empty]

theorem defaultRegistry_lookup_max11 :
    defaultRegistry.get? 11 = some builtinMax11Impl := by
  simp [defaultRegistry, defaultInitialState, regInsert, register, builtinMax11Impl,
    Std.HashMap.getElem_insert, Std.HashMap.contains_insert, Std.HashMap.contains_empty]

theorem defaultRegistry_lookup_abs :
    defaultRegistry.get? 12 = some builtinAbsImpl := by
  simp [defaultRegistry, defaultInitialState, regInsert, register, builtinAbsImpl,
    Std.HashMap.getElem_insert, Std.HashMap.contains_insert, Std.HashMap.contains_empty]

/-! ## Memory-read (`!r`) read dependencies

The `memVar` capture target (`!r`) names a *memory cell* reached through a
reference variable, rather than an environment entry.  The trusted artifact
below (`builtinMemDeref*`) is the explicit-clean-reference-argument form: an
extern `@23 r : (ref int :> clean {}) -> (int :> clean {})` that dereferences
its reference argument and returns the cell contents, with
`captures: { !r :> (int :> clean {}) }` declaring that memory read. This is the
representative explicit-reference-argument memory dependency used by `@23`.

Two cleanness facts cooperate at the call boundary, and *both* are load-bearing:

  * the **argument condition** `(ref int :> clean {})` forces the reference clean,
    so both runs realise `r` to a *common* logical location `l`
    (`agreeValueUnder.clean_ref` produces the shared `l ∈ ls`); and
  * the **capture** `!r :> (int :> clean {})` forces the *cell contents* at `l`
    clean, so the two memory reads agree (`agreeOnClean` on the location side,
    `agreeLocUnder.agree_values`).

A clean reference may still point to a poisoned cell, so the capture is not
implied by the argument condition — it is exactly the extra fact memory-read
read-dependencies contribute to fault-robustness. -/

/-- `List.foldl (· && g ·)` over a list yields `true` only when the initial
    accumulator is `true` and every element satisfies `g`. -/
private theorem list_foldl_and_forall {α : Type} {g : α → Bool} :
    ∀ {xs : List α} {b : Bool},
      List.foldl (fun acc l => acc && g l) b xs = true →
      b = true ∧ ∀ l, l ∈ xs → g l = true := by
  intro xs
  induction xs with
  | nil => intro b h; exact ⟨h, by intro l hl; cases hl⟩
  | cons x xs ih =>
      intro b h
      simp only [List.foldl_cons] at h
      obtain ⟨hbx, hrest⟩ := ih h
      rw [Bool.and_eq_true] at hbx
      refine ⟨hbx.1, ?_⟩
      intro l hl
      rcases List.mem_cons.mp hl with rfl | htail
      · exact hbx.2
      · exact hrest l htail

/-- A `LocSet.fold` with `&&` succeeds only when every member of the set
    satisfies the folded predicate.  This is the membership reading of the
    `memVar` call gate's per-cell fold. -/
private theorem locset_fold_and_forall {g : Loc → Bool} {ls : LocSet}
    (h : LocSet.fold ls true (fun acc l => acc && g l) = true) :
    ∀ l, l ∈ ls → g l = true := by
  unfold LocSet.fold at h
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at h
  intro l hl
  exact (list_foldl_and_forall h).2 l (by simpa using hl)

/-- Gate-extraction for a singleton *memory-read* `captures:` dependency
    `[⟨!v, ty, clean, noPred⟩]`: the dependency target resolves in the callable
    environment to a *reference* type `ref ls`, and every cell in `ls` resolves
    in the current memory typing to a qualified type that is clean under the
    regime.  The call boundary instantiates this at the single logical location
    that the runtime reference realises (the one supplied by
    `agreeValueUnder.clean_ref`). -/
private theorem capturesSatisfied_singleton_memVar
    {v : Name} {ty : Typ} {u : VarTypeEnv} {m : MemoryTypeEnv} {r : Regime}
    (h : capturesSatisfied
        [⟨CaptureTarget.memVar v, ty, false, SyntaxPredicate.noPred⟩] u m r = true) :
    ∃ ls : LocSet, (∃ qt : QTyp, u.lookup v = some qt ∧ qt.etyp = ETyp.ref ls) ∧
      ∀ l, l ∈ ls → ∃ cellQt : QTyp,
        m.lookup l = some cellQt ∧ qtypCleanUnderRegime cellQt r = true := by
  simp only [capturesSatisfied, List.all_cons, List.all_nil, Bool.and_true,
    captureSatisfied] at h
  cases hlk : u.lookup v with
  | none => simp [hlk] at h
  | some qt =>
      simp only [hlk] at h
      cases het : qt.etyp with
      | ref ls =>
          simp only [het] at h
          refine ⟨ls, ⟨qt, rfl, het⟩, ?_⟩
          intro l hl
          have hg := locset_fold_and_forall h l hl
          cases hcl : m.lookup l with
          | none => simp [hcl] at hg
          | some cellQt =>
              simp only [hcl] at hg
              simp only [captureCondSatisfied, Bool.and_eq_true] at hg
              exact ⟨cellQt, rfl, by simpa using hg.1.2⟩
      | int => simp [het] at h
      | bool => simp [het] at h
      | unit => simp [het] at h
      | string => simp [het] at h
      | arrow _ _ _ _ => simp [het] at h
      | parrow _ _ _ _ => simp [het] at h

/-! ### Trusted memory-read extern `@23` (the `!r` read-dependency demonstrator)

`builtinMemDerefDecl` is `@23 r : (ref int :> clean {}) -> (int :> clean {})`
with `captures: { !r :> (int :> clean {}) }`.  Its implementation
(`memDerefImpl`) dereferences the reference argument and returns the cell
contents.  The relational `callFR` is the new content: it composes the argument
condition (reference clean ⇒ a *common* logical cell via
`agreeValueUnder_ref_common_loc`) with the `!r` capture (cell contents clean ⇒
the two reads agree via `agreeOnClean` on the location side).  The four
non-relational fields mirror the captures-`[]`/`[a]` machinery; the only
declaration-level novelty is the reference-typed argument
(`argTypToETyp (ref int) = ETyp.ref ∅`, a signature placeholder compared
modulo locset). -/

def builtinMemDerefRetSpec : ExternReturn :=
  .simple .int false .noPred

/-- Proof-side declaration for the memory-read extern (`@23`): a pfn taking a
    `ref int` argument, declaring a `!r` read dependency on the cell behind it. -/
def builtinMemDerefDecl : ExternDeclaration :=
  { id := 23
    kind := .pfn
    typ := Typ.ref Typ.int
    argName := some "r"
    retSpec := some builtinMemDerefRetSpec
    effects := []
    preds := collectExternPreds builtinMemDerefRetSpec []
    argPoison := false
    captures := [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩] }

def builtinMemDerefImpl : ExternImpl :=
  .pfn memDerefImpl

/-- Output shape of a successful `memDerefImpl` dispatch: the argument is a
    `Value.loc`, the memory cell behind it holds `n`, and the result is
    `Value.num n`. -/
private theorem memDerefImpl_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : memDerefImpl env vArg mem = .ok vRaw) :
    ∃ (addr : Address) (n : Int), vArg = Value.loc addr ∧
      Memory.lookup mem addr = some n ∧ vRaw = Value.num n := by
  cases vArg with
  | loc addr =>
      simp only [memDerefImpl] at h
      cases hcl : Memory.lookup mem addr with
      | none => rw [hcl] at h; simp at h
      | some n =>
          rw [hcl] at h
          simp only [Except.ok.injEq] at h
          exact ⟨addr, n, rfl, hcl, h.symm⟩
  | _ => simp [memDerefImpl] at h

/-! #### `@23` declaration-boundary fields (mirror of the captures-`[a]` machinery) -/

private def builtinMemDerefExternClosure (ctx : TypeContext) (argQt : QTyp) : PFnTClosure :=
  PFnTClosure.extern 23 "r" builtinMemDerefRetSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt
    [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩]

private def builtinMemDerefDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.parrow (Typ.ref Typ.int) (parseReturnType builtinMemDerefRetSpec) ctx.pc
        [builtinMemDerefExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

private theorem builtinMemDeref_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMemDerefDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinMemDerefDeclResult ctx argQt := by
  cases htyped with
  | pfn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcPfn :
              typecheckExternPfn ctx 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec
                [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 23 "r" (Typ.ref Typ.int) false argPred
              builtinMemDerefRetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMemDeref_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMemDerefDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures := by
  cases htyped with
  | pfn _htc => exact ⟨_, _, rfl⟩

private theorem builtinMemDeref_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "r" (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures) ρ)
      (builtinMemDerefDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "r" (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures) ρ)
      (ETyp.parrow (Typ.ref Typ.int) (parseReturnType builtinMemDerefRetSpec) ctx.pc
        [builtinMemDerefExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩])
      (htcl := by simp [builtinMemDerefExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

private theorem builtinMemDeref_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMemDerefDeclResult ctx argQt).qualType μ θ
      (Value.peClosure "r" (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMemDerefDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt)
      (memberCap := [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩])
      23 "r" "r" (Typ.ref Typ.int) builtinMemDerefRetSpec ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinMemDerefExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinMemDerefExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

private theorem builtinMemDeref_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinMemDerefDecl builtinMemDerefImpl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.peClosure "r" (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMemDerefDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinMemDerefDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMemDerefDecl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "r" := by
        have h := hargName; simp [builtinMemDerefDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMemDerefRetSpec := by
        have h := hretSpec; simp [builtinMemDerefDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinMemDerefDecl] using hval⟩

theorem builtinMemDeref_declSingle :
    ExternDeclBoundarySingle builtinMemDerefDecl builtinMemDerefImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMemDeref_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinMemDeref_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMemDerefDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 23 "r" (Typ.ref Typ.int)
      (parseReturnType builtinMemDerefRetSpec) ctx.pc builtinMemDerefRetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "r"
      (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPred builtinMemDerefRetSpec captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinMemDeref_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinMemDeref_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

theorem builtinMemDeref_declFR :
    ExternDeclBoundaryFR builtinMemDerefDecl builtinMemDerefImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMemDeref_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinMemDeref_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMemDeref_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMemDeref_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "r"
      (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPredT builtinMemDerefRetSpec capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "r"
      (Expr.externPfn 23 "r" (Typ.ref Typ.int) false argPredT builtinMemDerefRetSpec capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by
    rw [hres]; simp [ctxAfter, builtinMemDerefDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 23 "r" (Typ.ref Typ.int)
      (parseReturnType builtinMemDerefRetSpec) ctx.pc builtinMemDerefRetSpec (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinMemDeref_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinMemDeref_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinMemDeref_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinMemDeref_decl_valueConsistent hric₁ hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinMemDerefDeclResult ctx argQt).qualType.etyp =
            ETyp.parrow (Typ.ref Typ.int) (parseReturnType builtinMemDerefRetSpec) ctx.pc
              [builtinMemDerefExternClosure ctx argQt] := rfl
        have htcl : builtinMemDerefExternClosure ctx argQt ∈
            [builtinMemDerefExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinMemDerefDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinMemDerefDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinMemDerefDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_parrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinMemDerefDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinMemDerefDeclResult]
        simp [hnone] at htag

/-! #### `@23` call-boundary fields — the memory-read `callFR` -/

/-- Output of a successful `@23` call: the argument is a `Value.loc addr`, the
    cell behind it holds `n` in the call-config memory, the result is
    `Value.num n`, and the config is unchanged. -/
private theorem builtinMemDeref_call_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hfacts : ExternCallPfnFacts builtinMemDerefDecl builtinMemDerefImpl entry res cf o) :
    ∃ (addr : Address) (n : Int), entry.argValue = Value.loc addr ∧
      Memory.lookup entry.callConfig.memory addr = some n ∧
      o = Value.num n ∧ cf = entry.callConfig := by
  rcases hfacts.impl_success with
    ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrun, hvalRet⟩
  simp only [builtinMemDerefImpl, ExternImpl.pfn.injEq] at himpl
  subst himpl
  have hret : retSpec = builtinMemDerefRetSpec := by
    simp only [builtinMemDerefDecl] at hretSpec
    exact (Option.some.inj hretSpec).symm
  subst hret
  obtain ⟨addr, n, harg, hlk, hraw⟩ := memDerefImpl_ok_shape hrun
  refine ⟨addr, n, harg, hlk, ?_, hfacts.output_config⟩
  rw [hraw] at hvalRet
  simp only [builtinMemDerefRetSpec, validateExternReturn, valueMatchesTyp,
    if_true, Except.ok.injEq] at hvalRet
  exact hvalRet.symm

private theorem builtinMemDeref_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMemDerefDecl builtinMemDerefImpl entry res cf o) :
    ∃ (addr : Address) (n : Int), entry.argValue = Value.loc addr ∧
      Memory.lookup entry.callConfig.memory addr = some n ∧
      o = Value.num n ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMemDerefDecl] at h
  | pfn hfacts => exact builtinMemDeref_call_output hfacts

/-- The body-entry environment of a successful `@23` call binds the reference
    argument name `"r"` to the runtime argument value. -/
private theorem builtinMemDeref_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinMemDerefDecl builtinMemDerefImpl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "r" = some entry.argValue := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMemDerefDecl] at h
  | pfn hfacts =>
      have hargName : entry.argName = "r" := by
        have h := hfacts.argName; simp only [builtinMemDerefDecl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- Shared structure from a `@23` call typing witness: clean integer result, post
    context equals body context, and — crucially — the reference argument `"r"`
    resolves clean (the argument gate) to a `ref ls` whose every cell is clean
    under the body regime (the `!r` capture gate). -/
private theorem builtinMemDeref_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinMemDerefDecl typedExpr entry res) :
    res.qualType.etyp = ETyp.int ∧
      res.qualType.pred = Predicate.noPred ∧
      ctxAfter entry.bodyCtx res = entry.bodyCtx ∧
      (∃ (rQt : QTyp) (ls : LocSet),
        entry.bodyCtx.varEnv.lookup "r" = some rQt ∧
        rQt.etyp = ETyp.ref ls ∧
        qtypCleanUnderRegime rQt entry.bodyCtx.regime = true ∧
        ∀ l, l ∈ ls → ∃ cellQt : QTyp,
          entry.bodyCtx.memEnv.lookup l = some cellQt ∧
          qtypCleanUnderRegime cellQt entry.bodyCtx.regime = true) := by
  cases htyped with
  | fnExternMember _ hkind _ _ _ _ _ _ _ => simp [builtinMemDerefDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv
      have hcap' : captures =
          [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩] := by
        simpa [builtinMemDerefDecl] using hcap.symm
      subst hcap'
      have hx : x = "r" := by
        have : some x = some "r" := by simpa [builtinMemDerefDecl] using harg.symm
        exact Option.some.inj this
      subst hx
      have hretSpec : retSpec = ExternReturn.simple Typ.int false SyntaxPredicate.noPred := by
        have : some retSpec = some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) := by
          simpa [builtinMemDerefDecl, builtinMemDerefRetSpec] using hret.symm
        exact Option.some.inj this
      subst retSpec
      have hpin' : declaredArgQt.poison = false := by simpa [builtinMemDerefDecl] using hpin
      cases fuel with
      | zero => simp [applyPFnTClosureAtCursor] at happly
      | succ fuel' =>
          have hcollect := collectAndAllocExternTags_noPred cursor.1
          simp only [applyPFnTClosureAtCursor, hcollect, resolveSyntaxPred, returnSpecToQTyp,
            bind, Except.bind, pure, Except.pure] at happly
          split at happly
          · simp at happly
          rename_i hgate
          rw [Bool.not_eq_true, Bool.not_eq_false'] at hgate
          rw [Bool.and_eq_true] at hgate
          obtain ⟨hcondArg, hcapGate⟩ := hgate
          have hargClean : qtypCleanUnderRegime ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩
              bodyState.regime' = true :=
            argConditionSatisfied_cleanRegime_of_declClean hcondArg hpin'
          obtain ⟨ls, ⟨lemQt, hlemLk, hlemEt⟩, hcells⟩ :=
            capturesSatisfied_singleton_memVar hcapGate
          have hfront : (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) "r"
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩).lookup "r"
              = some ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            VarTypeEnv_lookup_update_eq _ "r" _
          have hlemEq : lemQt = ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ :=
            Option.some.inj (hlemLk.symm.trans hfront)
          simp only [Except.ok.injEq] at happly
          subst res
          refine ⟨?_, ?_, ?_,
            ⟨⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ls, ?_, ?_, ?_, ?_⟩⟩
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · by_cases hprov : joinPoison p1 p = true <;>
              simp [normalizeAppResultByProvenance, hprov]
          · rw [hbody]; simp only [ctxAfter, applyExternRegimePolicy]; rfl
          · rw [hbody]; exact hfront
          · rw [hlemEq] at hlemEt; exact hlemEt
          · rw [hbody]; exact hargClean
          · intro l hl
            rw [hbody]
            exact hcells l hl

/-- Deref-value equality across the two runs: the reference argument is clean
    (a common logical cell `l`), the `!r` capture forces that cell's contents
    clean, so `agreeOnClean` on the location side forces the two integer reads
    equal. -/
private theorem builtinMemDeref_callRun_nEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinMemDerefDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinMemDerefDecl builtinMemDerefImpl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinMemDerefDecl builtinMemDerefImpl entry₁ res cf₁ o₁)
    {addr₀ addr₁ : Address} {n₀ n₁ : Int}
    (harg₀ : entry₀.argValue = Value.loc addr₀)
    (harg₁ : entry₁.argValue = Value.loc addr₁)
    (hlk₀ : Memory.lookup entry₀.callConfig.memory addr₀ = some n₀)
    (hlk₁ : Memory.lookup entry₁.callConfig.memory addr₁ = some n₁) :
    n₀ = n₁ := by
  obtain ⟨_, _, _, rQt, ls, hbindR, hetypR, hcleanR, hcells⟩ :=
    builtinMemDeref_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "r" = some (Value.loc addr₀) := by
    rw [builtinMemDeref_callRun_bodyVar hrun₀, harg₀]
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "r" = some (Value.loc addr₁) := by
    rw [builtinMemDeref_callRun_bodyVar hrun₁, harg₁]
  have hnotfun : rQt.etyp.isFunctionType = false := by rw [hetypR]; rfl
  have hcleanRP : qtypCleanUnder entry₀.bodyCtx.regime rQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanR hnotfun
  have hvar := hbody.agree.2 "r" rQt hbindR hcleanRP
  cases hvar with
  | both_none _x _qt hl0 _hl1 => rw [hrv₀] at hl0; exact absurd hl0 (by simp)
  | agree_values _x _qt v₀ v₁ hl0 hl1 hval =>
      have e0 : v₀ = Value.loc addr₀ := Option.some.inj (hl0.symm.trans hrv₀)
      have e1 : v₁ = Value.loc addr₁ := Option.some.inj (hl1.symm.trans hrv₁)
      subst e0; subst e1
      obtain ⟨l, hlin, hθ0, hθ1⟩ := agreeValueUnder_ref_common_loc hetypR hval
      obtain ⟨cellQt, hcellLk, hcellClean⟩ := hcells l hlin
      have hcellInt : cellQt.etyp = ETyp.int :=
        memEnv_lookup_etyp_int entry₀.bodyCtx.memEnv l cellQt hcellLk
      have hcellCleanP : qtypCleanUnder entry₀.bodyCtx.regime cellQt :=
        qtypCleanUnder_of_cleanUnderRegime hcellClean (by rw [hcellInt]; rfl)
      have hloc := hbody.agree.1 l cellQt hcellLk hcellCleanP
      have hbcmem₀ : entry₀.bodyConfig.memory = entry₀.callConfig.memory := by
        simp [ExternCallEntry.bodyConfig]
      have hbcmem₁ : entry₁.bodyConfig.memory = entry₁.callConfig.memory := by
        simp [ExternCallEntry.bodyConfig]
      cases hloc with
      | both_unrealized _l _qt hnone0 _hnone1 => rw [hθ0] at hnone0; exact absurd hnone0 (by simp)
      | agree_values _l _qt a₀' a₁' m₀ m₁ hr0 hr1 hm0 hm1 hmagree =>
          have ha0 : a₀' = addr₀ := Option.some.inj (hr0.symm.trans hθ0)
          have ha1 : a₁' = addr₁ := Option.some.inj (hr1.symm.trans hθ1)
          have e0 : entry₀.bodyConfig.memory.lookup a₀' = some n₀ := by
            rw [ha0, hbcmem₀]; exact hlk₀
          have e1 : entry₁.bodyConfig.memory.lookup a₁' = some n₁ := by
            rw [ha1, hbcmem₁]; exact hlk₁
          have hn0 : m₀ = n₀ := Option.some.inj (hm0.symm.trans e0)
          have hn1 : m₁ = n₁ := Option.some.inj (hm1.symm.trans e1)
          have hmeq : m₀ = m₁ := agreeValueUnder_num_int_imp_eq hcellInt hmagree
          rw [← hn0, ← hn1]; exact hmeq

theorem builtinMemDeref_callFR :
    ExternCallBoundaryFR builtinMemDerefDecl builtinMemDerefImpl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨hetyp, hpred, hctxAfter, _⟩ := builtinMemDeref_call_clean_shape htyped₀
  obtain ⟨addr₀, n₀, harg₀, hlk₀, ho₀, hcf₀⟩ := builtinMemDeref_callRun_output hrun₀
  obtain ⟨addr₁, n₁, harg₁, hlk₁, ho₁, hcf₁⟩ := builtinMemDeref_callRun_output hrun₁
  have hneq : n₀ = n₁ :=
    builtinMemDeref_callRun_nEq htyped₀ hbody hrun₀ hrun₁ harg₀ harg₁ hlk₀ hlk₁
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hvc : ∀ (μ : Memory) (θ : RealizationMap) (n : Int),
      valueConsistentWithRegime predSat ctx.regime res.qualType μ θ (Value.num n) := by
    intro μ θ n
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num n) (by rw [hetyp]; rfl)
  rw [hboc₀, hboc₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hd_res]; exact hbody.reserved₀), (by rw [hd_res]; exact hbody.reserved₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho₀, hetyp]; exact valueHasETyp.num _
  · rw [ho₁, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter']; exact hwfTm
  · rw [hctxAfter']; exact hbody.wfCtx
  · rw [hctxAfter']; exact hbody.tagBounded
  · exact hbody.wfConfig₀
  · exact hbody.wfConfig₁
  · rw [hctxAfter']; exact hbody.runtime₀
  · rw [hctxAfter']; exact hbody.runtime₁
  · rw [hctxAfter']; exact hbody.regime
  · rw [hctxAfter']; exact hbody.consistent₀
  · rw [hctxAfter']; exact hbody.consistent₁
  · rw [hctxAfter']; exact hbody.agree
  · rw [hctxAfter', ho₀]; exact hvc _ _ _
  · rw [hctxAfter', ho₁]; exact hvc _ _ _
  · rw [hctxAfter', ho₀, ho₁]
    exact resultAgreesIfClean_int_noPred_of_eq hetyp hpred (by rw [hneq])

theorem builtinMemDeref_callSingle :
    ExternCallBoundarySingle builtinMemDerefDecl builtinMemDerefImpl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrdIn hrun _hpc
  obtain ⟨hetyp, hpred, hctxAfter, _⟩ := builtinMemDeref_call_clean_shape htyped
  obtain ⟨addr, n, _harg, _hlk, ho, hcf⟩ := builtinMemDeref_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hctxAfter' : ctxAfter ctx res = ctx := hctxAfter
  have hnt : res.nextTag' = ctx.nextTag := by
    have h := congrArg TypeContext.nextTag hctxAfter'; simpa [ctxAfter] using h
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter'
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hboc, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter']; exact hwfTm
  · rw [ho, hetyp]; exact valueHasETyp.num _
  · rw [hctxAfter', hboc]; exact hric
  · rw [hctxAfter', hboc]; exact hcons
  · rw [hboc, ho]
    refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred]) ?_
    exact closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by rw [hetyp]; exact valueHasETyp.num _) (by rw [hetyp]; rfl)
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter'

theorem builtinMemDerefImpl_operationalSafe :
    ExternOperationalSafe builtinMemDerefDecl builtinMemDerefImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMemDerefImpl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinMemDerefImpl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨addr, n, _harg, _hlk, hraw⟩ := memDerefImpl_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · intro v himpl _ _
    simp [builtinMemDerefImpl] at himpl
  · intro implFn himpl
    simp [builtinMemDerefImpl] at himpl

/-- The complete trusted-extern-entry boundary contract for the memory-read
    extern (`@23`, captures `[!r]`): all five `ExternBoundarySpec` fields.  The
    relational `callFR` is the crux (`builtinMemDeref_callFR`), composing the
    reference-clean argument condition with the cell-clean `!r` capture. -/
theorem builtinMemDerefSpec :
    ExternBoundarySpec builtinMemDerefDecl builtinMemDerefImpl where
  declFR := builtinMemDeref_declFR
  callFR := builtinMemDeref_callFR
  declSingle := builtinMemDeref_declSingle
  callSingle := builtinMemDeref_callSingle
  operational := builtinMemDerefImpl_operationalSafe

/-- The interpreter's assembled `defaultRegistry` resolves `@23` to exactly the
    memory-read implementation `memDerefImpl` that the trusted boundary spec
    `builtinMemDerefSpec` validates (`builtinMemDerefImpl ≡ .pfn memDerefImpl`
    definitionally).  Function-level interpreter↔proof agreement for the
    memory-read extern, mirroring `defaultRegistry_lookup_max11`. -/
theorem defaultRegistry_lookup_memderef :
    defaultRegistry.get? 23 = some builtinMemDerefImpl := by
  simp [defaultRegistry, defaultInitialState, regInsert, register, builtinMemDerefImpl,
    Std.HashMap.contains_insert, Std.HashMap.contains_empty]

/-- A value found in a well-formed environment is itself well formed.  (Local
    copy of the `private` `SemanticsProperties.wfVarEnv_lookup`, needed here to
    bound the location `set_err` resolves from `errno`.) -/
private theorem wfVarEnv_lookup_loc
    {n : Address} {env : VarEnv} {x : Name} {v : Value}
    (h_wf_env : wfVarEnv n env) (h_lookup : VarEnv.lookup env x = some v) :
    wfValue n v := by
  induction env with
  | nil => simp [VarEnv.lookup, List.lookup] at h_lookup
  | cons head tail ih =>
      cases head with
      | mk x' v' =>
          cases h_wf_env with
          | cons _ _ _ h_wf_v' h_wf_tail =>
              simp [VarEnv.lookup, List.lookup] at h_lookup
              by_cases h_eq : x == x'
              · simp [h_eq] at h_lookup
                subst h_lookup
                exact h_wf_v'
              · simp [h_eq] at h_lookup
                exact ih h_wf_tail h_lookup

/-- Operational safety of `setErrImpl` (`@22`), the `set_err` impure extern —
    the `fn`-clause content of `ExternOperationalSafe`, and the key Path-2 payoff.

    Because `set_err` writes the location it resolves from the captured `errno`
    binding (rather than a fixed reserved address), its well-formedness obligation
    discharges *directly* from the `wfVarEnv addr env` hypothesis the boundary
    already supplies: the resolved cell `a` satisfies `a < addr` because
    `(errno, Value.loc a)` lives in the well-formed environment.  No
    reserved-address invariant and no fold of `RegistryReservedBelow` into
    `wfConfig` are required.  The call neither allocates (`addr' = addr`, so
    `addr ≤ addr'`) nor writes out of bounds, and returns a trivially well-formed
    `unit`. -/
theorem setErrImpl_operational
    (env : VarEnv) (vArg : Value) (mem : Memory) (addr : Address)
    (vRaw : Value) (mem' : Memory) (addr' : Address)
    (hImpl : setErrImpl env vArg mem addr = .ok (vRaw, mem', addr')) :
    addr ≤ addr' ∧
    ((∀ a, mem.contains a → a < addr) →
      wfVarEnv addr env →
      wfValue addr vArg →
      (∀ a, mem'.contains a → a < addr') ∧ wfValue addr' vRaw) := by
  cases vArg with
  | num n =>
    cases hlook : VarEnv.lookup env "errno" with
    | none => simp [setErrImpl, hlook] at hImpl
    | some w =>
      cases w with
      | loc a =>
        simp only [setErrImpl, hlook, Except.ok.injEq, Prod.mk.injEq] at hImpl
        obtain ⟨rfl, rfl, rfl⟩ := hImpl
        refine ⟨Nat.le_refl _, fun hmem hwfenv _ => ?_⟩
        have ha_lt : a < addr := by
          have hw := wfVarEnv_lookup_loc hwfenv hlook
          cases hw with | loc h => exact h
        refine ⟨fun a' hc' => ?_, wfValue.unit⟩
        by_cases h_eq : a' = a
        · subst h_eq; exact ha_lt
        · have hcmp : compare a a' ≠ Ordering.eq :=
            fun hc => h_eq (LawfulEqCmp.eq_of_compare hc).symm
          exact hmem a' (by
            simpa [Memory.update] using
              ExtTreeMap.contains_of_contains_insert
                (t := mem) (k := a) (a := a') (v := n) hc' hcmp)
      | num _ => simp [setErrImpl, hlook] at hImpl
      | bool _ => simp [setErrImpl, hlook] at hImpl
      | unit => simp [setErrImpl, hlook] at hImpl
      | str _ => simp [setErrImpl, hlook] at hImpl
      | closure _ _ _ => simp [setErrImpl, hlook] at hImpl
      | peClosure _ _ _ => simp [setErrImpl, hlook] at hImpl
  | bool _ => simp [setErrImpl] at hImpl
  | unit => simp [setErrImpl] at hImpl
  | str _ => simp [setErrImpl] at hImpl
  | loc _ => simp [setErrImpl] at hImpl
  | closure _ _ _ => simp [setErrImpl] at hImpl
  | peClosure _ _ _ => simp [setErrImpl] at hImpl

/-! ### `@22` (`set_err`) runtime shape lemmas

Reusable inversions of a successful `setErrImpl` dispatch, the `@22`
write-effect target resolution, and the non-shadowing of the captured `errno`
target by the argument binding.  These feed the `@22` `callSingle` / `callFR`
boundary fields. -/

/-- Output shape of a successful `setErrImpl` (`@22`) dispatch: the argument is a
    `Value.num n`, the runtime environment resolves `errno` to a location `a`, the
    result is `Value.unit`, the cell at `a` is overwritten with `n`, and the
    address cursor is threaded through unchanged. -/
private theorem setErrImpl_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {next : Address}
    {vRaw : Value} {mem' : Memory} {next' : Address}
    (h : setErrImpl env vArg mem next = .ok (vRaw, mem', next')) :
    ∃ (n : Int) (a : Address),
      vArg = Value.num n ∧
      VarEnv.lookup env "errno" = some (Value.loc a) ∧
      vRaw = Value.unit ∧
      mem' = Memory.update mem a n ∧
      next' = next := by
  cases vArg with
  | num n =>
    cases hlook : VarEnv.lookup env "errno" with
    | none => simp [setErrImpl, hlook] at h
    | some w =>
      cases w with
      | loc a =>
        simp only [setErrImpl, hlook, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨n, a, rfl, rfl, rfl, rfl, rfl⟩
      | num _ => simp [setErrImpl, hlook] at h
      | bool _ => simp [setErrImpl, hlook] at h
      | unit => simp [setErrImpl, hlook] at h
      | str _ => simp [setErrImpl, hlook] at h
      | closure _ _ _ => simp [setErrImpl, hlook] at h
      | peClosure _ _ _ => simp [setErrImpl, hlook] at h
  | bool _ => simp [setErrImpl] at h
  | unit => simp [setErrImpl] at h
  | str _ => simp [setErrImpl] at h
  | loc _ => simp [setErrImpl] at h
  | closure _ _ _ => simp [setErrImpl] at h
  | peClosure _ _ _ => simp [setErrImpl] at h

/-- The cell `setErrImpl` writes is below the address cursor: from
    `wfVarEnv addr env` and the resolved `errno` binding `Value.loc a`, `a < addr`. -/
private theorem setErrImpl_errno_target_wf
    {env : VarEnv} {a : Address} {addr : Address}
    (hwf : wfVarEnv addr env)
    (hlook : VarEnv.lookup env "errno" = some (Value.loc a)) :
    a < addr := by
  have hw := wfVarEnv_lookup_loc hwf hlook
  cases hw with | loc h => exact h

/-- Non-shadowing of the captured `errno` target by the argument binding:
    extending the captured environment with the `@22` argument (any name other
    than `errno`) leaves the resolved `errno` target unchanged.  For `@22` the
    argument name is `n`, so `n ≠ errno` discharges the hypothesis. -/
private theorem setErrImpl_errno_lookup_captured
    (capturedEnv : VarEnv) (argName : Name) (argVal : Value)
    (hne : argName ≠ "errno") :
    VarEnv.lookup (VarEnv.update capturedEnv argName argVal) "errno"
      = VarEnv.lookup capturedEnv "errno" :=
  VarEnv_lookup_update_ne capturedEnv argName "errno" argVal (Ne.symm hne)

/-- The synthetic body-output config of a `@22` dispatch keeps the runtime result
    config `cf` (its memory and address cursor) and rebinds the variable
    environment to the call's unified environment. -/
private theorem setErrImpl_bodyOutputConfig (entry : ExternCallEntry) (cf : Config) :
    entry.bodyOutputConfig cf = { cf with varEnv := entry.unifiedEnv } := rfl

/-- Type-side mirror of `setErrImpl_ok_shape`: invert a successful type-level
    effect application.  A `!v`-targeted effect resolves `v` in the unified type
    environment to a reference type `ref ls`, the syntactic effect predicate
    resolves, and the resulting `memEnv'` is the assignment-shaped update of `ls`
    (singleton strong / multi-location weak), with the target reference's own
    poison `qt.poison` folded into the stored poison/predicate.  Parameterized
    over the effect, so the `@22` clean-singleton `!errno` instantiation is a
    later specialization. -/
private theorem applyExternEffect_errno_shape
    {effect : Effect} {unifiedEnv : VarTypeEnv} {tagMapping : TagMapping}
    {pc : Poison} {memEnv memEnv' : MemoryTypeEnv}
    (h : applyExternEffect effect unifiedEnv tagMapping pc memEnv = .ok memEnv') :
    ∃ (v : Name) (qt : QTyp) (ls : LocSet) (resolvedPred : Predicate),
      effect.target = EffectTarget.namedVar v ∧
      VarTypeEnv.lookup unifiedEnv v = some qt ∧
      qt.etyp = ETyp.ref ls ∧
      resolveSyntaxPred effect.pred unifiedEnv tagMapping = .ok resolvedPred ∧
      memEnv' =
        (match ExtTreeSet.toList ls with
         | [l] => updateMemEnv memEnv l
             ⟨ETyp.int, joinPoison pc (joinPoison qt.poison effect.poison),
              if qt.poison || pc then Predicate.noPred else resolvedPred⟩
         | _ => updateLocsetWeak memEnv ls
             (joinPoison pc (joinPoison qt.poison effect.poison))
             (if qt.poison || pc then Predicate.noPred else resolvedPred)) := by
  unfold applyExternEffect at h
  cases htarget : effect.target with
  | namedVar v =>
    simp only [htarget, bind, Except.bind] at h
    cases hlk : VarTypeEnv.lookup unifiedEnv v with
    | none => simp only [hlk] at h; simp at h
    | some qt =>
      simp only [hlk] at h
      cases hetyp : qt.etyp with
      | ref ls =>
        simp only [hetyp] at h
        cases hres : resolveSyntaxPred effect.pred unifiedEnv tagMapping with
        | error e => simp only [hres] at h; simp at h
        | ok resolvedPred =>
          simp only [hres, pure, Except.pure, Except.ok.injEq, effectSpecToQTyp] at h
          exact ⟨v, qt, ls, resolvedPred, rfl, hlk, hetyp, rfl, h.symm⟩
      | int => simp only [hetyp] at h; simp at h
      | bool => simp only [hetyp] at h; simp at h
      | unit => simp only [hetyp] at h; simp at h
      | string => simp only [hetyp] at h; simp at h
      | arrow _ _ _ _ => simp only [hetyp] at h; simp at h
      | parrow _ _ _ _ => simp only [hetyp] at h; simp at h

/-! ### `@22` (`set_err`) proof-side declaration

Mirrors the interpreter's `regInsert r4 22 (.fn setErrImpl)`
(`LeanPoison.ExternBuiltins`): an impure `fn` extern taking an `int` argument
`n`, returning `unit`, with the single declared effect `!errno :> (int :> clean
{})`.  Authored here (rather than at the spec-assembly step) because the
call-boundary fields are stated against this declaration. -/

/-- Return spec of `@22`: `unit`, clean, no predicate. -/
def builtinSetErrRetSpec : ExternReturn :=
  .simple .unit false .noPred

/-- The single declared write-effect of `@22`: a clean `int` written through the
    captured `errno` reference, with no predicate. -/
def builtinSetErrEffect : Effect :=
  ⟨EffectTarget.namedVar "errno", false, .noPred⟩

/-- Proof-side declaration for the interpreter's built-in `set_err` extern (`@22`). -/
def builtinSetErrDecl : ExternDeclaration :=
  { id := 22
    kind := .fn
    typ := .int
    argName := some "n"
    retSpec := some builtinSetErrRetSpec
    effects := [builtinSetErrEffect]
    preds := collectExternPreds builtinSetErrRetSpec [builtinSetErrEffect]
    argPoison := false }

/-- Runtime implementation shape for `@22`: the interpreter's shared `setErrImpl`,
    so the running interpreter and this proof-side spec reference the same
    function. -/
def builtinSetErrImpl : ExternImpl :=
  .fn setErrImpl

/-- Runtime inversion of a successful `@22` (`set_err`) call boundary run: the
    `.fn` dispatch resolves `errno` to a location `a` in the unified environment,
    returns `unit`, overwrites the cell at `a` with the integer argument, and
    threads the address cursor through unchanged.  The `.pfn` constructor is
    impossible because `builtinSetErrDecl.kind = .fn`. -/
private theorem builtinSetErr_callRun_output
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinSetErrDecl builtinSetErrImpl entry res cf o) :
    ∃ (n : Int) (a : Address),
      entry.argValue = Value.num n ∧
      VarEnv.lookup entry.unifiedEnv "errno" = some (Value.loc a) ∧
      o = Value.unit ∧
      cf.memory = Memory.update entry.callConfig.memory a n ∧
      cf.nextAddr = entry.callConfig.nextAddr ∧
      cf = { entry.callConfig with memory := cf.memory, nextAddr := cf.nextAddr } := by
  cases hrun with
  | fn hfacts =>
      rcases hfacts.impl_success with
        ⟨implFn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrunImpl, hvalRet⟩
      simp only [builtinSetErrImpl, ExternImpl.fn.injEq] at himpl
      subst himpl
      have hret : retSpec = builtinSetErrRetSpec := by
        simp only [builtinSetErrDecl] at hretSpec
        exact (Option.some.inj hretSpec).symm
      subst hret
      obtain ⟨n, a, harg, hlk, hraw, hmem, hnext⟩ := setErrImpl_ok_shape hrunImpl
      refine ⟨n, a, harg, hlk, ?_, hmem, hnext, hfacts.output_config⟩
      rw [hraw] at hvalRet
      simp only [builtinSetErrRetSpec, validateExternReturn, valueMatchesTyp,
        if_true, Except.ok.injEq] at hvalRet
      exact hvalRet.symm
  | pfn hfacts => have h := hfacts.kind_pfn; simp [builtinSetErrDecl] at h

private theorem collectAndAllocExternTags_noPred₂ (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.noPred, SyntaxPredicate.noPred] nextTag
      = .ok ({}, nextTag) := rfl

/-- Typing inversion of a successful `@22` (`set_err`) call boundary witness:
    the result is `unit`/`noPred`, the tag environment and regime are unchanged
    (the `noPred` effect/return allocate no tags), and `res.memEnv'` is the output
    of the single `!errno` effect applied to the body-context memory environment
    under the body program counter. -/
private theorem builtinSetErr_call_clean_shape
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call builtinSetErrDecl typedExpr entry res) :
    res.qualType.etyp = ETyp.unit ∧
    res.qualType.pred = Predicate.noPred ∧
    res.tagEnv' = invalidateTagDeps entry.bodyCtx.tagEnv
      (effectTargetLocs [builtinSetErrEffect] entry.bodyCtx.varEnv) ∧
    res.regime' = invalidateRegimeDepsEffect entry.bodyCtx.regime entry.bodyCtx.tagEnv
      (effectTargetLocs [builtinSetErrEffect] entry.bodyCtx.varEnv) ∧
    res.nextTag' = entry.bodyCtx.nextTag ∧
    applyExternEffect builtinSetErrEffect entry.bodyCtx.varEnv {} entry.bodyCtx.pc
        entry.bodyCtx.memEnv = .ok res.memEnv' ∧
    res.nextLoc' = entry.bodyCtx.nextLoc ∧
    res.declared' = entry.bodyCtx.declaredExternRefs ∧
    ∃ argQt : QTyp,
      entry.bodyCtx.varEnv.lookup "n" = some argQt ∧
      qtypCleanUnderRegime argQt entry.bodyCtx.regime = true := by
  cases htyped with
  | pfnExternMember _ hkind => simp [builtinSetErrDecl] at hkind
  | fnExternMember hid hkind htyp harg hret heff hcap hpin hbody happly =>
    rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
      id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec effects captures tenv
    have hcap' : captures = [] := by simpa [builtinSetErrDecl] using hcap.symm
    subst hcap'
    have heff' : effects = [builtinSetErrEffect] := by simpa [builtinSetErrDecl] using heff.symm
    subst heff'
    have hx : x = "n" := by
      have h : some x = some "n" := by simpa [builtinSetErrDecl] using harg.symm
      exact Option.some.inj h
    subst hx
    have hretSpec : retSpec = builtinSetErrRetSpec := by
      have h : some retSpec = some builtinSetErrRetSpec := by
        simpa [builtinSetErrDecl] using hret.symm
      exact Option.some.inj h
    subst hretSpec
    cases fuel with
    | zero => simp [applyFnTClosureAtCursor] at happly
    | succ fuel' =>
        simp only [applyFnTClosureAtCursor, builtinSetErrRetSpec, builtinSetErrEffect,
          collectExternPreds, List.map, List.cons_append, List.nil_append,
          collectAndAllocExternTags_noPred₂, List.forIn_cons, List.forIn_nil,
          resolveSyntaxPred, returnSpecToQTyp, bind, Except.bind, pure, Except.pure] at happly
        split at happly
        · simp at happly
        · rename_i hgate
          split at happly
          · simp at happly
          · rename_i memEnv' heffect
            simp only [Except.ok.injEq] at happly
            subst happly
            have hpin' : declaredArgQt.poison = false := by
              simpa [builtinSetErrDecl] using hpin
            have hcond :
                argConditionSatisfied declaredArgQt
                  ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩ bodyState.regime' fuel' = true := by
              simpa [capturesSatisfied] using hgate
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩, ?_, ?_⟩
            · simp [normalizeAppResultByProvenance]; split <;> rfl
            · simp [normalizeAppResultByProvenance]; split <;> rfl
            · rw [hbody]; rfl
            · rw [hbody]; simp only [applyExternRegimePolicy]; rfl
            · rw [hbody]
            · rw [hbody]; simp only [builtinSetErrEffect]
              convert heffect using 1
              cases applyExternEffect
                  { target := EffectTarget.namedVar "errno", poison := false, pred := SyntaxPredicate.noPred }
                  ((VarTypeEnv.ofCaptured tenv).update "n"
                    { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred })
                  ∅ (joinPoison p (joinPoison p1 ctx.pc)) bodyState.memEnv' <;> rfl
            · rw [hbody]
            · rw [hbody]
            · rw [hbody]; exact VarTypeEnv_lookup_update_eq _ "n" _
            · rw [hbody]
              exact argConditionSatisfied_cleanRegime_of_declClean hcond hpin'

/-- The single-run call-boundary field for `@22` (`set_err`): the first `.fn`
    (memory-writing) `callSingle`.  Under `ctx.pc = true` the effect poisons the
    written errno cell (`storedPoison = true`, `storedPred = noPred`), so the
    memory post conjuncts go through: unwritten cells transport, the written cell
    carries no surviving guard, and (by `θ` injectivity) no clean cell aliases the
    written address. -/
theorem builtinSetErr_callSingle :
    ExternCallBoundarySingle builtinSetErrDecl builtinSetErrImpl := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hwfTm hTmBounded
    θ cf o hθwf hwfCtx hric hreg hcons hwfcfg hrdIn hrun hpc
  obtain ⟨hetyp, hpred, htagEnv, hregime, hnextTag, heffect, _hnextLoc, hdeclEq, _argQt, _hbindN, _hcleanN⟩ :=
    builtinSetErr_call_clean_shape htyped
  obtain ⟨n, a, harg, herrnoRt, ho, hcfmem, hcfnext, hcfshape⟩ :=
    builtinSetErr_callRun_output hrun
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  -- Shared setup: the effect's target locset `ls`, and the runtime errno write
  -- realizes a logical location in `ls`.
  obtain ⟨vE, qtE, ls, rpE, htgtE, hlkE, hetypE, hresE, hmemE⟩ :=
    applyExternEffect_errno_shape heffect
  have hvE : vE = "errno" := by
    simpa [builtinSetErrEffect, EffectTarget.namedVar.injEq] using htgtE.symm
  subst hvE
  obtain ⟨vRt, hvRtLk, hvRtTyp⟩ := hric.2 hlkE
  have hvRtEq : vRt = Value.loc a := by
    have hb : entry.bodyConfig.varEnv.lookup "errno" = some (Value.loc a) := by
      simpa [ExternCallEntry.bodyConfig] using herrnoRt
    rw [hb] at hvRtLk; exact (Option.some.inj hvRtLk).symm
  subst hvRtEq
  rw [hetypE] at hvRtTyp
  obtain ⟨l_e, hθ_le, hle_in⟩ : ∃ l_e, θ.lookup l_e = some a ∧ l_e ∈ ls := by
    cases hvRtTyp with | loc hlk hin => exact ⟨_, hlk, hin⟩
  have hpcbody : entry.bodyCtx.pc = true := hpc
  -- Under `pc = true` the effect poisons every written cell and erases its
  -- predicate; unwritten cells keep their incoming type.
  have hwritten : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      qt.poison = true ∧ qt.pred = Predicate.noPred := by
    intro l qt hin hlk
    rw [hmemE] at hlk
    have h := assign_memEnv_formula_lookup_mem_props entry.bodyCtx.memEnv ls _ _ l hin qt hlk
    exact ⟨h.1 (by simp [hpcbody, joinPoison]), h.2 (by simp [hpcbody])⟩
  have hunwritten : ∀ l, l ∉ ls →
      res.memEnv'.lookup l = entry.bodyCtx.memEnv.lookup l := by
    intro l hnin
    rw [hmemE]
    exact assign_memEnv_formula_lookup_eq_of_not_mem entry.bodyCtx.memEnv ls _ _ l hnin
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by
      have hreg_eq : (entry.bodyOutputConfig cf).registry = entry.bodyConfig.registry := by
        rw [hcfshape]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
      rw [hreg_eq, hdeclEq]
      exact hrdIn)⟩
  · -- TagMeaningBounded tm res.nextTag'
    rw [hnextTag]; exact hTmBounded
  · -- wfTagMeaningCtx tm (ctxAfter ctx res): the effect writes poison=true/noPred
    -- cells (carrying no guard descriptor), leaves every other cell unchanged, and
    -- does not touch the variable environment.
    rcases hwfTm with ⟨hwfTm'⟩
    refine EnvRespectsTagMeaning.intro fun ⟨qtDeep, k0, d0, hqte0, hqd0⟩ => ?_
    rcases hqte0 with ⟨_, _, x, _, qtRoot, hlookupVar, hinq⟩ | ⟨_, _, loc, _, qtRoot, hlookupMem, hinq⟩
    · exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
        (QTypInEnvs.inVar _ _ x qtDeep qtRoot hlookupVar hinq) hqd0)
    · have hlookupMem' : res.memEnv'.lookup loc = some qtRoot := hlookupMem
      by_cases hin : loc ∈ ls
      · -- Written cell: ⟨int, true, noPred⟩ carries no guard descriptor.
        obtain ⟨_, hprednp⟩ := hwritten loc qtRoot hin hlookupMem'
        have hint : qtRoot.etyp = ETyp.int := memEnv_lookup_etyp_int _ _ _ hlookupMem'
        have hEq : qtDeep = qtRoot := QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [hint, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
        rw [hEq] at hqd0
        simp [qtypGuardDesc?, hprednp] at hqd0
      · rw [hunwritten loc hin] at hlookupMem'
        exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
          (QTypInEnvs.inMem _ _ loc qtDeep qtRoot hlookupMem' hinq) hqd0)
  · -- valueHasETyp θ o res.qualType.etyp
    rw [ho, hetyp]; exact valueHasETyp.unit
  · -- runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ
    refine ⟨fun l a' hθl => ?_, fun {x qt} hlk => ?_⟩
    · obtain ⟨hmem, hcont⟩ := hric.1 l a' hθl
      refine ⟨?_, ?_⟩
      · show res.memEnv'.contains l = true
        rw [hmemE]
        exact assign_memEnv_formula_contains_of_contains entry.bodyCtx.memEnv ls _ _ l hmem
      · show cf.memory.contains a' = true
        rw [hcfmem]
        have hbc : entry.callConfig.memory.contains a' = true := by
          simpa [ExternCallEntry.bodyConfig] using hcont
        simp [Memory.update, Std.ExtTreeMap.contains_insert, hbc]
    · exact hric.2 hlk
  · -- consistentWithRegime for the effect-updated context and memory.
    -- Written cells are poisoned with `noPred` (no obligation).  A tag live in
    -- the invalidated output regime was live with the same value in the input
    -- regime (the invalidation is a value-preserving sub-map), so the input
    -- consistency transports: an unwritten cell's realized address differs from
    -- the written errno address by `θ`-injectivity, and `predSat`-level facts
    -- move across the memory change by the `PredSatLaws` mem-compatibility law
    -- (a materialised errno-reading guard has been dropped from the regime, so
    -- its obligation is vacuous).
    have hmemc : ∀ (qt' : QTyp) (v' : Value),
        qtypPredHolds predSat qt' entry.bodyConfig.memory v' ↔
        qtypPredHolds predSat qt' cf.memory v' :=
      fun qt' v' => qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ
        entry.bodyConfig.memory cf.memory qt' v'
    have hmono : Regime.monotoneStep entry.bodyCtx.regime (ctxAfter ctx res).regime := by
      show Regime.monotoneStep entry.bodyCtx.regime res.regime'
      rw [hregime]
      exact invalidateRegimeDepsEffect_monotone _ _ _
    have hgate_val : ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        entry.bodyCtx.regime.lookup? k = some b := by
      intro k b hk
      have hk'' : res.regime'.lookup? k = some b := hk
      rw [hregime] at hk''
      exact invalidateRegimeDepsEffect_lookup_some_imp _ _ _ k b hk''
    have hgate_ne : ∀ k, (ctxAfter ctx res).regime.lookup? k ≠ none →
        entry.bodyCtx.regime.lookup? k ≠ none := by
      intro k hk
      cases hk0 : (ctxAfter ctx res).regime.lookup? k with
      | none => exact absurd hk0 hk
      | some b => rw [hgate_val k b hk0]; exact Option.some_ne_none b
    refine ⟨?_, ?_, ?_⟩
    · -- locations
      intro l qt k hlookup hguard hkR
      have hlookup' : res.memEnv'.lookup l = some qt := hlookup
      by_cases hin : l ∈ ls
      · obtain ⟨_, hprednp⟩ := hwritten l qt hin hlookup'
        simp [qtypGuardTag, hprednp] at hguard
      · rw [hunwritten l hin] at hlookup'
        have hold := hcons.1 l qt k hlookup' hguard (hgate_ne k hkR)
        cases hold with
        | noPred_ok hpn => exact locsRegime.noPred_ok (l, qt) hpn
        | guardOnly_ok k' hgo => exact locsRegime.guardOnly_ok (l, qt) k' hgo
        | withPred_ok k' an pb ve a' n' b' hclos hregk hreal hmem hconsist =>
            have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
            have hk'k : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                  _ = some k := hguard
              exact Option.some.inj this
            obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
              cases hk0 : (ctxAfter ctx res).regime.lookup? k with
              | none => exact absurd hk0 hkR
              | some b => exact ⟨b, rfl⟩
            have hbb' : b = b' := by
              have hbin := hgate_val k b hbout
              rw [hk'k] at hregk
              exact Option.some.inj (hbin.symm.trans hregk)
            have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
              rw [hk'k, ← hbb']
              exact hbout
            have hne : a' ≠ a := by
              intro heq
              apply hin
              have hl_e : θ.lookup l_e = some a' := by rw [heq]; exact hθ_le
              have hll : l = l_e := hθwf _ _ _ hreal hl_e
              rw [hll]; exact hle_in
            have hmem' : cf.memory.lookup a' = some n' := by
              rw [hcfmem]
              have hcmp : compare a a' ≠ Ordering.eq := by
                intro hce
                exact hne ((Nat.compare_eq_eq).1 hce).symm
              have hbody : entry.callConfig.memory.lookup a' = some n' := by
                simpa [ExternCallEntry.bodyConfig] using hmem
              simpa [Memory.update, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hbody
            refine locsRegime.withPred_ok (l, qt) k' an pb ve a' n' b' hclos hregk_out hreal hmem' ?_
            exact ⟨fun hb => (hmemc qt (Value.num n')).1 (hconsist.1 hb),
              fun hb hh => (hconsist.2 hb) ((hmemc qt (Value.num n')).2 hh)⟩
    · -- variables (the variable environment and its values are unchanged)
      intro x qt k hlookup hguard hkR
      have hold := hcons.2.1 x qt k hlookup hguard (hgate_ne k hkR)
      cases hold with
      | noPred_ok hpn => exact varsRegime.noPred_ok (x, qt) hpn
      | guardOnly_ok k' hgo => exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' an pb ve v b' hclos hregk hvar hconsist =>
          have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
          have hk'k : k' = k := by
            have : some k' = some k := by
              calc
                some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                _ = some k := hguard
            exact Option.some.inj this
          obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
            cases hk0 : (ctxAfter ctx res).regime.lookup? k with
            | none => exact absurd hk0 hkR
            | some b => exact ⟨b, rfl⟩
          have hbb' : b = b' := by
            have hbin := hgate_val k b hbout
            rw [hk'k] at hregk
            exact Option.some.inj (hbin.symm.trans hregk)
          have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
            rw [hk'k, ← hbb']
            exact hbout
          refine varsRegime.withPred_ok (x, qt) k' an pb ve v b' hclos hregk_out hvar ?_
          exact ⟨fun hb => (hmemc qt v).1 (hconsist.1 hb),
            fun hb hh => (hconsist.2 hb) ((hmemc qt v).2 hh)⟩
    · -- captured closures: the regime shrinks monotonically and `predSat`-level
      -- facts move across the memory change
      intro x qt v hlookup hvlookup
      have hold := hcons.2.2 x qt v hlookup hvlookup
      exact closureCapturedVarsRegime_monotone hmono
        (closureCapturedVarsRegime_transport_μ hmemc hold)
  · -- valueConsistentWithRegime
    rw [ho]
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hetyp ▸ valueHasETyp.unit) hnotfun)
  · -- PreservesInheritedFinalCleanLocsOneRun: a clean (or guard-clean) output cell
    -- is unwritten — written cells are poisoned with `noPred` — so by `θ`-injectivity
    -- its realized address differs from the written errno address and the write
    -- leaves its value unchanged.
    refine ⟨?_⟩
    intro l qt_in qt_out hlk_in hlk_out hclean_out
    have hnin : l ∉ ls := by
      intro hin
      obtain ⟨hp, hprednp⟩ := hwritten l qt_out hin hlk_out
      cases hclean_out with
      | clean hp' => rw [hp] at hp'; cases hp'
      | guard k htagk _ _ => simp [qtypGuardTag, hprednp] at htagk
    cases hθl : θ.lookup l with
    | none => exact .both_unrealized hθl hθl
    | some a' =>
        have hne : a' ≠ a := by
          intro heq
          apply hnin
          have hl_e : θ.lookup l_e = some a' := by rw [heq]; exact hθ_le
          have hll : l = l_e := hθwf _ _ _ hθl hl_e
          rw [hll]; exact hle_in
        obtain ⟨_, hcontA⟩ := hric.1 l a' hθl
        have hsomeA : (entry.bodyConfig.memory[a']?).isSome = true := by
          rw [← Std.ExtTreeMap.contains_eq_isSome_getElem?]
          exact hcontA
        obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsomeA
        have hn'' : entry.bodyConfig.memory.lookup a' = some n' := by
          rw [Memory.lookup, Std.ExtTreeMap.get?_eq_getElem?]
          exact hn'
        refine .preserve_value a' n' hθl hn'' hθl ?_
        show cf.memory.lookup a' = some n'
        rw [hcfmem]
        have hcmp : compare a a' ≠ Ordering.eq := by
          intro hce
          exact hne ((Nat.compare_eq_eq).1 hce).symm
        have hbody : entry.callConfig.memory.lookup a' = some n' := by
          simpa [ExternCallEntry.bodyConfig] using hn''
        simpa [Memory.update, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp] using hbody
  · -- FreshCleanLocsUnrealizedOneRun ctx res θ
    intro l qt hnc hlk hclean
    by_cases hin : l ∈ ls
    · cases hclean with
      | clean hp => rw [(hwritten l qt hin hlk).1] at hp; exact absurd hp (by decide)
      | guard k htag _ _ =>
          simp [qtypGuardTag, (hwritten l qt hin hlk).2] at htag
    · rw [hunwritten l hin] at hlk
      exact absurd (memEnv_contains_of_lookup_some _ l qt hlk) hnc

/-! ## The `set_err` `callFR` field

The two-run relational write-effect post: paired successful `@22` calls from
agreeing inputs produce `StepFRPost` for the two effect-updated configurations.
The per-run conjuncts mirror `builtinSetErr_callSingle` (without its `pc = true`
hypothesis: the written cells always store `noPred` — the effect predicate is
`noPred` on both gate branches — but may be *clean*).  The relational keys are:

* written-value agreement — the declared argument is clean, so the gate forces
  the body binding `"n"` clean under the body regime, and the two runs' integer
  arguments agree (`builtinSetErr_callRun_argEq`);
* target stability — when the written cells are clean the captured `errno`
  reference is clean too, so the input agreement on the `errno` binding yields
  one shared logical location realized by both runs' written addresses
  (`agreeValueUnder_ref_common_loc`); a dirty target poisons the written cells
  and the corresponding agreement obligations are vacuous. -/

-- Local mirrors of `StepFRAssign`-private regime/memory transport compositions
-- (built from the public `StepFR` primitives).

private lemma setErr_qtypCleanUnder_of_monotone
    {R R' : Regime} (hmono : Regime.monotoneStep R R') {qt : QTyp} :
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison => exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hkR : R.lookup? k ≠ none := hmono.2 k (by simp [hreg])
      cases hk : R.lookup? k with
      | none => exact (hkR hk).elim
      | some b =>
          rcases hmono.1 k b hk with hk' | hkNone
          · have hb : b = true := Option.some.inj (hk'.symm.trans hreg)
            subst hb
            exact qtypCleanUnder.guard k htag hk hnotfun
          · simp [hkNone] at hreg

private lemma setErr_agreeValueUnder_transport
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ μ₀' μ₁' : Memory}
    {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value}
    (hpred_compat₀ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₀ v ↔ qtypPredHolds predSat qt μ₀' v)
    (hpred_compat₁ : ∀ (qt : QTyp) (v : Value),
      qtypPredHolds predSat qt μ₁ v ↔ qtypPredHolds predSat qt μ₁' v)
    (hmono : Regime.monotoneStep R R')
    (hclean : qtypCleanUnder R' qt)
    (hagree : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁) :
    agreeValueUnder predSat R' μ₀' μ₁' θ₀ θ₁ qt v₀ v₁ := by
  have hcleanR : qtypCleanUnder R qt := setErr_qtypCleanUnder_of_monotone hmono hclean
  have hmem : agreeValueUnder predSat R μ₀' μ₁' θ₀ θ₁ qt v₀ v₁ :=
    agreeValueUnder_clean_extends_transport_mem hpred_compat₀ hpred_compat₁ hcleanR
      (by intro l a h; exact h) (by intro l a h; exact h) hagree
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      (fun qt hclean' => setErr_qtypCleanUnder_of_monotone hmono hclean')
      (fun h => memberVarsRegimeEvidence_monotone hmono h)
      (fun h => memberCvcrEvidence_monotone hmono h)
      (fun h => memberVarsRegimeEvidence_monotone hmono h)
      (fun h => memberCvcrEvidence_monotone hmono h)
      hclean hmem

/-- Two agreeing integer values are equal (the closure/ref constructors are
    impossible at an `int` type carried by `Value.num`). -/
private theorem agreeValueUnder_num_eq
    {predSat : PredSat} {R : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {n₀ n₁ : Int}
    (hInt : qt.etyp = ETyp.int)
    (h : agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁)) :
    n₀ = n₁ := by
  cases h with
  | clean_eq_nonref_nonarrow _ _ _ hEq =>
      simpa [Value.num.injEq] using hEq
  | withPred_true_eq _ _ _ _ _ hEq =>
      simpa [Value.num.injEq] using hEq
  | clean_internal_arrow _ _ _ _ _ _ _ _ _ _ _ hv₀ _ => cases hv₀
  | clean_internal_arrow_extern _ _ _ _ _ _ _ _ _ _ _ hv₀ _ => cases hv₀
  | dirty_internal_arrow _ hisArrow _ _ =>
      rw [hInt] at hisArrow; simp [ETyp.isArrow] at hisArrow
  | clean_internal_parrow _ _ _ _ _ _ _ _ _ _ _ hv₀ _ => cases hv₀
  | clean_internal_parrow_extern _ _ _ _ _ _ _ _ _ _ _ hv₀ _ => cases hv₀
  | dirty_internal_parrow _ hisParrow _ _ =>
      rw [hInt] at hisParrow; simp [ETyp.isParrow] at hisParrow
  | clean_ref _ _ _ _ hv₀ _ _ => cases hv₀
  | withPred_true_ref _ _ _ _ _ _ hv₀ _ _ => cases hv₀

/-- The body-entry environment of a successful `set_err` call binds `"n"` to the
    runtime argument value. -/
private theorem builtinSetErr_callRun_bodyVar
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun builtinSetErrDecl builtinSetErrImpl entry res cf o) :
    entry.bodyConfig.varEnv.lookup "n" = some entry.argValue := by
  cases hrun with
  | pfn hfacts => have h := hfacts.kind_pfn; simp [builtinSetErrDecl] at h
  | fn hfacts =>
      have hargName : entry.argName = "n" := by
        have h := hfacts.argName
        simp only [builtinSetErrDecl] at h
        exact (Option.some.inj h).symm
      have hbc : entry.bodyConfig.varEnv = entry.unifiedEnv := by
        simp [ExternCallEntry.bodyConfig]
      rw [hbc, hfacts.unifiedEnv_eq, hargName]
      simp [VarEnv.update, VarEnv.lookup]

/-- Argument equality for `set_err`: clean body agreement plus the clean argument
    binding (gate passed against the clean precondition) force the two integer
    arguments equal. -/
private theorem builtinSetErr_callRun_argEq
    {predSat : PredSat} {θ₀ θ₁ : RealizationMap}
    {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value} {typedExpr₀ : Expr}
    (htyped₀ : ExternBoundaryTyping.Call builtinSetErrDecl typedExpr₀ entry₀ res)
    (hbody : BodyEntryInputsAgree predSat entry₀.bodyCtx entry₀ entry₁ θ₀ θ₁)
    (hrun₀ : ExternCallBoundaryRun builtinSetErrDecl builtinSetErrImpl entry₀ res cf₀ o₀)
    (hrun₁ : ExternCallBoundaryRun builtinSetErrDecl builtinSetErrImpl entry₁ res cf₁ o₁)
    {m₀ m₁ : Int}
    (hm₀ : entry₀.argValue = Value.num m₀) (hm₁ : entry₁.argValue = Value.num m₁) :
    m₀ = m₁ := by
  obtain ⟨_, _, _, _, _, _, _, _, argQt, hbind, hcleanB⟩ :=
    builtinSetErr_call_clean_shape htyped₀
  have hrv₀ : entry₀.bodyConfig.varEnv.lookup "n" = some (Value.num m₀) := by
    rw [builtinSetErr_callRun_bodyVar hrun₀, hm₀]
  have hrv₁ : entry₁.bodyConfig.varEnv.lookup "n" = some (Value.num m₁) := by
    rw [builtinSetErr_callRun_bodyVar hrun₁, hm₁]
  obtain ⟨v, hvlk, hvet⟩ := hbody.runtime₀.2 hbind
  have hv : v = Value.num m₀ := by rw [hrv₀] at hvlk; exact (Option.some.inj hvlk).symm
  have hInt : argQt.etyp = ETyp.int := by rw [hv] at hvet; exact valueHasETyp_num_etyp hvet
  have hcleanP : qtypCleanUnder entry₀.bodyCtx.regime argQt :=
    qtypCleanUnder_of_cleanUnderRegime hcleanB (by rw [hInt]; rfl)
  exact builtinAbs_arg_eq_of_bodyAgree hbody hbind hcleanP hInt hrv₀ hrv₁

/-- The two-run call-boundary FR field for `@22` (`set_err`): the first `.fn`
    (memory-writing) `callFR`.  See the section header for the proof shape. -/
theorem builtinSetErr_callFR :
    ExternCallBoundaryFR builtinSetErrDecl builtinSetErrImpl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ _htyped₁ hpredlaws hwfTm hTmBounded θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
  obtain ⟨hetyp, hpred, htagEnv, hregime, hnextTag, heffect, hnextLoc, hdeclEq, argQtN, hbindN, _hcleanN⟩ :=
    builtinSetErr_call_clean_shape htyped₀
  obtain ⟨n₀, a₀, harg₀, herrnoRt₀, ho₀, hcfmem₀, hcfnext₀, hcfshape₀⟩ := builtinSetErr_callRun_output hrun₀
  obtain ⟨n₁, a₁, harg₁, herrnoRt₁, ho₁, hcfmem₁, hcfnext₁, hcfshape₁⟩ := builtinSetErr_callRun_output hrun₁
  have hnotfun : res.qualType.etyp.isFunctionType = false := by rw [hetyp]; rfl
  have hrespects : QTypRespectsTagMeaning tm res.qualType :=
    QTypRespectsTagMeaning_of_nonFunction_noGuard tm res.qualType hnotfun
      (by simp [qtypGuardDesc?, hpred])
  -- Type-level effect shape (shared by both runs: same bodyCtx, same res).
  obtain ⟨vE, qtE, ls, rpE, htgtE, hlkE, hetypE, hresE, hmemE⟩ :=
    applyExternEffect_errno_shape heffect
  have hvE : vE = "errno" := by
    simpa [builtinSetErrEffect, EffectTarget.namedVar.injEq] using htgtE.symm
  subst hvE
  have hrpE : rpE = Predicate.noPred := by
    symm
    simpa [builtinSetErrEffect, resolveSyntaxPred, pure, Except.pure] using hresE
  -- Per-run errno realization.
  obtain ⟨vRt₀, hvRtLk₀, hvRtTyp₀⟩ := hbody.runtime₀.2 hlkE
  have hvRtEq₀ : vRt₀ = Value.loc a₀ := by
    have hb : entry₀.bodyConfig.varEnv.lookup "errno" = some (Value.loc a₀) := by
      simpa [ExternCallEntry.bodyConfig] using herrnoRt₀
    rw [hb] at hvRtLk₀; exact (Option.some.inj hvRtLk₀).symm
  rw [hvRtEq₀, hetypE] at hvRtTyp₀
  obtain ⟨l_e₀, hθ_le₀, hle_in₀⟩ : ∃ l, θ₀.lookup l = some a₀ ∧ l ∈ ls := by
    cases hvRtTyp₀ with | loc hlk hin => exact ⟨_, hlk, hin⟩
  obtain ⟨vRt₁, hvRtLk₁, hvRtTyp₁⟩ := hbody.runtime₁.2 hlkE
  have hvRtEq₁ : vRt₁ = Value.loc a₁ := by
    have hb : entry₁.bodyConfig.varEnv.lookup "errno" = some (Value.loc a₁) := by
      simpa [ExternCallEntry.bodyConfig] using herrnoRt₁
    rw [hb] at hvRtLk₁; exact (Option.some.inj hvRtLk₁).symm
  rw [hvRtEq₁, hetypE] at hvRtTyp₁
  obtain ⟨l_e₁, hθ_le₁, hle_in₁⟩ : ∃ l, θ₁.lookup l = some a₁ ∧ l ∈ ls := by
    cases hvRtTyp₁ with | loc hlk hin => exact ⟨_, hlk, hin⟩
  -- The effect stores `noPred` on both gate branches (the effect predicate is
  -- `noPred`); the stored poison is the pc/target join.
  have hwrittenPred : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      qt.pred = Predicate.noPred := by
    intro l qt hin hlk
    rw [hmemE] at hlk
    have h := assign_memEnv_formula_lookup_mem_props ctx.memEnv ls _ _ l hin qt hlk
    exact h.2 (by rw [hrpE]; exact ite_self _)
  have hwrittenPoison : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison) = true →
      qt.poison = true := by
    intro l qt hin hlk hsp
    rw [hmemE] at hlk
    exact (assign_memEnv_formula_lookup_mem_props ctx.memEnv ls _ _ l hin qt hlk).1 hsp
  have hunwritten : ∀ l, l ∉ ls →
      res.memEnv'.lookup l = ctx.memEnv.lookup l := by
    intro l hnin
    rw [hmemE]
    exact assign_memEnv_formula_lookup_eq_of_not_mem ctx.memEnv ls _ _ l hnin
  -- Memory compatibility and the regime shrink.
  have hmemc₀ : ∀ (qt' : QTyp) (v' : Value),
      qtypPredHolds predSat qt' entry₀.bodyConfig.memory v' ↔
      qtypPredHolds predSat qt' cf₀.memory v' :=
    fun qt' v' => qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀
      entry₀.bodyConfig.memory cf₀.memory qt' v'
  have hmemc₁ : ∀ (qt' : QTyp) (v' : Value),
      qtypPredHolds predSat qt' entry₁.bodyConfig.memory v' ↔
      qtypPredHolds predSat qt' cf₁.memory v' :=
    fun qt' v' => qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁
      entry₁.bodyConfig.memory cf₁.memory qt' v'
  have hmono : Regime.monotoneStep ctx.regime (ctxAfter ctx res).regime := by
    show Regime.monotoneStep ctx.regime res.regime'
    rw [hregime]
    exact invalidateRegimeDepsEffect_monotone _ _ _
  have hgate_val : ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
      ctx.regime.lookup? k = some b := by
    intro k b hk
    have hk'' : res.regime'.lookup? k = some b := hk
    rw [hregime] at hk''
    exact invalidateRegimeDepsEffect_lookup_some_imp _ _ _ k b hk''
  have hgate_ne : ∀ k, (ctxAfter ctx res).regime.lookup? k ≠ none →
      ctx.regime.lookup? k ≠ none := by
    intro k hk
    cases hk0 : (ctxAfter ctx res).regime.lookup? k with
    | none => exact absurd hk0 hk
    | some b => rw [hgate_val k b hk0]; exact Option.some_ne_none b
  have hcleanIn : ∀ {qt : QTyp}, qtypCleanUnder (ctxAfter ctx res).regime qt →
      qtypCleanUnder ctx.regime qt :=
    fun h => setErr_qtypCleanUnder_of_monotone hmono h
  -- Per-run final-memory lookups away from the written address.
  have hfinal₀ : ∀ a', a' ≠ a₀ →
      cf₀.memory.lookup a' = entry₀.bodyConfig.memory.lookup a' := by
    intro a' hne
    rw [hcfmem₀]
    have hcmp : compare a₀ a' ≠ Ordering.eq := by
      intro hce
      exact hne ((Nat.compare_eq_eq).1 hce).symm
    simp [Memory.update, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp,
      ExternCallEntry.bodyConfig]
  have hfinal₁ : ∀ a', a' ≠ a₁ →
      cf₁.memory.lookup a' = entry₁.bodyConfig.memory.lookup a' := by
    intro a' hne
    rw [hcfmem₁]
    have hcmp : compare a₁ a' ≠ Ordering.eq := by
      intro hce
      exact hne ((Nat.compare_eq_eq).1 hce).symm
    simp [Memory.update, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp,
      ExternCallEntry.bodyConfig]
  have hne₀ : ∀ l a', l ∉ ls → θ₀.lookup l = some a' → a' ≠ a₀ := by
    intro l a' hnin hθl heq
    apply hnin
    have hl_e : θ₀.lookup l_e₀ = some a' := by rw [heq]; exact hθ_le₀
    have hll : l = l_e₀ := hbody.wfRealization₀ _ _ _ hθl hl_e
    rw [hll]; exact hle_in₀
  have hne₁ : ∀ l a', l ∉ ls → θ₁.lookup l = some a' → a' ≠ a₁ := by
    intro l a' hnin hθl heq
    apply hnin
    have hl_e : θ₁.lookup l_e₁ = some a' := by rw [heq]; exact hθ_le₁
    have hll : l = l_e₁ := hbody.wfRealization₁ _ _ _ hθl hl_e
    rw [hll]; exact hle_in₁
  -- Shared wfTagMeaningCtx for the effect-updated context.
  have hwfTmAfter : wfTagMeaningCtx tm (ctxAfter ctx res) := by
    rcases hwfTm with ⟨hwfTm'⟩
    refine EnvRespectsTagMeaning.intro fun ⟨qtDeep, k0, d0, hqte0, hqd0⟩ => ?_
    rcases hqte0 with ⟨_, _, x, _, qtRoot, hlookupVar, hinq⟩ | ⟨_, _, loc, _, qtRoot, hlookupMem, hinq⟩
    · exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
        (QTypInEnvs.inVar _ _ x qtDeep qtRoot hlookupVar hinq) hqd0)
    · have hlookupMem' : res.memEnv'.lookup loc = some qtRoot := hlookupMem
      by_cases hin : loc ∈ ls
      · have hprednp := hwrittenPred loc qtRoot hin hlookupMem'
        have hint : qtRoot.etyp = ETyp.int := memEnv_lookup_etyp_int _ _ _ hlookupMem'
        have hEq : qtDeep = qtRoot := QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [hint, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
        rw [hEq] at hqd0
        simp [qtypGuardDesc?, hprednp] at hqd0
      · rw [hunwritten loc hin] at hlookupMem'
        exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
          (QTypInEnvs.inMem _ _ loc qtDeep qtRoot hlookupMem' hinq) hqd0)
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, hwfTmAfter, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, hwfTmAfter, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- TagMeaningBounded tm res.nextTag'
    rw [hnextTag]; exact hTmBounded
  · -- valueHasETyp θ₀ o₀
    rw [ho₀, hetyp]; exact valueHasETyp.unit
  · -- valueHasETyp θ₁ o₁
    rw [ho₁, hetyp]; exact valueHasETyp.unit
  · -- wfTypeContext (ctxAfter ctx res)
    refine ⟨?_, ?_, ?_⟩
    · intro l hcont
      have hcont' : res.memEnv'.contains l = true := hcont
      rw [hmemE] at hcont'
      have hlt : l < ctx.nextLoc := by
        rcases assign_memEnv_formula_contains_eq_or_mem ctx.memEnv ls _ _ l hcont' with hold | hin
        · exact hbody.wfCtx.1 l hold
        · have hb := hbody.wfCtx.2.1 "errno" qtE hlkE
          rw [hetypE] at hb
          exact hb l (by simpa using hin)
      show l < (ctxAfter ctx res).nextLoc
      simp only [ctxAfter]
      rw [hnextLoc]
      exact hlt
    · simp only [ctxAfter]
      rw [hnextLoc]
      exact hbody.wfCtx.2.1
    · simp only [ctxAfter]
      rw [hnextLoc]
      exact hbody.wfCtx.2.2
  · -- TagBoundedCtx (ctxAfter ctx res)
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · intro k hk
      have hk' : res.tagEnv'.get? k ≠ none := hk
      rw [htagEnv] at hk'
      have hkin := invalidateTagDeps_get?_ne_none_imp _ _ k hk'
      have hlt := hbody.tagBounded.1 k hkin
      show k < (ctxAfter ctx res).nextTag
      simp only [ctxAfter]
      rw [hnextTag]
      exact hlt
    · simp only [ctxAfter]
      rw [hnextTag]
      exact hbody.tagBounded.2.1.1
    · intro l qt hlk
      have hlk' : res.memEnv'.lookup l = some qt := hlk
      show qtypPredTagBounded qt (ctxAfter ctx res).nextTag
      simp only [ctxAfter]
      rw [hnextTag]
      by_cases hin : l ∈ ls
      · have hprednp := hwrittenPred l qt hin hlk'
        simp only [qtypPredTagBounded, hprednp]
        trivial
      · rw [hunwritten l hin] at hlk'
        exact hbody.tagBounded.2.1.2 l qt hlk'
    · simp only [ctxAfter]
      rw [hnextTag]
      exact hbody.tagBounded.2.2
  · -- wfConfig (entry₀.bodyOutputConfig cf₀)
    refine ⟨?_, ?_⟩
    · intro a hconta
      have ha₀lt : a₀ < entry₀.bodyConfig.nextAddr :=
        setErrImpl_errno_target_wf hbody.wfConfig₀.2
          (by simpa [ExternCallEntry.bodyConfig] using herrnoRt₀)
      have hconta' : (Memory.update entry₀.callConfig.memory a₀ n₀).contains a := by
        have : (entry₀.bodyOutputConfig cf₀).memory = cf₀.memory := rfl
        rw [this, hcfmem₀] at hconta
        exact hconta
      rw [Memory.update, Std.ExtTreeMap.contains_insert] at hconta'
      have hnext : (entry₀.bodyOutputConfig cf₀).nextAddr = entry₀.bodyConfig.nextAddr := by
        show cf₀.nextAddr = entry₀.bodyConfig.nextAddr
        rw [hcfnext₀]; rfl
      rw [hnext]
      rcases (by simpa using hconta' : a₀ = a ∨ a ∈ entry₀.callConfig.memory) with heq | hold
      · rw [← heq]; exact ha₀lt
      · exact hbody.wfConfig₀.1 a (by simpa [ExternCallEntry.bodyConfig] using hold)
    · have hnext : (entry₀.bodyOutputConfig cf₀).nextAddr = entry₀.bodyConfig.nextAddr := by
        show cf₀.nextAddr = entry₀.bodyConfig.nextAddr
        rw [hcfnext₀]; rfl
      show wfVarEnv (entry₀.bodyOutputConfig cf₀).nextAddr (entry₀.bodyOutputConfig cf₀).varEnv
      rw [hnext]
      exact hbody.wfConfig₀.2
  · -- wfConfig (entry₁.bodyOutputConfig cf₁)
    refine ⟨?_, ?_⟩
    · intro a hconta
      have ha₁lt : a₁ < entry₁.bodyConfig.nextAddr :=
        setErrImpl_errno_target_wf hbody.wfConfig₁.2
          (by simpa [ExternCallEntry.bodyConfig] using herrnoRt₁)
      have hconta' : (Memory.update entry₁.callConfig.memory a₁ n₁).contains a := by
        have : (entry₁.bodyOutputConfig cf₁).memory = cf₁.memory := rfl
        rw [this, hcfmem₁] at hconta
        exact hconta
      rw [Memory.update, Std.ExtTreeMap.contains_insert] at hconta'
      have hnext : (entry₁.bodyOutputConfig cf₁).nextAddr = entry₁.bodyConfig.nextAddr := by
        show cf₁.nextAddr = entry₁.bodyConfig.nextAddr
        rw [hcfnext₁]; rfl
      rw [hnext]
      rcases (by simpa using hconta' : a₁ = a ∨ a ∈ entry₁.callConfig.memory) with heq | hold
      · rw [← heq]; exact ha₁lt
      · exact hbody.wfConfig₁.1 a (by simpa [ExternCallEntry.bodyConfig] using hold)
    · have hnext : (entry₁.bodyOutputConfig cf₁).nextAddr = entry₁.bodyConfig.nextAddr := by
        show cf₁.nextAddr = entry₁.bodyConfig.nextAddr
        rw [hcfnext₁]; rfl
      show wfVarEnv (entry₁.bodyOutputConfig cf₁).nextAddr (entry₁.bodyOutputConfig cf₁).varEnv
      rw [hnext]
      exact hbody.wfConfig₁.2
  · -- runtimeInstantiatesCtx (ctxAfter ctx res) (run 0)
    refine ⟨fun l a' hθl => ?_, fun {x qt} hlk => ?_⟩
    · obtain ⟨hmem, hcont⟩ := hbody.runtime₀.1 l a' hθl
      refine ⟨?_, ?_⟩
      · show res.memEnv'.contains l = true
        rw [hmemE]
        exact assign_memEnv_formula_contains_of_contains ctx.memEnv ls _ _ l hmem
      · show cf₀.memory.contains a' = true
        rw [hcfmem₀]
        have hbc : entry₀.callConfig.memory.contains a' = true := by
          simpa [ExternCallEntry.bodyConfig] using hcont
        simp [Memory.update, Std.ExtTreeMap.contains_insert, hbc]
    · exact hbody.runtime₀.2 hlk
  · -- runtimeInstantiatesCtx (ctxAfter ctx res) (run 1)
    refine ⟨fun l a' hθl => ?_, fun {x qt} hlk => ?_⟩
    · obtain ⟨hmem, hcont⟩ := hbody.runtime₁.1 l a' hθl
      refine ⟨?_, ?_⟩
      · show res.memEnv'.contains l = true
        rw [hmemE]
        exact assign_memEnv_formula_contains_of_contains ctx.memEnv ls _ _ l hmem
      · show cf₁.memory.contains a' = true
        rw [hcfmem₁]
        have hbc : entry₁.callConfig.memory.contains a' = true := by
          simpa [ExternCallEntry.bodyConfig] using hcont
        simp [Memory.update, Std.ExtTreeMap.contains_insert, hbc]
    · exact hbody.runtime₁.2 hlk
  · -- regimeConsistentWithCtx (ctxAfter ctx res)
    intro k deps hk
    have hk' : res.tagEnv'.get? k = some ⟨true, deps⟩ := hk
    rw [htagEnv] at hk'
    have hkin := invalidateTagDeps_get?_some_imp _ _ k _ hk'
    have hRtrue := hbody.regime k deps hkin
    show res.regime'.lookup? k = some true
    rw [hregime]
    exact invalidateRegimeDepsEffect_lookup_preserve_of_survive _ _ _ k true
      (Option.ne_none_iff_exists'.mpr ⟨_, hk'⟩) hRtrue
  · -- consistentWithRegime (run 0)
    refine ⟨?_, ?_, ?_⟩
    · intro l qt k hlookup hguard hkR
      have hlookup' : res.memEnv'.lookup l = some qt := hlookup
      by_cases hin : l ∈ ls
      · have hprednp := hwrittenPred l qt hin hlookup'
        simp [qtypGuardTag, hprednp] at hguard
      · rw [hunwritten l hin] at hlookup'
        have hold := hbody.consistent₀.1 l qt k hlookup' hguard (hgate_ne k hkR)
        cases hold with
        | noPred_ok hpn => exact locsRegime.noPred_ok (l, qt) hpn
        | guardOnly_ok k' hgo => exact locsRegime.guardOnly_ok (l, qt) k' hgo
        | withPred_ok k' an pb ve a' n' b' hclos hregk hreal hmem hconsist =>
            have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
            have hk'k : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                  _ = some k := hguard
              exact Option.some.inj this
            obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
              cases hk0 : (ctxAfter ctx res).regime.lookup? k with
              | none => exact absurd hk0 hkR
              | some b => exact ⟨b, rfl⟩
            have hbb' : b = b' := by
              have hbin := hgate_val k b hbout
              rw [hk'k] at hregk
              exact Option.some.inj (hbin.symm.trans hregk)
            have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
              rw [hk'k, ← hbb']
              exact hbout
            have hmem' : cf₀.memory.lookup a' = some n' := by
              rw [hfinal₀ a' (hne₀ l a' hin hreal)]
              exact hmem
            refine locsRegime.withPred_ok (l, qt) k' an pb ve a' n' b' hclos hregk_out hreal hmem' ?_
            exact ⟨fun hb => (hmemc₀ qt (Value.num n')).1 (hconsist.1 hb),
              fun hb hh => (hconsist.2 hb) ((hmemc₀ qt (Value.num n')).2 hh)⟩
    · intro x qt k hlookup hguard hkR
      have hold := hbody.consistent₀.2.1 x qt k hlookup hguard (hgate_ne k hkR)
      cases hold with
      | noPred_ok hpn => exact varsRegime.noPred_ok (x, qt) hpn
      | guardOnly_ok k' hgo => exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' an pb ve v b' hclos hregk hvar hconsist =>
          have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
          have hk'k : k' = k := by
            have : some k' = some k := by
              calc
                some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                _ = some k := hguard
            exact Option.some.inj this
          obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
            cases hk0 : (ctxAfter ctx res).regime.lookup? k with
            | none => exact absurd hk0 hkR
            | some b => exact ⟨b, rfl⟩
          have hbb' : b = b' := by
            have hbin := hgate_val k b hbout
            rw [hk'k] at hregk
            exact Option.some.inj (hbin.symm.trans hregk)
          have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
            rw [hk'k, ← hbb']
            exact hbout
          refine varsRegime.withPred_ok (x, qt) k' an pb ve v b' hclos hregk_out hvar ?_
          exact ⟨fun hb => (hmemc₀ qt v).1 (hconsist.1 hb),
            fun hb hh => (hconsist.2 hb) ((hmemc₀ qt v).2 hh)⟩
    · intro x qt v hlookup hvlookup
      have hold := hbody.consistent₀.2.2 x qt v hlookup hvlookup
      exact closureCapturedVarsRegime_monotone hmono
        (closureCapturedVarsRegime_transport_μ hmemc₀ hold)
  · -- consistentWithRegime (run 1)
    refine ⟨?_, ?_, ?_⟩
    · intro l qt k hlookup hguard hkR
      have hlookup' : res.memEnv'.lookup l = some qt := hlookup
      by_cases hin : l ∈ ls
      · have hprednp := hwrittenPred l qt hin hlookup'
        simp [qtypGuardTag, hprednp] at hguard
      · rw [hunwritten l hin] at hlookup'
        have hold := hbody.consistent₁.1 l qt k hlookup' hguard (hgate_ne k hkR)
        cases hold with
        | noPred_ok hpn => exact locsRegime.noPred_ok (l, qt) hpn
        | guardOnly_ok k' hgo => exact locsRegime.guardOnly_ok (l, qt) k' hgo
        | withPred_ok k' an pb ve a' n' b' hclos hregk hreal hmem hconsist =>
            have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
            have hk'k : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                  _ = some k := hguard
              exact Option.some.inj this
            obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
              cases hk0 : (ctxAfter ctx res).regime.lookup? k with
              | none => exact absurd hk0 hkR
              | some b => exact ⟨b, rfl⟩
            have hbb' : b = b' := by
              have hbin := hgate_val k b hbout
              rw [hk'k] at hregk
              exact Option.some.inj (hbin.symm.trans hregk)
            have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
              rw [hk'k, ← hbb']
              exact hbout
            have hmem' : cf₁.memory.lookup a' = some n' := by
              rw [hfinal₁ a' (hne₁ l a' hin hreal)]
              exact hmem
            refine locsRegime.withPred_ok (l, qt) k' an pb ve a' n' b' hclos hregk_out hreal hmem' ?_
            exact ⟨fun hb => (hmemc₁ qt (Value.num n')).1 (hconsist.1 hb),
              fun hb hh => (hconsist.2 hb) ((hmemc₁ qt (Value.num n')).2 hh)⟩
    · intro x qt k hlookup hguard hkR
      have hold := hbody.consistent₁.2.1 x qt k hlookup hguard (hgate_ne k hkR)
      cases hold with
      | noPred_ok hpn => exact varsRegime.noPred_ok (x, qt) hpn
      | guardOnly_ok k' hgo => exact varsRegime.guardOnly_ok (x, qt) k' hgo
      | withPred_ok k' an pb ve v b' hclos hregk hvar hconsist =>
          have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
          have hk'k : k' = k := by
            have : some k' = some k := by
              calc
                some k' = qtypGuardTag qt := by simp [qtypGuardTag, hclos']
                _ = some k := hguard
            exact Option.some.inj this
          obtain ⟨b, hbout⟩ : ∃ b, (ctxAfter ctx res).regime.lookup? k = some b := by
            cases hk0 : (ctxAfter ctx res).regime.lookup? k with
            | none => exact absurd hk0 hkR
            | some b => exact ⟨b, rfl⟩
          have hbb' : b = b' := by
            have hbin := hgate_val k b hbout
            rw [hk'k] at hregk
            exact Option.some.inj (hbin.symm.trans hregk)
          have hregk_out : (ctxAfter ctx res).regime.lookup? k' = some b' := by
            rw [hk'k, ← hbb']
            exact hbout
          refine varsRegime.withPred_ok (x, qt) k' an pb ve v b' hclos hregk_out hvar ?_
          exact ⟨fun hb => (hmemc₁ qt v).1 (hconsist.1 hb),
            fun hb hh => (hconsist.2 hb) ((hmemc₁ qt v).2 hh)⟩
    · intro x qt v hlookup hvlookup
      have hold := hbody.consistent₁.2.2 x qt v hlookup hvlookup
      exact closureCapturedVarsRegime_monotone hmono
        (closureCapturedVarsRegime_transport_μ hmemc₁ hold)
  · -- agreeOnClean across the two effect-updated runs
    refine ⟨?_, ?_⟩
    · -- locations
      intro l qt hlk hclean
      have hlk' : res.memEnv'.lookup l = some qt := hlk
      by_cases hin : l ∈ ls
      · -- A written-set cell.  Its predicate is `noPred`; cleanness forces the
        -- stored poison clean, hence pc and the captured errno reference clean.
        have hprednp := hwrittenPred l qt hin hlk'
        have hpoisonF : qt.poison = false := by
          cases hclean with
          | clean hp => exact hp
          | guard k htagk _ _ => simp [qtypGuardTag, hprednp] at htagk
        have hspF : joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison) = false := by
          by_contra hsp
          have hsp' : joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison) = true := by
            cases h : joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison) with
            | true => rfl
            | false => exact absurd h hsp
          have := hwrittenPoison l qt hin hlk' hsp'
          rw [hpoisonF] at this
          cases this
        have hsplit : ctx.pc = false ∧ qtE.poison = false := by
          have h := hspF
          simp [joinPoison, builtinSetErrEffect, Bool.or_eq_false_iff] at h
          exact ⟨h.1, h.2⟩
        -- Common written logical location from the clean errno binding agreement.
        have hcleanE : qtypCleanUnder ctx.regime qtE := qtypCleanUnder.clean hsplit.2
        have hvarE := hbody.agree.2 "errno" qtE hlkE hcleanE
        cases hvarE with
        | both_none _ _ h0 _ =>
            have hb : entry₀.bodyConfig.varEnv.lookup "errno" = some (Value.loc a₀) := by
              simpa [ExternCallEntry.bodyConfig] using herrnoRt₀
            rw [hb] at h0; cases h0
        | agree_values _ _ v₀' v₁' hl0 hl1 hval =>
            have e0 : v₀' = Value.loc a₀ := by
              have hb : entry₀.bodyConfig.varEnv.lookup "errno" = some (Value.loc a₀) := by
                simpa [ExternCallEntry.bodyConfig] using herrnoRt₀
              rw [hb] at hl0; exact (Option.some.inj hl0).symm
            have e1 : v₁' = Value.loc a₁ := by
              have hb : entry₁.bodyConfig.varEnv.lookup "errno" = some (Value.loc a₁) := by
                simpa [ExternCallEntry.bodyConfig] using herrnoRt₁
              rw [hb] at hl1; exact (Option.some.inj hl1).symm
            rw [e0, e1] at hval
            obtain ⟨l_c, hlc_in, hθ0c, hθ1c⟩ := agreeValueUnder_ref_common_loc hetypE hval
            have hqtInt : qt.etyp = ETyp.int := memEnv_lookup_etyp_int _ _ _ hlk'
            have hnotref : ¬ ∃ ls', qt.etyp = ETyp.ref ls' := by
              intro href
              rcases href with ⟨ls', h⟩
              rw [hqtInt] at h; cases h
            by_cases hlc : l = l_c
            · -- The written cell itself: both runs hold the (agreeing) argument.
              subst hlc
              have hagreeN : n₀ = n₁ :=
                builtinSetErr_callRun_argEq htyped₀ hbody hrun₀ hrun₁ harg₀ harg₁
              refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hθ0c hθ1c ?_ ?_ ?_
              · show cf₀.memory.lookup a₀ = some n₀
                rw [hcfmem₀]; simp [Memory.update, Memory.lookup]
              · show cf₁.memory.lookup a₁ = some n₁
                rw [hcfmem₁]; simp [Memory.update, Memory.lookup]
              · exact agreeValueUnder.clean_eq_nonref_nonarrow hpoisonF
                  (by rw [hqtInt]; rfl) hnotref (by rw [hagreeN])
            · -- A written-set member that is not the written cell: unwritten in
              -- both runs (the realizations of `l` differ from those of `l_c`).
              have hne₀' : ∀ a', θ₀.lookup l = some a' → a' ≠ a₀ := by
                intro a' hθl heq
                apply hlc
                have hl_c : θ₀.lookup l_c = some a' := by rw [heq]; exact hθ0c
                exact hbody.wfRealization₀ _ _ _ hθl hl_c
              have hne₁' : ∀ a', θ₁.lookup l = some a' → a' ≠ a₁ := by
                intro a' hθl heq
                apply hlc
                have hl_c : θ₁.lookup l_c = some a' := by rw [heq]; exact hθ1c
                exact hbody.wfRealization₁ _ _ _ hθl hl_c
              -- The pre-call cell: absent means unrealized in both runs.
              by_cases hcont : ctx.memEnv.contains l = true
              · -- Present: it was clean before the call (the joined stored poison
                -- is clean only if every tracked member was), so the input
                -- agreement transports.
                have hcontIsSome : (ctx.memEnv[l]?).isSome = true := by
                  rw [← Std.ExtTreeMap.contains_eq_isSome_getElem?]
                  exact hcont
                obtain ⟨e_old, hget_old⟩ := Option.isSome_iff_exists.mp hcontIsSome
                have hlk_old : ctx.memEnv.lookup l = some ⟨ETyp.int, e_old.poison, e_old.pred⟩ := by
                  simp only [MemoryTypeEnv.lookup]
                  rw [Std.ExtTreeMap.get?_eq_getElem?]
                  simp [hget_old]
                -- The output cell is the joined entry; its clean poison forces
                -- the old member poison clean.
                have hpoison_old : e_old.poison = false := by
                  rcases hls_shape : Std.ExtTreeSet.toList ls with _ | ⟨x, _ | ⟨y, ys⟩⟩
                  · have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin
                    simp [hls_shape] at hInList
                  · -- singleton: l = x = l_c, contradiction with hlc
                    exfalso
                    apply hlc
                    have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin
                    have hcInList : l_c ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hlc_in
                    rw [hls_shape] at hInList hcInList
                    simp at hInList hcInList
                    rw [hInList, hcInList]
                  · -- weak update: the joined poison is the fold over members
                    have hlk_weak : (updateLocsetWeak ctx.memEnv ls
                        (joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison))
                        (if (qtE.poison || ctx.pc) = true then Predicate.noPred else rpE)).lookup l = some qt := by
                      rw [hmemE] at hlk'
                      simpa [hls_shape] using hlk'
                    unfold updateLocsetWeak at hlk_weak
                    set joined :=
                      LocSet.fold ls
                        (joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison),
                          if (qtE.poison || ctx.pc) = true then Predicate.noPred else rpE)
                        (fun (accP, accPred) l0 =>
                          match ctx.memEnv.get? l0 with
                          | some qt0 => (joinPoison accP qt0.poison, joinPredicates accPred qt0.pred)
                          | none => (accP, Predicate.noPred)) with hjoined
                    set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalQt
                    dsimp at hlk_weak
                    unfold LocSet.fold at hlk_weak
                    rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hlk_weak
                    have hInList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin
                    have hlookup_final :
                        (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) ctx.memEnv).lookup l = some finalQt :=
                      list_fold_updateMemEnv_lookup_eq_of_mem ls.toList ctx.memEnv l finalQt hInList rfl
                    have hqtEq : qt = finalQt := by
                      have : some qt = some finalQt := by
                        calc
                          some qt =
                              (ls.toList.foldl (fun acc l0 => updateMemEnv acc l0 finalQt) ctx.memEnv).lookup l := by
                                symm
                                exact hlk_weak
                          _ = some finalQt := hlookup_final
                      exact Option.some.inj this
                    have hjoined_false : joined.1 = false := by
                      have : finalQt.poison = false := by rw [← hqtEq]; exact hpoisonF
                      simpa [hfinalQt] using this
                    have hjoined_fold :
                        ((ls.toList.foldl
                            (fun acc l0 =>
                              match ctx.memEnv[l0]? with
                              | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                              | none => (acc.1, Predicate.noPred))
                            (joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison),
                              if (qtE.poison || ctx.pc) = true then Predicate.noPred else rpE)).1) = false := by
                      unfold joined at hjoined_false
                      unfold LocSet.fold at hjoined_false
                      rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at hjoined_false
                      exact hjoined_false
                    exact
                      list_fold_joinPoison_false_implies_lookup_poison_false
                        ctx.memEnv ls.toList
                        (joinPoison ctx.pc (joinPoison qtE.poison builtinSetErrEffect.poison))
                        (if (qtE.poison || ctx.pc) = true then Predicate.noPred else rpE)
                        l ⟨ETyp.int, e_old.poison, e_old.pred⟩ hInList hlk_old hjoined_fold
                have hclean_old : qtypCleanUnder ctx.regime (⟨ETyp.int, e_old.poison, e_old.pred⟩ : QTyp) :=
                  qtypCleanUnder.clean hpoison_old
                have hagree_old := hbody.agree.1 l _ hlk_old hclean_old
                cases hagree_old with
                | both_unrealized _ _ hnone₀ hnone₁ =>
                    exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
                | agree_values _ _ a0 a1 m₀ m₁ hreal₀ hreal₁ hlkm₀ hlkm₁ hagreeV =>
                    have hmEq : m₀ = m₁ := agreeValueUnder_num_eq rfl hagreeV
                    refine agreeLocUnder.agree_values l qt a0 a1 m₀ m₁ hreal₀ hreal₁ ?_ ?_ ?_
                    · show cf₀.memory.lookup a0 = some m₀
                      rw [hfinal₀ a0 (hne₀' a0 hreal₀)]
                      simpa [ExternCallEntry.bodyConfig] using hlkm₀
                    · show cf₁.memory.lookup a1 = some m₁
                      rw [hfinal₁ a1 (hne₁' a1 hreal₁)]
                      simpa [ExternCallEntry.bodyConfig] using hlkm₁
                    · exact agreeValueUnder.clean_eq_nonref_nonarrow hpoisonF
                        (by rw [hqtInt]; rfl) hnotref (by rw [hmEq])
              · -- Absent: never realized, in either run.
                have hnone₀ : θ₀.lookup l = none := by
                  cases hθl : θ₀.lookup l with
                  | none => rfl
                  | some a' =>
                      have := (hbody.runtime₀.1 l a' hθl).1
                      exact absurd this (by simpa using hcont)
                have hnone₁ : θ₁.lookup l = none := by
                  cases hθl : θ₁.lookup l with
                  | none => rfl
                  | some a' =>
                      have := (hbody.runtime₁.1 l a' hθl).1
                      exact absurd this (by simpa using hcont)
                exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      · -- An unwritten cell: the input agreement transports across the two writes.
        rw [hunwritten l hin] at hlk'
        have hagree_old := hbody.agree.1 l qt hlk' (hcleanIn hclean)
        cases hagree_old with
        | both_unrealized _ _ hnone₀ hnone₁ =>
            exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
        | agree_values _ _ a0 a1 m₀ m₁ hreal₀ hreal₁ hlkm₀ hlkm₁ hagreeV =>
            refine agreeLocUnder.agree_values l qt a0 a1 m₀ m₁ hreal₀ hreal₁ ?_ ?_ ?_
            · show cf₀.memory.lookup a0 = some m₀
              rw [hfinal₀ a0 (hne₀ l a0 hin hreal₀)]
              exact hlkm₀
            · show cf₁.memory.lookup a1 = some m₁
              rw [hfinal₁ a1 (hne₁ l a1 hin hreal₁)]
              exact hlkm₁
            · exact setErr_agreeValueUnder_transport hmemc₀ hmemc₁ hmono hclean hagreeV
    · -- variables: the environments and values are unchanged
      intro x qt hlk hclean
      have hvar := hbody.agree.2 x qt hlk (hcleanIn hclean)
      cases hvar with
      | both_none _ _ h0 h1 =>
          exact agreeVarUnder.both_none x qt h0 h1
      | agree_values _ _ v₀ v₁ hl0 hl1 hval =>
          refine agreeVarUnder.agree_values x qt v₀ v₁ hl0 hl1 ?_
          exact setErr_agreeValueUnder_transport hmemc₀ hmemc₁ hmono hclean hval
  · -- valueConsistentWithRegime (run 0)
    rw [ho₀]
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hetyp ▸ valueHasETyp.unit) hnotfun)
  · -- valueConsistentWithRegime (run 1)
    rw [ho₁]
    exact valueConsistentWithRegime.noTag (by simp [qtypGuardTag, hpred])
      (closureCapturedVarsRegime_nonClosure_of_nonFunctionType (hetyp ▸ valueHasETyp.unit) hnotfun)
  · -- resultAgreesIfClean (both outputs are `unit`) + reserved-discipline transports
    refine ⟨?_, ?_, ?_⟩
    · intro hclean
      rw [ho₀, ho₁]
      cases hclean with
      | clean hpoison =>
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison (by rw [hetyp]; rfl)
            (by intro href; rcases href with ⟨ls', h⟩; rw [hetyp] at h; cases h) rfl
      | guard k htag _ _ =>
          have hnone : qtypGuardTag res.qualType = none := by simp [qtypGuardTag, hpred]
          simp [hnone] at htag
    · have hreg_eq : (entry₀.bodyOutputConfig cf₀).registry = entry₀.bodyConfig.registry := by
        rw [hcfshape₀]
        simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
      rw [hreg_eq, hdeclEq]
      exact hbody.reserved₀
    · have hreg_eq : (entry₁.bodyOutputConfig cf₁).registry = entry₁.bodyConfig.registry := by
        rw [hcfshape₁]
        simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
      rw [hreg_eq, hdeclEq]
      exact hbody.reserved₁

/-! ## The `set_err` operational field

`setErrImpl_operational` already matches the `fn` clause of
`ExternOperationalSafe` verbatim; the `pfn`/`val` clauses are impossible by
constructor mismatch. -/

theorem builtinSetErrImpl_operationalSafe :
    ExternOperationalSafe builtinSetErrDecl builtinSetErrImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- impure `fn` branch: exactly `setErrImpl_operational`.
    intro implFn himpl env vArg mem addr vRaw mem' addr' hrun
    simp only [builtinSetErrImpl, ExternImpl.fn.injEq] at himpl
    subst himpl
    exact setErrImpl_operational env vArg mem addr vRaw mem' addr' hrun
  · -- pure `pfn` branch: impossible.
    intro implPfn himpl _ _ _ _ _ _ _ _ _
    simp [builtinSetErrImpl] at himpl
  · -- `val` branch: impossible.
    intro v himpl _ _
    simp [builtinSetErrImpl] at himpl
  · -- fn mem-mono: `setErrImpl` only does `mem.update a n` (= `mem.insert a n`),
    --   which preserves all existing keys.
    intro implFn himpl env vArg mem addr vRaw mem' addr' hrun a hc
    simp only [builtinSetErrImpl, ExternImpl.fn.injEq] at himpl
    subst himpl
    -- Unfold setErrImpl to see the memory update
    cases vArg with
    | num n =>
      cases hlook : VarEnv.lookup env "errno" with
      | none => simp [setErrImpl, hlook] at hrun
      | some w =>
        cases w with
        | loc errAddr =>
          simp only [setErrImpl, hlook, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨_, rfl, _⟩ := hrun
          -- mem' = mem.update errAddr n = mem.insert errAddr n
          -- ExtTreeMap.contains_insert: (t.insert k v).contains a = (cmp k a == Ordering.eq || t.contains a)
          simp only [Memory.update]
          rw [ExtTreeMap.contains_insert]
          simp [hc]
        | num _ => simp [setErrImpl, hlook] at hrun
        | bool _ => simp [setErrImpl, hlook] at hrun
        | unit => simp [setErrImpl, hlook] at hrun
        | str _ => simp [setErrImpl, hlook] at hrun
        | closure _ _ _ => simp [setErrImpl, hlook] at hrun
        | peClosure _ _ _ => simp [setErrImpl, hlook] at hrun
    | bool _ => simp [setErrImpl] at hrun
    | unit => simp [setErrImpl] at hrun
    | str _ => simp [setErrImpl] at hrun
    | loc _ => simp [setErrImpl] at hrun
    | closure _ _ _ => simp [setErrImpl] at hrun
    | peClosure _ _ _ => simp [setErrImpl] at hrun

/-! ## The `set_err` declaration-boundary fields: `declSingle` and `declFR`

The declaration `extern fn @22 …` typechecks (via `typecheckExternFn`) to an
extern *closure* type: an `arrow` whose single `FnTClosure.extern` carries the
declared effects and captures the declaration context's type environment — the
first `.fn` declaration realization (every prior one is `.pfn`).  No tags or
locations are allocated, so `ctxAfter ctx res = ctx` and both posts collapse
exactly as in the `abs` declaration fields, with the `fn`-flavored extern
constructors (`valueHasETyp.closure_extern`,
`deepValueQTypProperty.closure_extern`, `QTypRespectsTagMeaning_fn_extern`,
`agreeValueUnder.clean_internal_arrow_extern`). -/

/-- The extern closure stored in the `set_err` declaration's `arrow` type. -/
private def builtinSetErrExternClosure (ctx : TypeContext) (argQt : QTyp) : FnTClosure :=
  FnTClosure.extern 22 "n" builtinSetErrRetSpec [builtinSetErrEffect]
    (VarTypeEnv.toCaptured ctx.varEnv) argQt []

/-- The exact `TypeResult` produced by typechecking `extern fn @22 …` in `ctx`. -/
private def builtinSetErrDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.arrow Typ.int (parseReturnType builtinSetErrRetSpec) ctx.pc
        [builtinSetErrExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := ctx.declaredExternRefs
}

/-- Inverting a `set_err` declaration typing witness pins the result to
    `builtinSetErrDeclResult ctx argQt` for some argument precondition `argQt`. -/
private theorem builtinSetErr_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinSetErrDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = builtinSetErrDeclResult ctx argQt := by
  cases htyped with
  | fn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcFn :
              typecheckExternFn ctx 22 "n" Typ.int false argPred builtinSetErrRetSpec
                [builtinSetErrEffect] [] = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternFn_ok_res_eq ctx 22 "n" Typ.int false argPred builtinSetErrRetSpec
              [builtinSetErrEffect] res htcFn
          exact ⟨argQt, hres⟩

/-- The declaration expression typed against `builtinSetErrDecl` is
    `externFn @22` with the clean integer signature and the single `!errno`
    effect; only its argument predicate is free. -/
private theorem builtinSetErr_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinSetErrDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec
        [builtinSetErrEffect] captures := by
  cases htyped with
  | fn _htc => exact ⟨_, _, rfl⟩

/-- The `set_err` declaration's extern closure value is well-typed at the
    declared `arrow` type (the `fn` mirror of `builtinAbs_decl_valueHasETyp`). -/
private theorem builtinSetErr_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.closure "n"
        (Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec [builtinSetErrEffect] captures) ρ)
      (builtinSetErrDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.closure "n"
        (Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec [builtinSetErrEffect] captures) ρ)
      (ETyp.arrow Typ.int (parseReturnType builtinSetErrRetSpec) ctx.pc
        [builtinSetErrExternClosure ctx argQt])
  refine valueHasETyp.closure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := []) (htcl := by simp [builtinSetErrExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

/-- The `set_err` declaration's extern closure value is regime-consistent (the
    `fn` mirror of `builtinAbs_decl_valueConsistent`). -/
private theorem builtinSetErr_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinSetErrDeclResult ctx argQt).qualType μ θ
      (Value.closure "n"
        (Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec [builtinSetErrEffect] captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinSetErrDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.closure_extern (argQt := argQt) (memberCap := []) 22 "n" "n" Typ.int
      builtinSetErrRetSpec [builtinSetErrEffect] ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [builtinSetErrExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [builtinSetErrExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

/-- A successful `set_err` declaration boundary leaves the config unchanged and
    emits the extern `fn` closure value (`val`/`pfn` impossible by kind). -/
private theorem builtinSetErr_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinSetErrDecl builtinSetErrImpl ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.closure "n"
        (Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec [builtinSetErrEffect] captures)
        cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinSetErrDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [builtinSetErrDecl] at h
  | pfn hfacts => have h := hfacts.kind_pfn; simp [builtinSetErrDecl] at h
  | fn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "n" := by
        have h := hargName; simp [builtinSetErrDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinSetErrRetSpec := by
        have h := hretSpec; simp [builtinSetErrDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [builtinSetErrDecl] using hval⟩

/-- The `set_err` single-run declaration-boundary field. -/
theorem builtinSetErr_declSingle :
    ExternDeclBoundarySingle builtinSetErrDecl builtinSetErrImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinSetErr_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := builtinSetErr_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinSetErrDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_fn_extern tm ctx 22 "n" Typ.int (parseReturnType builtinSetErrRetSpec)
      ctx.pc builtinSetErrRetSpec [builtinSetErrEffect] (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.closure "n"
      (Expr.externFn 22 "n" Typ.int false argPred builtinSetErrRetSpec [builtinSetErrEffect] captures) ρ := by
    rw [ho]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf, hd_res]; exact hrdIn)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact builtinSetErr_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact builtinSetErr_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · exact FreshCleanLocsUnrealizedOneRun.vacuous_of_ctxAfter_eq hctxAfter

/-- The `set_err` paired declaration-boundary field: both outputs are the `fn`
    closure of the shared declaration expression, so the two clean extern arrows
    agree via `agreeValueUnder.clean_internal_arrow_extern`. -/
theorem builtinSetErr_declFR :
    ExternDeclBoundaryFR builtinSetErrDecl builtinSetErrImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinSetErr_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := builtinSetErr_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinSetErr_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinSetErr_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.closure "n"
      (Expr.externFn 22 "n" Typ.int false argPredT builtinSetErrRetSpec [builtinSetErrEffect] capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.closure "n"
      (Expr.externFn 22 "n" Typ.int false argPredT builtinSetErrRetSpec [builtinSetErrEffect] capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinSetErrDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_fn_extern tm ctx 22 "n" Typ.int (parseReturnType builtinSetErrRetSpec)
      ctx.pc builtinSetErrRetSpec [builtinSetErrEffect] (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : res.declared' = ctx.declaredExternRefs := by
    have h := congrArg TypeContext.declaredExternRefs hctxAfter
    simpa [ctxAfter] using h
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀, hd_res]; exact hrdIn₀), (by rw [hcf₁, hd_res]; exact hrdIn₁)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact builtinSetErr_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact builtinSetErr_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact builtinSetErr_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact builtinSetErr_decl_valueConsistent hric₁ hcwr₁
  · -- resultAgreesIfClean: the two extern arrows agree (shared argPredT)
    rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (builtinSetErrDeclResult ctx argQt).qualType.etyp =
            ETyp.arrow Typ.int (parseReturnType builtinSetErrRetSpec) ctx.pc
              [builtinSetErrExternClosure ctx argQt] := rfl
        have htcl : builtinSetErrExternClosure ctx argQt ∈ [builtinSetErrExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (builtinSetErrDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [builtinSetErrDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (builtinSetErrDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_arrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (builtinSetErrDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, builtinSetErrDeclResult]
        simp [hnone] at htag

/-- The complete trusted-extern-entry boundary contract for the built-in
    `set_err` extern (`@22`): all five `ExternBoundarySpec` fields.  This is the
    first fully proven `.fn` (write-effect) trusted entry. -/
theorem builtinSetErrSpec : ExternBoundarySpec builtinSetErrDecl builtinSetErrImpl where
  declFR := builtinSetErr_declFR
  callFR := builtinSetErr_callFR
  declSingle := builtinSetErr_declSingle
  callSingle := builtinSetErr_callSingle
  operational := builtinSetErrImpl_operationalSafe

/-- The interpreter's default registry dispatches `@22` to the same `setErrImpl`
    the trusted spec is proven against (mirrors `defaultRegistry_lookup_abs`). -/
theorem defaultRegistry_lookup_seterr :
    defaultRegistry.get? 22 = some builtinSetErrImpl := by
  simp [defaultRegistry, defaultInitialState, regInsert, register, builtinSetErrImpl,
    Std.HashMap.getElem_insert, Std.HashMap.contains_insert, Std.HashMap.contains_empty]

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

/-! ## Reference-valued externs (`extern ref`): the `@21` errno boundary

Declaration-boundary machinery for reference-valued externs and the trusted
`@21` entry.  The declaration-level fault-robustness (`StepFRPost`) and
single-run (`ExternBoundarySinglePost`) obligations for an `extern ref`
declaration consume the runtime reserved-cell facts:

* the run produces `Value.loc a` for a fixed reserved address `a`;
* `a` is present in memory (for `runtimeInstantiatesCtx` of the extended θ);
* `a` is not in the range of the incoming θ (for the injectivity-preserving
  realization-map insert `ell ↦ a`).

The declaration allocates a fresh logical location `ell = ctx.nextLoc`,
seeds its cell as POISONED with `noPred` (`points_to: (int :> poisoned {})`),
and returns a clean `ref {ell}`.  The poisoned cell makes the clean-agreement
and fresh-clean-location obligations vacuous; the clean ref result forces the
θ extension, which is where the reserved-address freshness hypothesis is
consumed. -/

open scoped MemoryTypeEnv

/-- The `points_to:` cell qualifier of a conservative `extern ref` declaration:
    poisoned with no predicate. -/
def externRefCellQt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩

/-- The typing result of an `extern ref @id` declaration in `ctx`: one fresh
    logical location `ctx.nextLoc` carrying the poisoned `points_to:` cell, a
    clean `ref {ctx.nextLoc}` result, `id` added to the declared set, all
    other typing state unchanged.  Mirrors `typecheckExternRef` exactly. -/
def externRefDeclResult (ctx : TypeContext) (id : ExternId) : TypeResult := {
  qualType := ⟨ETyp.ref (LocSet.singleton ctx.nextLoc), false, Predicate.noPred⟩
  memEnv' := updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc + 1
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := id :: ctx.declaredExternRefs
}

namespace ExternRefDecl

/-- The poisoned `noPred` cell is never clean under any regime. -/
lemma cellQt_not_cleanUnder (R : Regime) : ¬ qtypCleanUnder R externRefCellQt := by
  intro hclean
  cases hclean with
  | clean hpoison => simp [externRefCellQt] at hpoison
  | guard k htag _ _ => simp [externRefCellQt, qtypGuardTag] at htag

/-- Self lookup in the extended memory type environment returns the cell. -/
lemma memEnv_lookup_self (Γ : MemoryTypeEnv) (l : Loc) :
    (updateMemEnv Γ l externRefCellQt).lookup l = some externRefCellQt := by
  simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self, Option.map, externRefCellQt]

/-- Membership in the extended memory type environment. -/
lemma memEnv_contains_cases {Γ : MemoryTypeEnv} {l l' : Loc}
    (h : (updateMemEnv Γ l externRefCellQt).contains l') :
    l' = l ∨ Γ.contains l' := by
  by_cases hEq : l' = l
  · exact Or.inl hEq
  · have hCmp : compare l l' ≠ Ordering.eq := by
      intro hce
      have : l = l' := (Nat.compare_eq_eq).1 hce
      exact hEq this.symm
    have hOld : Γ.contains l' = true := by
      simp [updateMemEnv, Std.ExtTreeMap.contains_insert, hCmp] at h
      exact h
    exact Or.inr hOld

lemma memEnv_contains_self (Γ : MemoryTypeEnv) (l : Loc) :
    (updateMemEnv Γ l externRefCellQt).contains l := by
  simp [updateMemEnv, Std.ExtTreeMap.contains_insert]

lemma memEnv_contains_of_old {Γ : MemoryTypeEnv} {l l' : Loc}
    (h : Γ.contains l') :
    (updateMemEnv Γ l externRefCellQt).contains l' := by
  by_cases hEq : l' = l
  · subst hEq
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert]
  · have hCmp : compare l l' ≠ Ordering.eq := by
      intro hce
      have : l = l' := (Nat.compare_eq_eq).1 hce
      exact hEq this.symm
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert, h]

/-- The incoming realization map does not realize the fresh location. -/
lemma theta_fresh_none
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (hwf : wfTypeContext ctx) (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    θ.lookup ctx.nextLoc = none :=
  freshLoc_not_realized ctx μ ρ θ ctx.nextLoc hwf hric (Nat.le_refl _)

/-- Self lookup in the extended realization map. -/
lemma theta_lookup_self (θ : RealizationMap) (l : Loc) (a : Address) :
    (θ.update l a).lookup l = some a := by
  simp [RealizationMap.update, RealizationMap.lookup]

/-- The θ insert at the fresh location is a lookup-preserving extension. -/
lemma theta_extends
    {θ : RealizationMap} {ell : Loc} {a : Address}
    (hnone : θ.lookup ell = none) :
    θ.extendsMap (θ.update ell a) := by
  intro l a' hl
  by_cases h : l = ell
  · subst h
    rw [hnone] at hl
    exact absurd hl (by simp)
  · rw [RealizationMap_lookup_update_ne h]
    exact hl

/-- The θ insert at the fresh location preserves well-formedness (injectivity)
    because the reserved address is not in θ's range.  This is the load-bearing
    use of the reserved-address freshness hypothesis. -/
lemma theta_wfExtends
    {θ : RealizationMap} {ell : Loc} {a : Address}
    (hnone : θ.lookup ell = none)
    (hfresh : ∀ l, θ.lookup l ≠ some a) :
    wfExtendsMap θ (θ.update ell a) := by
  refine ⟨theta_extends hnone, ?_⟩
  intro hinj l₁ l₂ a' h1 h2
  exact ExtTreeMap_insert_preserves_injectivity θ ell a
    (fun k' => hfresh k') hinj l₁ l₂ a' h1 h2

/-- The returned location value is typed at the declared ref type under the
    extended realization map. -/
lemma result_valueHasETyp
    (ctx : TypeContext) (id : ExternId) (θ : RealizationMap) (a : Address) :
    valueHasETyp (θ.update ctx.nextLoc a) (Value.loc a)
      (externRefDeclResult ctx id).qualType.etyp := by
  show valueHasETyp (θ.update ctx.nextLoc a) (Value.loc a)
    (ETyp.ref (LocSet.singleton ctx.nextLoc))
  exact valueHasETyp.loc (l := ctx.nextLoc)
    (theta_lookup_self θ ctx.nextLoc a) (by simp [LocSet.singleton])

/-- The returned location value is regime-consistent: the result type carries
    no guard tag, and a location is not a closure. -/
lemma result_valueConsistent
    (ctx : TypeContext) (id : ExternId) (predSat : PredSat) (R : Regime)
    (μ : Memory) (θ' : RealizationMap) (a : Address) :
    valueConsistentWithRegime predSat R
      (externRefDeclResult ctx id).qualType μ θ' (Value.loc a) :=
  valueConsistentWithRegime.noTag
    (by simp [externRefDeclResult, qtypGuardTag])
    (.intro (.nonClosure (by intro xp bd rc h; simp at h)
                         (by intro xp bd rc h; simp at h)))

/-- The extended runtime instantiation: the fresh location realizes to the
    present reserved address; inherited locations transport along the
    extension; variables transport via `valueHasETyp_extends`. -/
lemma ric_extended
    (ctx : TypeContext) (id : ExternId) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (a : Address)
    (hwf : wfTypeContext ctx)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hpresent : μ.contains a) :
    runtimeInstantiatesCtx (ctxAfter ctx (externRefDeclResult ctx id)) μ ρ
      (θ.update ctx.nextLoc a) := by
  have hnone : θ.lookup ctx.nextLoc = none := theta_fresh_none ctx μ ρ θ hwf hric
  constructor
  · intro l a' hl
    by_cases h : l = ctx.nextLoc
    · subst h
      have hself := theta_lookup_self θ ctx.nextLoc a
      have ha' : a' = a := by
        have := hself.symm.trans hl
        exact (Option.some.inj this).symm
      subst ha'
      exact ⟨memEnv_contains_self ctx.memEnv ctx.nextLoc, hpresent⟩
    · rw [RealizationMap_lookup_update_ne h] at hl
      obtain ⟨hmem, hmem_a⟩ := hric.1 l a' hl
      exact ⟨memEnv_contains_of_old hmem, hmem_a⟩
  · intro x qt hx
    obtain ⟨v, hv, hvtyp⟩ := hric.2 hx
    exact ⟨v, hv, valueHasETyp_extends (theta_extends hnone) hvtyp⟩

/-- Regime consistency for the extended context: the fresh cell carries
    `noPred` (no guard tag), inherited locations transport along the θ
    extension with unchanged memory, variables and closure evidence are
    unchanged. -/
lemma cwr_extended
    (ctx : TypeContext) (id : ExternId) (predSat : PredSat)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (a : Address)
    (hnone : θ.lookup ctx.nextLoc = none)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    consistentWithRegime predSat
      (ctxAfter ctx (externRefDeclResult ctx id)).regime
      (ctxAfter ctx (externRefDeclResult ctx id)) μ ρ
      (θ.update ctx.nextLoc a) := by
  have hext : θ.extendsMap (θ.update ctx.nextLoc a) := theta_extends hnone
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hkR
    have hlookup' :
        (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup l = some qt := by
      simpa [ctxAfter, externRefDeclResult] using hlookup
    by_cases h : l = ctx.nextLoc
    · subst h
      have hqt : qt = externRefCellQt := by
        have hself := memEnv_lookup_self ctx.memEnv ctx.nextLoc
        exact Option.some.inj (hlookup'.symm.trans hself)
      subst hqt
      simp [externRefCellQt, qtypGuardTag] at hguard
    · rw [MemoryTypeEnv_lookup_updateMemEnv_ne h] at hlookup'
      have hloc := hcwr.1 l qt k hlookup' hguard hkR
      cases hloc with
      | noPred_ok hpred => exact locsRegime.noPred_ok (l, qt) hpred
      | guardOnly_ok k' hgo => exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' arg_name pred_body var_env a_old n_old b hclos hreg hreal hmem hcons =>
          exact locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a_old n_old b
            hclos hreg (hext l a_old hreal) hmem hcons
  · intro x qt k hlookup hguard hkR
    have hlookup' : ctx.varEnv.lookup x = some qt := by
      simpa [ctxAfter, externRefDeclResult] using hlookup
    exact hcwr.2.1 x qt k hlookup' hguard hkR
  · intro x qt v hlookup hv
    have hlookup' : ctx.varEnv.lookup x = some qt := by
      simpa [ctxAfter, externRefDeclResult] using hlookup
    exact closureCapturedVarsRegime_transport_μ_θ (fun _ _ => Iff.rfl) hext
      (hcwr.2.2 x qt v hlookup' hv)

/-- Clean agreement for the extended context: the fresh cell is poisoned (so
    vacuous), inherited locations and variables transport along the two θ
    extensions with unchanged memories. -/
lemma agree_extended
    (ctx : TypeContext) (id : ExternId) (predSat : PredSat)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap) (a : Address)
    (hnone₀ : θ₀.lookup ctx.nextLoc = none)
    (hnone₁ : θ₁.lookup ctx.nextLoc = none)
    (hagree : agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat
      (ctxAfter ctx (externRefDeclResult ctx id)).regime
      (ctxAfter ctx (externRefDeclResult ctx id))
      μ₀ ρ₀ (θ₀.update ctx.nextLoc a) μ₁ ρ₁ (θ₁.update ctx.nextLoc a) := by
  have hext₀ : θ₀.extendsMap (θ₀.update ctx.nextLoc a) := theta_extends hnone₀
  have hext₁ : θ₁.extendsMap (θ₁.update ctx.nextLoc a) := theta_extends hnone₁
  constructor
  · intro l qt hlookup hclean
    have hlookup' :
        (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup l = some qt := by
      simpa [ctxAfter, externRefDeclResult] using hlookup
    by_cases h : l = ctx.nextLoc
    · subst h
      have hqt : qt = externRefCellQt := by
        have hself := memEnv_lookup_self ctx.memEnv ctx.nextLoc
        exact Option.some.inj (hlookup'.symm.trans hself)
      subst hqt
      exact absurd hclean (cellQt_not_cleanUnder _)
    · rw [MemoryTypeEnv_lookup_updateMemEnv_ne h] at hlookup'
      have hold := hagree.1 l qt hlookup' hclean
      cases hold with
      | both_unrealized _ _ hn0 hn1 =>
          refine agreeLocUnder.both_unrealized l qt ?_ ?_
          · rw [RealizationMap_lookup_update_ne h]; exact hn0
          · rw [RealizationMap_lookup_update_ne h]; exact hn1
      | agree_values _ _ a0 a1 n0 n1 hr0 hr1 hm0 hm1 hag =>
          refine agreeLocUnder.agree_values l qt a0 a1 n0 n1
            (hext₀ l a0 hr0) (hext₁ l a1 hr1) hm0 hm1 ?_
          exact agreeValueUnder_clean_extends_transport_mem
            (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hclean hext₀ hext₁ hag
  · intro x qt hlookup hclean
    have hlookup' : ctx.varEnv.lookup x = some qt := by
      simpa [ctxAfter, externRefDeclResult] using hlookup
    have hold := hagree.2 x qt hlookup' hclean
    cases hold with
    | both_none _ _ hn0 hn1 => exact agreeVarUnder.both_none x qt hn0 hn1
    | agree_values _ _ v0 v1 hl0 hl1 hag =>
        exact agreeVarUnder.agree_values x qt v0 v1 hl0 hl1
          (agreeValueUnder_clean_extends_transport_mem
            (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) hclean hext₀ hext₁ hag)

/-- The two clean ref results agree: both runs return the same reserved
    address, realized at the shared fresh logical location. -/
lemma result_agrees
    (ctx : TypeContext) (id : ExternId) (predSat : PredSat)
    (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (a : Address) :
    resultAgreesIfClean predSat (ctxAfter ctx (externRefDeclResult ctx id)).regime
      μ₀ μ₁ (θ₀.update ctx.nextLoc a) (θ₁.update ctx.nextLoc a)
      (externRefDeclResult ctx id).qualType (Value.loc a) (Value.loc a) := by
  intro _hclean
  exact agreeValueUnder.clean_ref (l := ctx.nextLoc)
    (hpoison := rfl) (hetyp := rfl)
    (hlookup1 := theta_lookup_self θ₀ ctx.nextLoc a)
    (hin := by simp [LocSet.singleton])
    (hv1 := rfl)
    (hlookup2 := theta_lookup_self θ₁ ctx.nextLoc a)
    (hv2 := rfl)

/-- Tag-meaning facts: no tags are allocated, the result type and the new cell
    carry no guard descriptors. -/
lemma boundaryTagMeaningPost
    (ctx : TypeContext) (id : ExternId) (predSat : PredSat) (tm : TagMeaning)
    (hpredlaws : PredSatLaws predSat tm)
    (hwfTm : wfTagMeaningCtx tm ctx)
    (hTmBounded : TagMeaningBounded tm ctx.nextTag) :
    BoundaryTagMeaningPost ctx (externRefDeclResult ctx id) predSat tm tm := by
  have hcell_desc :
      ∀ {qt' k d}, QTypInQTyp qt' externRefCellQt →
        qtypGuardDesc? qt' = some (k, d) → tm.lookup k = some d := by
    intro qt' k d hinq hqd
    have hnotfun : externRefCellQt.etyp.isFunctionType = false := by
      simp [externRefCellQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hEq : qt' = externRefCellQt := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
    subst hEq
    simp [externRefCellQt, qtypGuardDesc?] at hqd
  have hEnvTm : EnvRespectsTagMeaning tm ctx.varEnv
      (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt) := by
    have hEnvTm_ctx : EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv := hwfTm
    have hupd := EnvRespectsTagMeaning_memEnv_ext tm ctx.varEnv ctx.memEnv
      ctx.nextLoc externRefCellQt (by simp [externRefCellQt]) hEnvTm_ctx hcell_desc
    simpa [updateMemEnv, MemoryTypeEnv.update, externRefCellQt] using hupd
  have hresTm : QTypRespectsTagMeaning tm (externRefDeclResult ctx id).qualType := by
    have hnotfun : (externRefDeclResult ctx id).qualType.etyp.isFunctionType = false := by
      simp [externRefDeclResult, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
    have hguard : qtypGuardDesc? (externRefDeclResult ctx id).qualType = none := by
      simp [externRefDeclResult, qtypGuardDesc?]
    intro qt' k d hinq hqd
    exact QTypRespectsTagMeaning_of_nonFunction_noGuard tm _ hnotfun hguard hinq hqd
  refine ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩
  · exact hTmBounded
  · exact wfTagMeaningCtx_ctxAfter tm ctx (externRefDeclResult ctx id) hEnvTm

/-- Well-formedness of the extended typing context: the fresh location is
    bounded by the advanced cursor, inherited bounds are monotone. -/
lemma wfCtx_extended
    (ctx : TypeContext) (id : ExternId) (hwf : wfTypeContext ctx) :
    wfTypeContext (ctxAfter ctx (externRefDeclResult ctx id)) := by
  simp only [wfTypeContext, ctxAfter, externRefDeclResult]
  refine ⟨?_, varEnvRefLocsBounded_mono hwf.2.1 (Nat.le_succ _),
    varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 (Nat.le_succ _)⟩
  intro l hcontains
  rcases memEnv_contains_cases hcontains with h | h
  · subst h
    exact Nat.lt_succ_self _
  · exact Nat.lt_trans (hwf.1 l h) (Nat.lt_succ_self _)

/-- Tag boundedness of the extended typing context: tags are untouched; the
    new cell's `noPred` predicate carries no tags. -/
lemma tagBounded_extended
    (ctx : TypeContext) (id : ExternId) (hbnd : TagBoundedCtx ctx) :
    TagBoundedCtx (ctxAfter ctx (externRefDeclResult ctx id)) := by
  refine ⟨hbnd.1, ⟨hbnd.2.1.1, ?_⟩, hbnd.2.2⟩
  intro l qt hlookup
  by_cases h : l = ctx.nextLoc
  · subst h
    have hqt : qt = externRefCellQt := by
      have hself := memEnv_lookup_self ctx.memEnv ctx.nextLoc
      have hlookup' :
          (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup ctx.nextLoc
            = some qt := hlookup
      exact Option.some.inj (hlookup'.symm.trans hself)
    subst hqt
    exact trivial
  · have hlookup' : ctx.memEnv.lookup l = some qt := by
      have hl :
          (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup l
            = some qt := hlookup
      rw [MemoryTypeEnv_lookup_updateMemEnv_ne h] at hl
      exact hl
    exact hbnd.2.1.2 l qt hlookup'

/-- Inherited clean locations keep their realization and cell value: the
    config is unchanged, and the θ extension preserves inherited lookups. -/
lemma preservesInherited
    (ctx : TypeContext) (id : ExternId) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (a : Address)
    (hwf : wfTypeContext ctx)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    PreservesInheritedFinalCleanLocsOneRun ctx (externRefDeclResult ctx id)
      μ μ θ (θ.update ctx.nextLoc a) := by
  refine ⟨?_⟩
  intro l qt_in _qt_out hin _hout _hclean
  have hne : l ≠ ctx.nextLoc := by
    intro h
    subst h
    have hcontains := memEnv_contains_of_lookup_some ctx.memEnv ctx.nextLoc qt_in hin
    exact Nat.lt_irrefl ctx.nextLoc (hwf.1 ctx.nextLoc hcontains)
  cases hθ : θ.lookup l with
  | none =>
      refine .both_unrealized hθ ?_
      rw [RealizationMap_lookup_update_ne hne]
      exact hθ
  | some a' =>
      have hcontains : μ.contains a' = true := (hric.1 l a' hθ).2
      obtain ⟨n, hn⟩ := Memory_lookup_some_of_contains hcontains
      refine .preserve_value a' n hθ hn ?_ hn
      rw [RealizationMap_lookup_update_ne hne]
      exact hθ

/-- Fresh clean locations are unrealized: the only fresh location carries the
    poisoned cell, which is never clean. -/
lemma freshCleanUnrealized
    (ctx : TypeContext) (id : ExternId) (θ : RealizationMap) (a : Address) :
    FreshCleanLocsUnrealizedOneRun ctx (externRefDeclResult ctx id)
      (θ.update ctx.nextLoc a) := by
  intro l qt hnotin hlookup hclean
  by_cases h : l = ctx.nextLoc
  · subst h
    have hqt : qt = externRefCellQt := by
      have hself := memEnv_lookup_self ctx.memEnv ctx.nextLoc
      have hlookup' :
          (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup ctx.nextLoc
            = some qt := hlookup
      exact Option.some.inj (hlookup'.symm.trans hself)
    subst hqt
    exact absurd hclean (cellQt_not_cleanUnder _)
  · have hlookup' : ctx.memEnv.lookup l = some qt := by
      have hl : (updateMemEnv ctx.memEnv ctx.nextLoc externRefCellQt).lookup l
          = some qt := hlookup
      rw [MemoryTypeEnv_lookup_updateMemEnv_ne h] at hl
      exact hl
    exact absurd (memEnv_contains_of_lookup_some ctx.memEnv l qt hlookup') hnotin

end ExternRefDecl

open ExternRefDecl in
/-- Single-run declaration field for `extern ref`: a successful run (config
    unchanged, output the reserved `Value.loc a`) discharges
    `ExternBoundarySinglePost`.  The reserved-cell facts come from the
    threaded invariants: presence and bound from `RegistryReservedWF`,
    θ-range freshness from `ReservedDiscipline` (with the id not yet
    declared, which `typecheckExternRef`'s duplicate gate guarantees). -/
theorem externRef_declSinglePost
    (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cf : Config) (o : Value)
    (na : Address) (pm : Bool) (registry : ExternRegistry)
    (id : ExternId) (a : Address)
    (hres : res = externRefDeclResult ctx id)
    (hpredlaws : PredSatLaws predSat tm)
    (hwfTm : wfTagMeaningCtx tm ctx)
    (hTmBounded : TagMeaningBounded tm ctx.nextTag)
    (hwf : wfTypeContext ctx)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    (hreserved : RegistryReservedWF registry μ na)
    (hrd : ReservedDiscipline registry ctx.declaredExternRefs θ)
    (hlookup_reg : registry.get? id = some (ExternImpl.val (Value.loc a)))
    (hnotdecl : id ∉ ctx.declaredExternRefs)
    (hcf : cf = { memory := μ, varEnv := ρ, nextAddr := na, pureMode := pm,
                  registry := registry })
    (ho : o = Value.loc a) :
    ExternBoundarySinglePost ctx res predSat tm θ μ cf o := by
  subst hres ho hcf
  have hpresent : μ.contains a := (hreserved a ⟨id, hlookup_reg⟩).1
  have hfresh : ∀ l, θ.lookup l ≠ some a :=
    hrd.fresh_addr hlookup_reg hnotdecl
  have hnone : θ.lookup ctx.nextLoc = none := theta_fresh_none ctx μ ρ θ hwf hric
  refine ⟨tm, boundaryTagMeaningPost ctx id predSat tm hpredlaws hwfTm hTmBounded,
    θ.update ctx.nextLoc a, theta_wfExtends hnone hfresh,
    result_valueHasETyp ctx id θ a,
    ric_extended ctx id μ ρ θ a hwf hric hpresent,
    cwr_extended ctx id predSat μ ρ θ a hnone hcwr,
    result_valueConsistent ctx id predSat _ μ _ a,
    preservesInherited ctx id μ ρ θ a hwf hric,
    freshCleanUnrealized ctx id θ a,
    hrd.declare hlookup_reg⟩

open ExternRefDecl in
/-- Two-run FR field shape: paired successful `extern ref`
    declaration runs (configs unchanged, both outputs the same reserved
    `Value.loc a`) discharge `StepFRPost` given the reserved-cell facts as
    explicit hypotheses for both runs. -/
theorem externRef_declFRPost
    (postExpr : Expr) (ctx : TypeContext) (res : TypeResult)
    (predSat : PredSat) (tm : TagMeaning)
    (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value)
    (a₀ a₁ : Address) (pm : Bool) (registry : ExternRegistry)
    (id : ExternId) (a : Address)
    (hres : res = externRefDeclResult ctx id)
    (hpredlaws : PredSatLaws predSat tm)
    (hwfTm : wfTagMeaningCtx tm ctx)
    (hTmBounded : TagMeaningBounded tm ctx.nextTag)
    (hwf : wfTypeContext ctx)
    (hbnd : TagBoundedCtx ctx)
    (hric₀ : runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀)
    (hric₁ : runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁)
    (hreg : regimeConsistentWithCtx ctx)
    (hcwr₀ : consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀)
    (hcwr₁ : consistentWithRegime predSat ctx.regime ctx μ₁ ρ₁ θ₁)
    (hagree : agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
    (hwfcfg₀ : wfConfig { memory := μ₀, varEnv := ρ₀, nextAddr := a₀,
                          pureMode := pm, registry := registry })
    (hwfcfg₁ : wfConfig { memory := μ₁, varEnv := ρ₁, nextAddr := a₁,
                          pureMode := pm, registry := registry })
    (hcf₀ : cf₀ = { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
                    registry := registry })
    (hcf₁ : cf₁ = { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
                    registry := registry })
    (ho₀ : o₀ = Value.loc a)
    (ho₁ : o₁ = Value.loc a)
    (hreserved₀ : RegistryReservedWF registry μ₀ a₀)
    (hreserved₁ : RegistryReservedWF registry μ₁ a₁)
    (hrd₀ : ReservedDiscipline registry ctx.declaredExternRefs θ₀)
    (hrd₁ : ReservedDiscipline registry ctx.declaredExternRefs θ₁)
    (hlookup_reg : registry.get? id = some (ExternImpl.val (Value.loc a)))
    (hnotdecl : id ∉ ctx.declaredExternRefs) :
    StepFRPost ctx postExpr res predSat tm θ₀ θ₁ cf₀ cf₁ o₀ o₁ := by
  subst hres ho₀ ho₁ hcf₀ hcf₁
  have hpresent₀ : μ₀.contains a := (hreserved₀ a ⟨id, hlookup_reg⟩).1
  have hpresent₁ : μ₁.contains a := (hreserved₁ a ⟨id, hlookup_reg⟩).1
  have hfresh₀ : ∀ l, θ₀.lookup l ≠ some a :=
    hrd₀.fresh_addr hlookup_reg hnotdecl
  have hfresh₁ : ∀ l, θ₁.lookup l ≠ some a :=
    hrd₁.fresh_addr hlookup_reg hnotdecl
  have hnone₀ : θ₀.lookup ctx.nextLoc = none := theta_fresh_none ctx μ₀ ρ₀ θ₀ hwf hric₀
  have hnone₁ : θ₁.lookup ctx.nextLoc = none := theta_fresh_none ctx μ₁ ρ₁ θ₁ hwf hric₁
  have hpost := boundaryTagMeaningPost ctx id predSat tm hpredlaws hwfTm hTmBounded
  refine ⟨tm, hpost, hpredlaws, hpost.2.2.2.1,
    θ₀.update ctx.nextLoc a, θ₁.update ctx.nextLoc a,
    theta_wfExtends hnone₀ hfresh₀,
    theta_wfExtends hnone₁ hfresh₁,
    result_valueHasETyp ctx id θ₀ a,
    result_valueHasETyp ctx id θ₁ a,
    hpost.2.2.1,
    wfCtx_extended ctx id hwf,
    tagBounded_extended ctx id hbnd,
    hwfcfg₀,
    hwfcfg₁,
    ric_extended ctx id μ₀ ρ₀ θ₀ a hwf hric₀ hpresent₀,
    ric_extended ctx id μ₁ ρ₁ θ₁ a hwf hric₁ hpresent₁,
    hreg,
    cwr_extended ctx id predSat μ₀ ρ₀ θ₀ a hnone₀ hcwr₀,
    cwr_extended ctx id predSat μ₁ ρ₁ θ₁ a hnone₁ hcwr₁,
    agree_extended ctx id predSat μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ a hnone₀ hnone₁ hagree,
    result_valueConsistent ctx id predSat _ μ₀ _ a,
    result_valueConsistent ctx id predSat _ μ₁ _ a,
    result_agrees ctx id predSat μ₀ μ₁ θ₀ θ₁ a,
    hrd₀.declare hlookup_reg,
    hrd₁.declare hlookup_reg⟩

/-! ## The trusted `@21` (`errno`) reference-extern entry

The first trusted `extern ref` boundary spec.  The declaration fields are the
two theorems above instantiated at the `@21` shape; the call fields are
vacuous (a reference extern is a declaration, not a callable); the
operational field's stored-location clause is discharged from the
reserved-address bound. -/

/-- The `@21` declaration shape produced by
    `extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {})`. -/
def builtinErrnoDecl : ExternDeclaration :=
  { id := 21
    kind := .ref
    typ := Typ.ref Typ.int
    argName := none
    retSpec := none
    effects := []
    preds := [SyntaxPredicate.noPred, SyntaxPredicate.noPred]
    argPoison := false
    refPoison := false
    cellPoison := true }

/-- The shipped runtime implementation: the registry hands out the stable
    `errnoAddr` cell. -/
def builtinErrnoImpl : ExternImpl := ExternImpl.val (Value.loc errnoAddr)

namespace ExternRefDecl

/-- Inversion of a successful `typecheckExternRef`: the v1 gates passed, so
    the result is exactly `externRefDeclResult` and the id was undeclared. -/
theorem typecheckExternRef_ok_inv
    {ctx : TypeContext} {id : ExternId}
    {refPoison : Bool} {refPred : SyntaxPredicate}
    {cellPoison : Bool} {cellPred : SyntaxPredicate} {res : TypeResult}
    (htc : typecheckExternRef ctx id refPoison refPred cellPoison cellPred = .ok res) :
    res = externRefDeclResult ctx id ∧ id ∉ ctx.declaredExternRefs := by
  unfold typecheckExternRef at htc
  by_cases hgate : (ctx.pureCtx || !ctx.externRefAllowed) = true
  · rw [if_pos hgate] at htc
    exact nomatch htc
  · rw [if_neg hgate] at htc
    by_cases hdup : ctx.declaredExternRefs.contains id = true
    · rw [if_pos hdup] at htc
      exact nomatch htc
    · rw [if_neg hdup] at htc
      have hnot : id ∉ ctx.declaredExternRefs := by
        intro hmem
        exact hdup (List.contains_iff_mem.mpr hmem)
      cases refPoison <;> cases refPred <;> cases cellPoison <;> cases cellPred <;>
        simp [bind, Except.bind, pure, Except.pure, updateMemEnv] at htc ;
        exact ⟨by simp [externRefDeclResult, externRefCellQt, updateMemEnv, htc.symm], hnot⟩

/-- Inverting a `@21` declaration typing witness pins the result to
    `externRefDeclResult` and yields the duplicate-gate fact. -/
theorem builtinErrno_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinErrnoDecl postExpr ctx res) :
    res = externRefDeclResult ctx 21 ∧ 21 ∉ ctx.declaredExternRefs := by
  cases htyped with
  | ref htc =>
      rename_i fuel
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcRef :
              typecheckExternRef ctx 21 false SyntaxPredicate.noPred true
                SyntaxPredicate.noPred = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          exact typecheckExternRef_ok_inv htcRef

/-- A successful `@21` declaration boundary run leaves the config unchanged
    and emits the reserved location value. -/
theorem builtinErrno_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun builtinErrnoDecl builtinErrnoImpl ctx res cᵢ cf o) :
    cf = cᵢ ∧ o = Value.loc errnoAddr ∧
      cᵢ.registry.get? 21 = some (ExternImpl.val (Value.loc errnoAddr)) := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinErrnoDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinErrnoDecl] at h
  | pfn hfacts => have h := hfacts.kind_pfn; simp [builtinErrnoDecl] at h
  | ref hfacts =>
      obtain ⟨addr, himpl, hv⟩ := hfacts.impl_value
      have haddr : addr = errnoAddr := by
        have h := himpl
        simp [builtinErrnoImpl] at h
        exact h.symm
      subst haddr
      refine ⟨hfacts.output_config, hv, ?_⟩
      have hlookup := hfacts.lookup
      simpa [builtinErrnoDecl, builtinErrnoImpl] using hlookup

end ExternRefDecl

open ExternRefDecl in
/-- The `@21` two-run declaration-boundary field. -/
theorem builtinErrno_declFR : ExternDeclBoundaryFR builtinErrnoDecl builtinErrnoImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ hwf hbnd hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁
    hrun₀ hrun₁
  obtain ⟨hres, hnotdecl⟩ := builtinErrno_decl_shape htyped
  obtain ⟨hcf₀, ho₀, hlookup₀⟩ := builtinErrno_declRun_shape hrun₀.run
  obtain ⟨hcf₁, ho₁, _⟩ := builtinErrno_declRun_shape hrun₁.run
  exact externRef_declFRPost postExpr ctx res predSat tm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁
    cf₀ cf₁ o₀ o₁ a₀ a₁ pm registry 21 errnoAddr hres hpredlaws hwfTm hTmBounded
    hwf hbnd hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree hwfcfg₀ hwfcfg₁ hcf₀ hcf₁
    ho₀ ho₁ hres₀ hres₁ hrd₀ hrd₁ (by simpa using hlookup₀) hnotdecl

open ExternRefDecl in
/-- The `@21` single-run declaration-boundary field. -/
theorem builtinErrno_declSingle :
    ExternDeclBoundarySingle builtinErrnoDecl builtinErrnoImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf hwf hric _hreg hcwr a pm registry _hwfcfg hreserved hrd
    hrun _hpc
  obtain ⟨hres, hnotdecl⟩ := builtinErrno_decl_shape htyped
  obtain ⟨hcf, ho, hlookup⟩ := builtinErrno_declRun_shape hrun
  exact externRef_declSinglePost ctx res predSat tm μ ρ θ cf o a pm registry
    21 errnoAddr hres hpredlaws hwfTm hTmBounded hwf hric hcwr hreserved hrd
    (by simpa using hlookup) hnotdecl hcf ho

open ExternRefDecl in
/-- The `@21` call fields are vacuous: a reference extern is a declaration,
    not a callable — no `Call` typing witness exists at kind `.ref`. -/
theorem builtinErrno_callFR : ExternCallBoundaryFR builtinErrnoDecl builtinErrnoImpl := by
  intro postExpr typedExpr₀ typedExpr₁ res predSat tm entry₀ entry₁ _ctx _hctx
    hcall₀ _hcall₁
  cases hcall₀ with
  | fnExternMember hid hkind _ _ _ _ _ _ _ _ =>
      exact absurd hkind (by simp [builtinErrnoDecl])
  | pfnExternMember hid hkind _ _ _ _ _ _ _ =>
      exact absurd hkind (by simp [builtinErrnoDecl])

open ExternRefDecl in
theorem builtinErrno_callSingle :
    ExternCallBoundarySingle builtinErrnoDecl builtinErrnoImpl := by
  intro typedExpr res predSat tm entry _ctx hcall
  cases hcall with
  | fnExternMember hid hkind _ _ _ _ _ _ _ _ =>
      exact absurd hkind (by simp [builtinErrnoDecl])
  | pfnExternMember hid hkind _ _ _ _ _ _ _ =>
      exact absurd hkind (by simp [builtinErrnoDecl])

/-- The `@21` operational field: the stored location value is well formed at
    any consumer cursor that bounds the registry-reserved addresses. -/
theorem builtinErrno_operational :
    ExternOperationalSafe builtinErrnoDecl builtinErrnoImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl
    exact absurd himpl (by simp [builtinErrnoImpl])
  · intro implPfn himpl
    exact absurd himpl (by simp [builtinErrnoImpl])
  · intro v himpl cfg id _hwf hlookup hbelow
    have hv : v = Value.loc errnoAddr := by
      have h := himpl
      simp [builtinErrnoImpl] at h
      exact h.symm
    subst hv
    refine wfValue.loc (hbelow errnoAddr ⟨id, ?_⟩)
    rw [hlookup, himpl]
  · intro implFn himpl
    exact absurd himpl (by simp [builtinErrnoImpl])

/-- The complete trusted boundary spec for the `@21` `errno` reference extern:
    the first trusted `extern ref` entry. -/
theorem builtinErrnoSpec : ExternBoundarySpec builtinErrnoDecl builtinErrnoImpl where
  declFR := builtinErrno_declFR
  callFR := builtinErrno_callFR
  declSingle := builtinErrno_declSingle
  callSingle := builtinErrno_callSingle
  operational := builtinErrno_operational

end ExternProofs
