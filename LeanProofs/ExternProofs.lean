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

/-- The exact computation performed by `builtinAbsPfn` on an integer argument. -/
private theorem builtinAbsPfn_num (env : VarEnv) (n : Int) (mem : Memory) :
    builtinAbsPfn env (Value.num n) mem = .ok (Value.num (Int.ofNat n.natAbs)) :=
  rfl

/-- `builtinAbsPfn` succeeds only on integer arguments, returning the integer
    absolute value as a clean `Value.num`. -/
private theorem builtinAbsPfn_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : builtinAbsPfn env vArg mem = .ok vRaw) :
    ∃ n : Int, vArg = Value.num n ∧ vRaw = Value.num (Int.ofNat n.natAbs) := by
  cases vArg with
  | num n =>
      simp only [builtinAbsPfn, Except.ok.injEq] at h
      exact ⟨n, rfl, h.symm⟩
  | _ => simp [builtinAbsPfn] at h

/-- Helper 1: `builtinAbsPfn` is a function of its integer argument, so equal
    integer inputs produce equal outputs. -/
private theorem builtinAbsPfn_output_eq_of_arg_eq
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
  refine ⟨?_, ?_, ?_⟩
  · -- impure `fn` branch: `builtinAbsImpl` is a `pfn`, so this is vacuous.
    intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinAbsImpl] at himpl
  · -- pure `pfn` branch: the returned raw value is a well-formed `num`.
    intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinAbsImpl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨n, _harg, hraw⟩ := builtinAbsPfn_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · -- `val` branch: impossible.
    intro v himpl _ _
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
  obtain ⟨n, harg, hraw⟩ := builtinAbsPfn_ok_shape hrun
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
  | fnRegularExternBody _ hkind _ _ _ _ _ _ _ => simp [builtinAbsDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures tenv
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
declaration.  The impure mirror (`fnExternMember`) is the symmetric follow-up:
its `regularExternBody` constructor and two-run FR fan-out need the same pin
threaded through the `Fn` static source and providers. -/

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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrun _hpc
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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
              typecheckExternPfn ctx 12 "x" Typ.int false argPred builtinAbsRetSpec = .ok res := by
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
    ∃ argPred : SyntaxPredicate,
      postExpr = Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec := by
  cases htyped with
  | pfn _htc => exact ⟨_, rfl⟩

/-- The `abs` declaration's extern closure value is well-typed at the declared
    `parrow` type.  The captured runtime environment `ρ` types against the
    captured type environment `VarTypeEnv.toCaptured ctx.varEnv` via the runtime
    instantiation of `ctx` (mirrors `stepFR_pfn`'s `peClosure` `henv`/`hcover`
    blocks, using the extern constructor which needs no `toPExpr`). -/
private theorem builtinAbs_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec) ρ)
      (builtinAbsDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinAbsRetSpec) ctx.pc
        [builtinAbsExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (htcl := by simp [builtinAbsExternClosure])
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
    {argPred : SyntaxPredicate} {argQt : QTyp}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinAbsDeclResult ctx argQt).qualType μ θ
      (Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinAbsDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt) 12 "x" "x" Typ.int builtinAbsRetSpec ρ
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
    cf = cᵢ ∧ ∃ argPred : SyntaxPredicate,
      o = Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinAbsDecl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinAbsDecl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "x" := by
        have h := hargName; simp [builtinAbsDecl] at h; exact h.symm
      have hretSpec' : retSpec = builtinAbsRetSpec := by
        have h := hretSpec; simp [builtinAbsDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, by simpa [builtinAbsDecl] using hval⟩

/-- The `abs` single-run declaration-boundary field.  Mirrors `callSingle`'s
    `ExternBoundarySinglePost` assembly (`tm' = tm`, `θ' = θ`, `ctxAfter = ctx`,
    `PreservesInherited…refl`, `FreshClean…vacuous`), with the extern closure's
    `QTypRespectsTagMeaning` / `valueHasETyp` / `valueConsistentWithRegime`
    obligations discharged by `QTypRespectsTagMeaning_pfn_extern` and the two
    shared extern-closure helpers above. -/
theorem builtinAbs_declSingle : ExternDeclBoundarySingle builtinAbsDecl builtinAbsImpl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinAbs_decl_shape htyped
  obtain ⟨hcf, argPred, ho⟩ := builtinAbs_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinAbsDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 12 "x" Typ.int (parseReturnType builtinAbsRetSpec)
      ctx.pc builtinAbsRetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "x" (Expr.externPfn 12 "x" Typ.int false argPred builtinAbsRetSpec) ρ := by
    rw [ho]
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinAbs_decl_shape htyped
  obtain ⟨argPredT, hpostExpr⟩ := builtinAbs_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinAbs_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinAbs_declRun_shape hrun₁.run
  -- Both outputs are the closure of the shared `postExpr`, hence share `argPredT`.
  have ho₀ : o₀ = Value.peClosure "x"
      (Expr.externPfn 12 "x" Typ.int false argPredT builtinAbsRetSpec) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "x"
      (Expr.externPfn 12 "x" Typ.int false argPredT builtinAbsRetSpec) ρ₁ := by
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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    the read dependency `captures: { a :> (int :> clean {}) }` (`doc/extern-env-deps.md`).
    This is the trusted contract under which `@11`'s clean `max a b` result is
    fault-robust: the captured `a` is a declared clean integer dependency.  It is a
    *distinct* declaration from `builtinMax11Decl` (captures `[]`): the captures=`[]`
    declaration cannot close the relational call boundary (that was the gap), and a
    top-level declaration with this `captures` list is not produced by the current AST
    (`doc/extern-env-deps-plan.md`), so only the call-boundary field is proved here. -/
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

/-- Proof-side copy of the interpreter's inner-`max` implementation (`Main.innerMaxImpl`):
    read the captured outer argument `a`, return `max a b`. -/
def builtinMax11Pfn : VarEnv → Value → Memory → Except ExternError Value
  | unifiedEnv, Value.num b, _m =>
      match VarEnv.lookup unifiedEnv "a" with
      | some (Value.num a) => .ok (Value.num (max a b))
      | _ => .error (.implFailure 11 "captured `a` missing or not an int")
  | _, _, _ => .error (.implFailure 11 "expected int argument")

/-- Runtime implementation shape for the inner-`max` extern (`@11`). -/
def builtinMax11Impl : ExternImpl :=
  .pfn builtinMax11Pfn

/-- `builtinMax11Pfn` succeeds only on an integer argument `b` with a captured
    integer `a`, returning the clean `Value.num (max a b)`. -/
private theorem builtinMax11Pfn_ok_shape
    {env : VarEnv} {vArg : Value} {mem : Memory} {vRaw : Value}
    (h : builtinMax11Pfn env vArg mem = .ok vRaw) :
    ∃ a b : Int, vArg = Value.num b ∧ VarEnv.lookup env "a" = some (Value.num a) ∧
      vRaw = Value.num (max a b) := by
  cases vArg with
  | num b =>
      simp only [builtinMax11Pfn] at h
      cases ha : VarEnv.lookup env "a" with
      | none => rw [ha] at h; simp at h
      | some va =>
          cases va with
          | num a =>
              rw [ha] at h
              simp only [Except.ok.injEq] at h
              exact ⟨a, b, rfl, rfl, h.symm⟩
          | _ => rw [ha] at h; simp at h
  | _ => simp [builtinMax11Pfn] at h

/-- The inner-`max` extern (`@11`) satisfies the operational-safety contract: the
    pure branch returns a well-formed `Value.num`; the impure and value branches are
    impossible by `ExternImpl` constructor discrimination. -/
theorem builtinMax11Impl_operationalSafe :
    ExternOperationalSafe builtinMax11Decl builtinMax11Impl := by
  refine ⟨?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [builtinMax11Impl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv _harg
    simp only [builtinMax11Impl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    obtain ⟨a, b, _harg, _ha, hraw⟩ := builtinMax11Pfn_ok_shape hrun
    rw [hraw]
    exact wfValue.num _
  · intro v himpl _ _
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
              typecheckExternPfn ctx 11 "b" Typ.int false argPred builtinMax11RetSpec = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternPfn_ok_res_eq ctx 11 "b" Typ.int false argPred builtinMax11RetSpec res htcPfn
          exact ⟨argQt, hres⟩

private theorem builtinMax11_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl builtinMax11Decl postExpr ctx res) :
    ∃ argPred : SyntaxPredicate,
      postExpr = Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec := by
  cases htyped with
  | pfn _htc => exact ⟨_, rfl⟩

private theorem builtinMax11_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec) ρ)
      (builtinMax11DeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec) ρ)
      (ETyp.parrow Typ.int (parseReturnType builtinMax11RetSpec) ctx.pc
        [builtinMax11ExternClosure ctx argQt])
  refine valueHasETyp.peClosure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (htcl := by simp [builtinMax11ExternClosure])
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
    {argPred : SyntaxPredicate} {argQt : QTyp}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (builtinMax11DeclResult ctx argQt).qualType μ θ
      (Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, builtinMax11DeclResult]) (.intro ?_)
  apply deepValueQTypProperty.peClosure_extern (argQt := argQt) 11 "b" "b" Typ.int builtinMax11RetSpec ρ
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
    cf = cᵢ ∧ ∃ argPred : SyntaxPredicate,
      o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec) cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [builtinMax11Decl] at h
  | fn hfacts => have h := hfacts.kind_fn; simp [builtinMax11Decl] at h
  | pfn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "b" := by
        have h := hargName; simp [builtinMax11Decl] at h; exact h.symm
      have hretSpec' : retSpec = builtinMax11RetSpec := by
        have h := hretSpec; simp [builtinMax11Decl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, by simpa [builtinMax11Decl] using hval⟩

theorem builtinMax11_declSingle : ExternDeclBoundarySingle builtinMax11Decl builtinMax11Impl := by
  intro postExpr ctx res predSat tm htyped hpredlaws hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg hrun _hpc
  obtain ⟨argQt, hres⟩ := builtinMax11_decl_shape htyped
  obtain ⟨hcf, argPred, ho⟩ := builtinMax11_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = ctx := by rw [hres]; simp [ctxAfter, builtinMax11DeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_pfn_extern tm ctx 11 "b" Typ.int (parseReturnType builtinMax11RetSpec)
      ctx.pc builtinMax11RetSpec (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.peClosure "b" (Expr.externPfn 11 "b" Typ.int false argPred builtinMax11RetSpec) ρ := by
    rw [ho]
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ hrun₀ hrun₁
  obtain ⟨argQt, hres⟩ := builtinMax11_decl_shape htyped
  obtain ⟨argPredT, hpostExpr⟩ := builtinMax11_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := builtinMax11_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := builtinMax11_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.peClosure "b"
      (Expr.externPfn 11 "b" Typ.int false argPredT builtinMax11RetSpec) ρ₁ := by
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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  obtain ⟨a, b, harg, ha, hraw⟩ := builtinMax11Pfn_ok_shape hrun
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
  | fnRegularExternBody _ hkind _ _ _ _ _ _ _ => simp [builtinMax11Decl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures tenv
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
    θ cf o _hθwf _hwfCtx hric _hreg hcons _hwfcfg hrun _hpc
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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  obtain ⟨a, b, harg, ha, hraw⟩ := builtinMax11Pfn_ok_shape hrun
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
  | fnRegularExternBody _ hkind _ _ _ _ _ _ _ => simp [builtinMax11CapturesDecl] at hkind
  | pfnExternMember hid hkind htyp harg hret hcap hpin hbody happly =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures tenv
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
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hrespects, hpredlaws⟩, hpredlaws, hrespects,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end ExternProofs
