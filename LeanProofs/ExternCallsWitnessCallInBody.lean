import LeanProofs.ExternCallsWitnessInt
import LeanProofs.ExternCallsWitnessClosed

/-!
# An extern function declared outside a function and called in its body

    let lo = 3 in
    let g = extern pfn @250 n : (int :> clean {}) -> ((int :> poisoned { 0, v => v >= lo })) in
    let f = fn u : int => (let y = g 5 in if y >= lo then 1 else x) : int in
    f 0

typed in the context `K` of `ExternCallsWitnessInt` (a poisoned integer `x`,
every tag of `@250` assigned true) as a clean `int` (`typed_clean`). The
function `f` captures `g`, `lo` (number 1) and `x`; its type has one member.
The run enters the body of `f` through that member: the captured types type
the closure's environment, `g`'s closure included (`valueHasETyp.peClosure_extern`).
In the body the call `g 5` is typed against the one member of the type of
`g`, allocates tag 0, whose guard `v >= lo` reads `lo` with number 1
(`capE`), and the conditional `y >= lo` is matched to that tag.

* The trusted entry of `g` (`gSpec`, registry `gReg m`): the implementation
  returns the value `m` whatever the argument (`gImpl m`), as in
  `ExternCallsWitnessIntCall`.
* `programTable_eq`, `laws_program`: the table of the program is the guard
  over `capE`, on which `loSat` is lawful; `match_iff_lawful`: the laws fix
  any relation there.
* `call_reached`: a run reaches the call in the body of `f`, which returns
  `m` and allocates the guard over `capE`.
* The view `βe m n` gives `lo` 3, `g` its closure, `u` 0 and `y` the value
  `m` (`tests`, `view_needed`). *Match* under `loSat (βe m n)` holds exactly
  when `3 ≤ m` (`match_iff`); *agreement* holds for two runs with the same
  registry (`agree`).
* `same_return`: for `3 ≤ m`, two runs from any `x` return the same value,
  with every premise of the theorem proved. `true_5`: the registry returns 5;
  the runs from `x = 0` and `x = 1` return 1. `fails_0`: the registry returns
  0; the program is typed clean, the runs return 0 and 1, and no relation and
  view meet the laws, the premise on tests and *match* (`no_premises_lt`).
-/

open Std LeanPoison ExternProofs

namespace ExternCallsWitness

namespace CallInBody

open IntGuard (K loGuard loBody loNum intQt loSat loTmOf pinSelectsOf)

/-! ## The entry -/

/-- The return of `g`: a poisoned integer with the guard `v => v >= lo`. -/
def gRet : ExternReturn := .simple .int true loGuard

/-- `extern pfn @250 n : (int :> clean {}) -> ((int :> poisoned { 0, v => v >= lo }))` -/
def gD : Expr := .externPfn 250 "n" .int false .noPred gRet []

/-- The declaration of `g`. -/
def gDecl : ExternDeclaration := pfnExternDecl 250 "n" .int gRet []

/-- The implementation: the value `m`, whatever the argument. -/
def constImpl (m : Int) : VarEnv → Value → Memory → Except ExternError Value :=
  fun _ _ _ => .ok (.num m)

/-- The implementation of `g` as an entry of a registry. -/
def gImpl (m : Int) : ExternImpl := .pfn (constImpl m)

/-- The output of a call of `g`: the value `m`, from an unchanged configuration. -/
private theorem g_callRun_output {m : Int} {entry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun gDecl (gImpl m) entry res cf o) :
    o = Value.num m ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [gDecl, pfnExternDecl] at h
  | pfn hfacts =>
      refine ⟨?_, hfacts.output_config⟩
      rcases hfacts.impl_success with
        ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, hrunImpl, hvalRet⟩
      have hret : retSpec = gRet := by
        simp only [gDecl, pfnExternDecl] at hretSpec
        exact (Option.some.inj hretSpec).symm
      subst hret
      simp only [gImpl, ExternImpl.pfn.injEq] at himpl
      subst himpl
      simp only [constImpl, Except.ok.injEq] at hrunImpl
      subst hrunImpl
      simpa [gRet, validateExternReturn, valueMatchesTyp] using hvalRet.symm

private theorem g_facts {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call gDecl typedExpr entry res) :
    SimplePfnCallFacts entry.bodyCtx res true :=
  simplePfnCall_facts (spred := loGuard) rfl rfl htyped

private theorem g_callSingle (m : Int) : ExternCallBoundarySingle gDecl (gImpl m) := by
  intro typedExpr res predSat β tm entry ctx htyped _hpredlaws hframe hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx htagBnd hric _hreg hcons _hwfcfg hrdIn hrun hmatch _hpc
  have hf : SimplePfnCallFacts ctx res true := g_facts htyped
  obtain ⟨ho, hcf⟩ := g_callRun_output hrun
  have hboc : entry.bodyOutputConfig cf = entry.bodyConfig := by
    rw [hcf]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  obtain ⟨tm', hext, hbnd', hresp', hwithin⟩ := hf.tagMeaning tm hTmBounded
  have hvt : valueHasETyp θ o res.qualType.etyp := by
    rw [ho, hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm', ⟨hext, hbnd', ?_, hresp', TagFrame.laws_of_within hframe hwithin, hwithin⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, hvt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show EnvRespectsTagMeaning tm' ctx.varEnv res.memEnv'
    rw [hf.memEnv]
    exact EnvRespectsTagMeaning_mono hext hwfTm
  · rw [hboc]
    refine ⟨fun l a hl => ?_, fun hx => hric.2 hx⟩
    show res.memEnv'.contains l ∧ _
    rw [hf.memEnv]; exact hric.1 l a hl
  · rw [hboc]; exact hf.consistent htagBnd hcons
  · have h := valueConsistent_of_callMatches hf.guard_mem hmatch hvt hf.notfun
    simpa [ExternCallEntry.bodyOutputConfig, ctxAfter] using h
  · rw [hboc]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · intro l _qt hnot hlookup _hclean
    rw [hf.memEnv] at hlookup
    exact absurd (memEnv_contains_of_lookup_some ctx.memEnv l _qt hlookup) hnot
  · rw [hboc, hf.declared]; exact hrdIn

private theorem g_callFR (m : Int) : ExternCallBoundaryFR gDecl (gImpl m) := by
  intro postExpr typedExpr₀ _typedExpr₁ res predSat₀ predSat₁ β₀ β₁ tm entry₀ entry₁ ctx hctx₁
    htyped₀ _htyped₁ _hpredlaws₀ _hpredlaws₁ hframe₀ hframe₁ hwfTm hTmBounded θ₀ θ₁ hbody
    cf₀ cf₁ o₀ o₁ hrun₀ hrun₁ hmatch₀ hmatch₁ hagree
  have hf : SimplePfnCallFacts ctx res true := g_facts htyped₀
  obtain ⟨ho₀, hcf₀⟩ := g_callRun_output hrun₀
  obtain ⟨ho₁, hcf₁⟩ := g_callRun_output hrun₁
  have hboc₀ : entry₀.bodyOutputConfig cf₀ = entry₀.bodyConfig := by
    rw [hcf₀]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  have hboc₁ : entry₁.bodyOutputConfig cf₁ = entry₁.bodyConfig := by
    rw [hcf₁]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  obtain ⟨tm', hext, hbnd', hresp', hwithin⟩ := hf.tagMeaning tm hTmBounded
  have hlaws₀' := TagFrame.laws_of_within hframe₀ hwithin
  have hlaws₁' := TagFrame.laws_of_within hframe₁ hwithin
  have hvt₀ : valueHasETyp θ₀ o₀ res.qualType.etyp := by
    rw [ho₀, hf.etyp]; exact valueHasETyp.num _
  have hvt₁ : valueHasETyp θ₁ o₁ res.qualType.etyp := by
    rw [ho₁, hf.etyp]; exact valueHasETyp.num _
  have hwfTm' : wfTagMeaningCtx tm' (ctxAfter ctx res) := by
    show EnvRespectsTagMeaning tm' ctx.varEnv res.memEnv'
    rw [hf.memEnv]
    exact EnvRespectsTagMeaning_mono hext hwfTm
  have hvc₀ := valueConsistent_of_callMatches hf.guard_mem hmatch₀ hvt₀ hf.notfun
  have hvc₁ := valueConsistent_of_callMatches hf.guard_mem hmatch₁ hvt₁ hf.notfun
  have hrai := resultAgreesIfClean_of_callAgrees (μ₀ := entry₀.bodyConfig.memory)
    (μ₁ := entry₁.bodyConfig.memory) (θ₀ := θ₀) (θ₁ := θ₁) (predSat₀ := predSat₀)
    (predSat₁ := predSat₁)
    hf.guard_mem (hf.poison_true rfl) hf.notfun hf.notref hagree
  have hmem₀ : (entry₀.bodyOutputConfig cf₀).memory = cf₀.memory := rfl
  have hmem₁ : (entry₁.bodyOutputConfig cf₁).memory = cf₁.memory := rfl
  rw [hboc₀] at hmem₀
  rw [hboc₁] at hmem₁
  rw [hboc₀, hboc₁]
  refine ⟨tm', ⟨hext, hbnd', hwfTm', hresp', hlaws₀', hwithin⟩, hlaws₁', hresp',
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩, hvt₀, hvt₁, hwfTm',
    hf.wfCtx hbody.wfCtx, hf.tagBounded hbody.tagBounded, hbody.wfConfig₀, ?_,
    hf.runtime hbody.runtime₀, ?_, hf.regimeConsistent hbody.regime,
    hf.consistent hbody.tagBounded hbody.consistent₀, ?_,
    hf.agree hbody.tagBounded ?_, ?_, ?_, hrai, ?_, ?_⟩
  · exact hbody.wfConfig₁
  · exact hf.runtime hbody.runtime₁
  · exact hf.consistent hbody.tagBounded hbody.consistent₁
  · exact hbody.agree
  · rw [hmem₀]; exact hvc₀
  · rw [hmem₁]; exact hvc₁
  · rw [hf.declared]; exact hbody.reserved₀
  · rw [hf.declared]; exact hbody.reserved₁

/-- `g` returns an integer, which is well formed. -/
private theorem gImpl_operationalSafe (m : Int) : ExternOperationalSafe gDecl (gImpl m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [gImpl] at himpl
  · intro implPfn himpl _env _vArg _mem _addr vRaw hrun _hmem _henv _harg
    simp only [gImpl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    simp only [constImpl, Except.ok.injEq] at hrun
    subst hrun
    exact wfValue.num m
  · intro v himpl _ _
    simp [gImpl] at himpl
  · intro implFn himpl
    simp [gImpl] at himpl

/-- The trusted entry of `g`. -/
theorem gSpec (m : Int) : ExternBoundarySpec gDecl (gImpl m) where
  declFR := pfnExternDecl_declFR 250 "n" Typ.int gRet [] (gImpl m)
  callFR := g_callFR m
  declSingle := pfnExternDecl_declSingle 250 "n" Typ.int gRet [] (gImpl m)
  callSingle := g_callSingle m
  operational := gImpl_operationalSafe m

/-- The trusted registry that holds `g` with the value `m`. -/
def gReg (m : Int) : TrustedRegistry := [⟨gDecl, gImpl m, gSpec m⟩]

/-- The runtime registry. -/
def regC (m : Int) : ExternRegistry := emptyExternRegistry.insert 250 (gImpl m)

/-- The runtime registry of `gReg m` is `regC m`. -/
theorem gReg_runtime (m : Int) : (gReg m).toRuntimeRegistry = regC m := rfl

private theorem regC_get (m : Int) : (regC m).get? 250 = some (gImpl m) := by simp [regC]

private theorem regC_get' (m : Int) : (regC m)[250]? = some (gImpl m) := by simp [regC]

private theorem regC_noLoc {m : Int} {id : ExternId} {a : Address}
    (h : (regC m).get? id = some (.val (.loc a))) : False := by
  by_cases hid : id = 250
  · subst hid; simp [regC, gImpl] at h
  · simp [regC, emptyExternRegistry, Ne.symm hid] at h

/-! ## The program -/

/-- `g 5` -/
def call : Expr := .app (.var "g") (.num 5)

/-- `let y = g 5 in if y >= lo then 1 else x` -/
def bodyF : Expr := .vlet "y" call IntGuard.test

/-- `fn u : int => (let y = g 5 in if y >= lo then 1 else x) : int` -/
def fnF : Expr := .fn "u" .int bodyF .int

/-- `f 0` -/
def callF : Expr := .app (.var "f") (.num 0)

/-- `let f = fn u : int => ... in f 0` -/
def letF : Expr := .vlet "f" fnF callF

/-- `let g = extern pfn @250 ... in let f = ... in f 0` -/
def letG : Expr := .vlet "g" gD letF

/-- `let lo = 3 in let g = ... in let f = ... in f 0` -/
def prog : Expr := .vlet "lo" (.num 3) letG

/-- The starting state of a run from `x = n`, with the registry returning `m`. -/
def cfgE (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regC m }

/-- The closure a declaration of `g` evaluates to under `env`. -/
def gClo (env : VarEnv) : Value := .peClosure "n" gD env

/-! ## Impure arrows with one member -/

private def isArrow1 : ETyp → Bool
  | .arrow _ _ _ [_] => true
  | _ => false

private def arrowS1 : ETyp → Typ
  | .arrow a _ _ _ => a
  | _ => Typ.int

private def arrowS2 : ETyp → Typ
  | .arrow _ b _ _ => b
  | _ => Typ.int

private def arrowP : ETyp → Poison
  | .arrow _ _ p _ => p
  | _ => false

private def arrowM : ETyp → FnTClosure
  | .arrow _ _ _ [m] => m
  | _ => .regular "" .unit []

private theorem arrow1_eq {E : ETyp} (h : isArrow1 E = true) :
    E = .arrow (arrowS1 E) (arrowS2 E) (arrowP E) [arrowM E] := by
  match E, h with
  | .arrow _ _ _ [_], _ => rfl

private def regTenv : FnTClosure → CapturedVarEnv
  | .regular _ _ t => t
  | .extern _ _ _ _ _ _ _ => []

/-! ## The typing -/

private def rLo : TypeResult := okVal (typecheckExpr K (.num 3) 58)

/-- The context of the body of `let lo`. -/
private def K1 : TypeContext :=
  { ctxAfter K rLo with
    varEnv := K.varEnv.update "lo" rLo.qualType,
    bindEnv := K.bindEnv.insert "lo" rLo.nextBind',
    nextBind := rLo.nextBind' + 1 }

private def rG : TypeResult := okVal (typecheckExpr K1 gD 56)

/-- The context of the body of `let g`. -/
private def K2 : TypeContext :=
  { ctxAfter K1 rG with
    varEnv := K1.varEnv.update "g" rG.qualType,
    bindEnv := K1.bindEnv.insert "g" rG.nextBind',
    nextBind := rG.nextBind' + 1 }

private def rF : TypeResult := okVal (typecheckExpr K2 fnF 54)

/-- The context of the call `f 0`. -/
private def K3 : TypeContext :=
  { ctxAfter K2 rF with
    varEnv := K2.varEnv.update "f" rF.qualType,
    bindEnv := K2.bindEnv.insert "f" rF.nextBind',
    nextBind := rF.nextBind' + 1 }

/-- The argument and the function of the call `f 0`. -/
private def rArg : TypeResult := okVal (typecheckExpr K3 (.num 0) 52)
private def rFun : TypeResult := okVal (typecheckExpr (ctxAfter K3 rArg) (.var "f") 52)

/-- The type of `f` at the call. -/
private def EF : ETyp := rFun.qualType.etyp

/-- The context of the body of `f`, entered through the one member of its type. -/
private def KB : TypeContext :=
  fnBodyCtx K3 rArg rFun (arrowP EF) "u" (regTenv (arrowM EF)) (rFun.nextTag', rFun.nextLoc')
    rFun.nextBind'

private def rC : TypeResult := okVal (typecheckExpr KB call 49)

/-- The context of the conditional: `y` bound to the result of the call. -/
private def L3 : TypeContext :=
  { ctxAfter KB rC with
    varEnv := KB.varEnv.update "y" rC.qualType,
    bindEnv := KB.bindEnv.insert "y" rC.nextBind',
    nextBind := rC.nextBind' + 1 }

/-- The typing of the program. -/
def rootRes : TypeResult := okVal (typecheckExpr K prog 60)

/-- The member result of the call `g 5`. -/
private def rM : TypeResult := iRes KB (.var "g") (.num 5) 47

/-- The captured types of the one member of the type of `g`: `lo` a clean
    integer with number 1, and `x` a poisoned integer. -/
def gCapE : CapturedVarEnv := [("lo", intQt, loNum), ("x", pInt, 0)]

/-- The type of `g`: a pure function type with one extern member. -/
def gQtE : QTyp :=
  { etyp := .parrow .int (parseReturnType gRet) false [.extern 250 "n" gRet gCapE intQt []],
    poison := false, pred := .noPred }

/-- The captured types of the one member of the type of `f`: `g` with its type
    and number 2, `lo` with number 1, and `x`. -/
def tenvE : CapturedVarEnv := [("g", gQtE, 2), ("lo", intQt, loNum), ("x", pInt, 0)]

/-- The captured environment of the guard the call makes: `lo` with its number
    1 and the extern's parameter `n` with the number of the call, 5. -/
def capE : CapturedVarEnv := [("lo", intQt, loNum), ("n", intQt, 5), ("x", pInt, 0)]

/-- The allocation of the guard at the call. -/
def gAlloc : TagAlloc := { tag := 0, argName := "v", body := loBody, capEnv := capE }

private def logOk (log : List TagAlloc) : Bool :=
  match log with
  | [a] => a.tag == 0 && a.argName == "v" && a.body == loBody && decide (a.capEnv = capE)
  | _ => false

private theorem logOk_eq {log : List TagAlloc} (h : logOk log = true) : log = [gAlloc] := by
  unfold logOk at h
  split at h
  · rename_i a
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rcases a with ⟨t, an, b, c⟩
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  · simp at h

/-- `y >= lo` is matched to tag 0 at the conditional of the body. -/
private def selects : Bool :=
  match matchGuard IntGuard.cond L3.memEnv L3.varEnv L3.bindEnv 47 with
  | .ok (k, _) => k == 0
  | .error _ => false

/-- What the typing gives, as a Boolean summary evaluated by the kernel. -/
private def facts : Bool :=
  isOkB (typecheckExpr K prog 60) &&
  isOkB (typecheckExpr K (.num 3) 58) &&
  isOkB (typecheckExpr K1 gD 56) &&
  isOkB (typecheckExpr K2 fnF 54) &&
  isOkB (typecheckExpr K3 (.num 0) 52) &&
  isOkB (typecheckExpr (ctxAfter K3 rArg) (.var "f") 52) &&
  isArrow1 EF &&
  isOkB (fnApply K3 rArg rFun (arrowS1 EF) (arrowS2 EF) (arrowP EF) 52 (arrowM EF)
    (rFun.nextTag', rFun.nextLoc') rFun.nextBind') &&
  decide (regTenv (arrowM EF) = tenvE) &&
  isOkB (typecheckExpr KB call 49) &&
  isOkB (typecheckExpr KB (.num 5) 47) &&
  isOkB (typecheckExpr (ctxAfter KB (iArg KB (.num 5) 47)) (.var "g") 47) &&
  isParrow1 (iFun KB (.var "g") (.num 5) 47).qualType.etyp &&
  (rFun.nextBind' == 4) &&
  (rC.nextBind' == 6) &&
  (rM.regime'.lookup? 0 == some true) &&
  (L3.regime.lookup? 0 == some true) &&
  logOk rM.tagLog' &&
  logOk rootRes.tagLog' &&
  decide (rM.qualType.pred = .guardClosure 0 "v" loBody capE) &&
  decide (rM.qualType.etyp = .int) &&
  decide (rC.qualType.pred = .guardClosure 0 "v" loBody capE) &&
  selects &&
  decide (rootRes.qualType.etyp = .int) &&
  (rootRes.qualType.poison == false)

private theorem facts_ok : facts = true := by decide +kernel

/-- The member of the type of `f` is the closure's parameter and body. -/
private theorem member : arrowM EF = .regular "u" bodyF (regTenv (arrowM EF)) := by
  decide +kernel

/-- The member of the type of `g` at the call, and its application. -/
private theorem memberG :
    let E := (iFun KB (.var "g") (.num 5) 47).qualType.etyp
    parrowM E = .extern 250 "n" gRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
      (extParts (parrowM E)).2.2 ∧
    isOkB (pfnApply KB (iArg KB (.num 5) 47) (iFun KB (.var "g") (.num 5) 47)
      (parrowS1 E) (parrowS2 E) (parrowP E) 47 (parrowM E) (iCursor KB (.var "g") (.num 5) 47)
        (iBind KB (.var "g") (.num 5) 47)) = true := by
  decide +kernel

/-- The facts of the typing, by name. -/
private structure Facts : Prop where
  root : typecheckExpr K prog 60 = .ok rootRes
  lo : typecheckExpr K (.num 3) 58 = .ok rLo
  g : typecheckExpr K1 gD 56 = .ok rG
  fT : typecheckExpr K2 fnF 54 = .ok rF
  arg : typecheckExpr K3 (.num 0) 52 = .ok rArg
  fn : typecheckExpr (ctxAfter K3 rArg) (.var "f") 52 = .ok rFun
  ef : EF = .arrow (arrowS1 EF) (arrowS2 EF) (arrowP EF) [arrowM EF]
  ap : fnApply K3 rArg rFun (arrowS1 EF) (arrowS2 EF) (arrowP EF) 52 (arrowM EF)
    (rFun.nextTag', rFun.nextLoc') rFun.nextBind' = .ok
      (okVal (fnApply K3 rArg rFun (arrowS1 EF) (arrowS2 EF) (arrowP EF) 52 (arrowM EF)
        (rFun.nextTag', rFun.nextLoc') rFun.nextBind'))
  tenv : regTenv (arrowM EF) = tenvE
  c : typecheckExpr KB call 49 = .ok rC
  argG : typecheckExpr KB (.num 5) 47 = .ok (iArg KB (.num 5) 47)
  funG : typecheckExpr (ctxAfter KB (iArg KB (.num 5) 47)) (.var "g") 47 =
    .ok (iFun KB (.var "g") (.num 5) 47)
  shape : isParrow1 (iFun KB (.var "g") (.num 5) 47).qualType.etyp = true
  bFun : rFun.nextBind' = 4
  bC : rC.nextBind' = 6
  regM : rM.regime'.lookup? 0 = some true
  reg3 : L3.regime.lookup? 0 = some true
  logM : rM.tagLog' = [gAlloc]
  logR : rootRes.tagLog' = [gAlloc]
  predM : rM.qualType.pred = .guardClosure 0 "v" loBody capE
  etypM : rM.qualType.etyp = .int
  predC : rC.qualType.pred = .guardClosure 0 "v" loBody capE
  sel : ∃ deps, matchGuard IntGuard.cond L3.memEnv L3.varEnv L3.bindEnv 47 = .ok (0, deps)
  etyp : rootRes.qualType.etyp = .int
  clean : rootRes.qualType.poison = false

private theorem facts_of : Facts := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩ := hf
  refine ⟨eq_okVal h1, eq_okVal h2, eq_okVal h3, eq_okVal h4, eq_okVal h5, eq_okVal h6,
    arrow1_eq h7, eq_okVal h8, h9, eq_okVal h10, eq_okVal h11, eq_okVal h12, h13, h14, h15,
    h16, h17, logOk_eq h18, logOk_eq h19, h20, h21, h22, ?_, h24, h25⟩
  unfold selects at h23
  split at h23
  · rename_i k d heq
    simp at h23
    subst h23
    exact ⟨d, heq⟩
  · simp at h23

/-- The program is typed as a clean `int`. -/
theorem typed_clean :
    typecheck K prog 60 = .ok rootRes ∧
      rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false :=
  ⟨facts_of.root, facts_of.etyp, facts_of.clean⟩

/-- The table of the program: the guard of tag 0 over `capE`. -/
theorem programTable_eq : programTable ∅ rootRes.tagLog' = loTmOf capE := by
  rw [facts_of.logR]
  rfl

/-! ## The runs -/

private def cfg1 (m n : Int) : Config :=
  { cfgE m n with varEnv := (cfgE m n).varEnv.update "lo" (.num 3) }

/-- `g` bound to its closure. -/
private def cfg2 (m n : Int) : Config :=
  { cfg1 m n with varEnv := (cfg1 m n).varEnv.update "g" (gClo (cfg1 m n).varEnv) }

/-- The closure of `f`: its environment holds `x`, `lo` and `g`. -/
private def fClo (m n : Int) : Value := .closure "u" bodyF (cfg2 m n).varEnv

private def cfg3 (m n : Int) : Config :=
  { cfg2 m n with varEnv := (cfg2 m n).varEnv.update "f" (fClo m n) }

/-- The configuration of the body of `f`, called with 0. -/
private def cfgB (m n : Int) : Config :=
  { { cfg3 m n with varEnv := (cfg3 m n).varEnv } with
    varEnv := VarEnv.update (cfg2 m n).varEnv "u" (.num 0), pureMode := false }

/-- `y` bound to the value the call returns, `m`. -/
private def cfgB3 (m n : Int) : Config :=
  { cfgB m n with varEnv := (cfgB m n).varEnv.update "y" (.num m) }

private theorem run_gD (m : Int) (cfg : Config) (hreg : cfg.registry = regC m) :
    terminatesTo gD cfg cfg (gClo cfg.varEnv) :=
  ⟨1, false, by unfold beval; simp [gD, hreg, regC_get', gImpl, gClo]⟩

private theorem run_fnF (m n : Int) : terminatesTo fnF (cfg2 m n) (cfg2 m n) (fClo m n) :=
  ⟨1, false, by unfold beval; simp [fnF, fClo]⟩

private theorem runF (m n : Int) :
    ∀ c, c.varEnv = (cfg3 m n).varEnv → terminatesTo (.var "f") c c (fClo m n) := by
  intro c hc
  exact run_var (by rw [hc]; simp [cfg3, VarEnv.update, VarEnv.lookup])

private theorem run_g (m n : Int) :
    ∀ c, c.varEnv = (cfgB m n).varEnv → terminatesTo (.var "g") c c (gClo (cfg1 m n).varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; simp [cfgB, cfg2, VarEnv.update, VarEnv.lookup, List.lookup])

/-- The call returns `m` and leaves the configuration. -/
private theorem run_call (m n : Int) : terminatesTo call (cfgB m n) (cfgB m n) (.num m) :=
  ⟨5, false, by
    simp [beval, call, cfgB, cfg3, cfg2, cfg1, cfgE, gClo, gD, gRet, VarEnv.lookup,
      VarEnv.update, regC_get', gImpl, constImpl, validateExternReturn, valueMatchesTyp,
      List.lookup]⟩

/-- A run with the value `m ≥ 3` returns 1. -/
theorem run_prog_ge (m n : Int) (hm : 3 ≤ m) :
    terminatesTo prog (cfgE m n) (cfgE m n) (.num 1) := by
  refine ⟨30, false, ?_⟩
  simp [prog, letG, letF, fnF, callF, bodyF, call, gD, gRet, IntGuard.test, IntGuard.cond,
    LeanPoison.beval, bevalFunctionBody, cfgE, regC_get', gImpl, constImpl,
    validateExternReturn, valueMatchesTyp, VarEnv.lookup, VarEnv.update, LeanPoison.evalOp,
    List.lookup, hm]

/-- A run with the value `m < 3` returns `x`. -/
theorem run_prog_lt (m n : Int) (hm : m < 3) :
    terminatesTo prog (cfgE m n) (cfgE m n) (.num n) := by
  refine ⟨30, false, ?_⟩
  simp [prog, letG, letF, fnF, callF, bodyF, call, gD, gRet, IntGuard.test, IntGuard.cond,
    LeanPoison.beval, bevalFunctionBody, cfgE, regC_get', gImpl, constImpl,
    validateExternReturn, valueMatchesTyp, VarEnv.lookup, VarEnv.update, LeanPoison.evalOp,
    List.lookup, Int.not_le.mpr hm]

/-! ## The steps of a run -/

/-- The root step. -/
def V0 (m n : Int) : Step := ⟨K, prog, 60, cfgE m n⟩
private def V1 (m n : Int) : Step := ⟨K1, letG, 58, cfg1 m n⟩
private def V2 (m n : Int) : Step := ⟨K2, letF, 56, cfg2 m n⟩
private def V3 (m n : Int) : Step := ⟨K3, callF, 54, cfg3 m n⟩

/-- The body of `f`, entered through the one member of its type. -/
private def VB (m n : Int) : Step := ⟨KB, bodyF, 51, cfgB m n⟩

/-- The call `g 5`. -/
private def VC (m n : Int) : Step := ⟨KB, call, 49, cfgB m n⟩

/-- The conditional of the body. -/
private def VT (m n : Int) : Step := ⟨L3, IntGuard.test, 49, cfgB3 m n⟩

private theorem env1_lo (m n : Int) : (cfg1 m n).varEnv.lookup "lo" = some (.num 3) := by
  simp [cfg1, cfgE, VarEnv.update, VarEnv.lookup]

private theorem env1_x (m n : Int) : (cfg1 m n).varEnv.lookup "x" = some (.num n) := by
  simp [cfg1, cfgE, VarEnv.update, VarEnv.lookup, List.lookup]

private theorem gCapE_lookup {z : Name} {qt : QTyp} (h : gCapE.lookup z = some qt) :
    (z = "lo" ∧ qt = intQt) ∨ (z = "x" ∧ qt = pInt) := by
  simp only [gCapE, CapturedVarEnv.lookup, List.lookup] at h
  split at h
  · rename_i heq
    simp only [Option.map_some, Option.some.injEq] at h
    exact Or.inl ⟨beq_iff_eq.mp heq, h.symm⟩
  · split at h
    · rename_i heq
      simp only [Option.map_some, Option.some.injEq] at h
      exact Or.inr ⟨beq_iff_eq.mp heq, h.symm⟩
    · simp at h

/-- The closure of `g` has the type of `g`: the captured types of its one member
    type the closure's environment, which holds `lo` and `x`. -/
private theorem g_typed (θ : RealizationMap) (m n : Int) :
    valueHasETyp θ (gClo (cfg1 m n).varEnv) gQtE.etyp := by
  unfold gClo gD
  show valueHasETyp θ _ (.parrow .int (parseReturnType gRet) false
      [.extern 250 "n" gRet gCapE intQt []])
  exact valueHasETyp.peClosure_extern (tenv := gCapE) (memberCap := []) (argQTyp := intQt)
    (htcl := List.mem_singleton_self _)
    (henv := fun z qt v hz hv => by
      rcases gCapE_lookup hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [env1_lo] at hv
        cases hv
        exact .num 3
      · rw [env1_x] at hv
        cases hv
        exact .num n)
    (hcover := fun z qt hz => by
      rcases gCapE_lookup hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, env1_lo m n⟩
      · exact ⟨_, env1_x m n⟩)

private theorem tenv_lookup {z : Name} {qt : QTyp} (h : tenvE.lookup z = some qt) :
    (z = "g" ∧ qt = gQtE) ∨ (z = "lo" ∧ qt = intQt) ∨ (z = "x" ∧ qt = pInt) := by
  simp only [tenvE, CapturedVarEnv.lookup, List.lookup] at h
  split at h
  · rename_i heq
    simp only [Option.map_some, Option.some.injEq] at h
    exact Or.inl ⟨beq_iff_eq.mp heq, h.symm⟩
  · split at h
    · rename_i heq
      simp only [Option.map_some, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨beq_iff_eq.mp heq, h.symm⟩)
    · split at h
      · rename_i heq
        simp only [Option.map_some, Option.some.injEq] at h
        exact Or.inr (Or.inr ⟨beq_iff_eq.mp heq, h.symm⟩)
      · simp at h

/-- The captured types of the member of `f` type the environment of its closure:
    `g` holds the closure of `g` (`g_typed`), `lo` and `x` integers. -/
private theorem typing_tenv (m n : Int) :
    ∃ θ, capturedVarsTypingProperty θ tenvE (cfg2 m n).varEnv := by
  refine ⟨∅, by decide, fun z qt hz => ?_, fun z qt v hz hv => ?_⟩
  · rcases tenv_lookup hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      simp [cfg2, cfg1, cfgE, VarEnv.update, VarEnv.lookup, List.lookup]
  · rcases tenv_lookup hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hv' : v = gClo (cfg1 m n).varEnv := by
        simpa [cfg2, VarEnv.update, VarEnv.lookup, List.lookup] using hv.symm
      subst hv'
      exact g_typed ∅ m n
    · simp [cfg2, cfg1, cfgE, VarEnv.update, VarEnv.lookup, List.lookup] at hv
      subst hv
      exact valueHasETyp.num _
    · simp [cfg2, cfg1, cfgE, VarEnv.update, VarEnv.lookup, List.lookup] at hv
      subst hv
      exact valueHasETyp.num _

/-- The parts of the call `f 0`: the argument, the function, and the body of
    `f` entered through the one member of its type. -/
private theorem call_sub {m n : Int} {s' : Step} (h : SubStep (V3 m n) s') :
    noAppIte s'.e = true ∨ s' = VB m n := by
  have hh := SubStep.app_inv (ctx := K3) (e1 := .var "f") (e2 := .num 0) (F := 54)
    (cfg := cfg3 m n) h
  clear h
  obtain ⟨G, hG, h⟩ := hh
  obtain rfl : G = 52 := by omega
  rcases h with h | h | h | h
  · subst h; exact Or.inl rfl
  · obtain ⟨_, _, _, _, _, rfl⟩ := h; exact Or.inl rfl
  · obtain ⟨H', r2, r1, rb, c2, c1, v2, x, body, env', st1, st2, p, tcls, tenv, cursor, bn,
      hH, h2, hr2, h1, hr1, hety, hthr, rfl⟩ := h
    obtain rfl : H' = 51 := by omega
    obtain rfl := ok_inj h2 facts_of.arg
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 (run_num (cfg3 m n) 0)
    subst hc2
    obtain rfl := ok_inj h1 facts_of.fn
    obtain ⟨hc1, hv⟩ := terminatesTo_det hr1 (runF m n _ rfl)
    subst hc1
    simp only [fClo, Value.closure.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    rw [show rFun.qualType.etyp = _ from facts_of.ef] at hety
    simp only [ETyp.arrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨hm, rfl, rfl, _⟩ := ThreadedAt.single_inv hthr
    have ht : tenv = regTenv (arrowM EF) := by rw [← hm]; rfl
    subst ht
    exact Or.inr rfl
  · obtain ⟨H', r2, r1, rb, c2, c1, v2, x, body, pbody, env', st1, st2, p, tcls, tenv, cursor,
      bn, hH, h2, hr2, h1, hr1, _⟩ := h
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 (run_num (cfg3 m n) 0)
    subst hc2
    have := terminatesTo_det hr1 (runF m n _ rfl)
    simp [fClo] at this

/-- The call `f 0` makes no extern call itself: `f` evaluates to a closure whose
    body is not an extern function. -/
private theorem call_noCall {m n : Int} {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt (V3 m n) effects entry res cf o) : False := by
  have hh := ExternCallAt.app_inv (ctx := K3) (e1 := .var "f") (e2 := .num 0) (F := 54)
    (cfg := cfg3 m n) h
  clear h
  obtain ⟨G, _, h⟩ := hh
  rcases h with
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env', id, argTyp, argPoison, argPred, retSpec, captures,
      memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, bn, implFn,
      _, hr2, _, hr1, _⟩ |
    ⟨r2, r1, c2, c1, v2, x, y, env', id, argTyp, argPoison, argPred, retSpec, effs, captures,
      _, hr2, _, hr1⟩
  · have := terminatesTo_det hr1 (runF m n _ rfl)
    simp [fClo] at this
  · have := terminatesTo_det hr1 (runF m n _ rfl)
    simp [fClo, bodyF] at this

private theorem toPExpr?_gD : Expr.toPExpr? gD = none := rfl

/-- The steps of the call `g 5`: the argument and the function, and no body,
    since the closure called is the extern's. -/
private theorem callG_sub {m n : Int} {s' : Step} (h : SubStep (VC m n) s') :
    noAppIte s'.e = true := by
  have hh := SubStep.app_inv (ctx := KB) (e1 := .var "g") (e2 := .num 5) (F := 49)
    (cfg := cfgB m n) h
  clear h
  obtain ⟨G, _, h⟩ := hh
  rcases h with h | h | h | h
  · subst h; rfl
  · obtain ⟨_, _, _, _, _, rfl⟩ := h; rfl
  · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, body, env', st1, st2, p, tcls, tenv, cursor, bn,
      _, _, hr2, _, hr1, _⟩ := h
    obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_num _ 5)
    have := terminatesTo_det hr1 (run_g m n _ rfl)
    simp [gClo] at this
  · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, body, pbody, env', st1, st2, p, tcls, tenv, cursor,
      bn, _, _, hr2, _, hr1, _, hpe, _⟩ := h
    obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_num _ 5)
    have := terminatesTo_det hr1 (run_g m n _ rfl)
    simp only [gClo, Value.peClosure.injEq] at this
    obtain ⟨_, ⟨_, rfl, _⟩⟩ := this
    rw [toPExpr?_gD] at hpe
    cases hpe

/-- The extern call of a run: it is typed against the member result `rM`,
    returns `m` and leaves the configuration. -/
private theorem callG_call {m n : Int} {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt (VC m n) effects entry res cf o) :
    res = rM ∧ o = .num m ∧ cf = cfgB m n ∧ effects = [] := by
  have hh := ExternCallAt.app_inv (ctx := KB) (e1 := .var "g") (e2 := .num 5) (F := 49)
    (cfg := cfgB m n) h
  clear h
  obtain ⟨G', hG, h⟩ := hh
  obtain rfl : G' = 47 := by omega
  rcases h with
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env', id, argTyp, argPoison, argPred, retSpec, captures,
      memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, bn, implFn,
      h2, hr2, h1, hr1, hety, hthr, hregl, _, himpl, hval, rfl, rfl, rfl⟩ |
    ⟨r2, r1, c2, c1, v2, x, y, env', id, argTyp, argPoison, argPred, retSpec, effs, captures,
      h2, hr2, h1, hr1⟩
  · obtain rfl : r2 = iArg KB (.num 5) 47 := ok_inj h2 facts_of.argG
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 (run_num _ 5)
    subst c2
    obtain rfl : r1 = iFun KB (.var "g") (.num 5) 47 := ok_inj h1 facts_of.funG
    obtain ⟨rfl, hc⟩ := terminatesTo_det hr1 (run_g m n _ rfl)
    simp only [gClo, Value.peClosure.injEq, gD, Expr.externPfn.injEq] at hc
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
    have hE := parrow1_eq facts_of.shape
    rw [hE] at hety
    simp only [ETyp.parrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨_, rfl, rfl, happ⟩ := ThreadedAt.single_inv hthr
    refine ⟨(okVal_of_eq happ).symm, ?_, rfl, rfl⟩
    have hregl' : (regC m).get? 250 = some (.pfn implFn) := hregl
    rw [regC_get] at hregl'
    simp only [gImpl, Option.some.injEq, ExternImpl.pfn.injEq] at hregl'
    subst hregl'
    simp only [constImpl, Except.ok.injEq] at himpl
    subst himpl
    simpa [validateExternReturn, gRet, valueMatchesTyp] using hval.symm
  · obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 (run_num _ 5)
    subst c2
    have := terminatesTo_det hr1 (run_g m n _ rfl)
    simp [gClo] at this

/-- The extern call of a run, built from the computed typing. -/
private theorem callG_at (m n : Int) :
    ∃ entry, ExternCallAt (VC m n) [] entry rM (cfgB m n) (.num m) := by
  obtain ⟨hm, hap⟩ := memberG
  have hr1 : terminatesTo (.var "g") { cfgB m n with varEnv := (cfgB m n).varEnv }
      { cfgB m n with varEnv := (cfgB m n).varEnv }
      (.peClosure "n" (.externPfn 250 "n" Typ.int false .noPred gRet []) (cfg1 m n).varEnv) :=
    run_g m n _ rfl
  have hregl : ({ cfgB m n with varEnv := (cfgB m n).varEnv } : Config).registry.get? 250 =
      some (.pfn (constImpl m)) := regC_get m
  exact ⟨_, ExternCallAt.pfn facts_of.argG (run_num _ 5) facts_of.funG hr1
    (parrow1_eq facts_of.shape) (ThreadedAt.here_of_eq (eq_okVal hap) hm) hregl rfl rfl
    (by simp [validateExternReturn, gRet, valueMatchesTyp])⟩

private inductive InSet (m n : Int) : Step → Prop
  | v0 : InSet m n (V0 m n)
  | v1 : InSet m n (V1 m n)
  | v2 : InSet m n (V2 m n)
  | v3 : InSet m n (V3 m n)
  | vb : InSet m n (VB m n)
  | vc : InSet m n (VC m n)
  | vt : InSet m n (VT m n)
  | leaf {s : Step} : noAppIte s.e = true → InSet m n s

private theorem inSet_step {m n : Int} {s s' : Step} (hs : InSet m n s) (h : SubStep s s') :
    InSet m n s' := by
  cases hs with
  | v0 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := K) (x := "lo") (e1 := .num 3)
        (e2 := letG) (F := 60) (cfg := cfgE m n) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc facts_of.lo
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_num (cfgE m n) 3)
        exact InSet.v1
  | v1 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := K1) (x := "g") (e1 := gD) (e2 := letF)
        (F := 58) (cfg := cfg1 m n) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc facts_of.g
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_gD m (cfg1 m n) rfl)
        exact InSet.v2
  | v2 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := K2) (x := "f") (e1 := fnF) (e2 := callF)
        (F := 56) (cfg := cfg2 m n) h
      obtain rfl : f = 54 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc facts_of.fT
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_fnF m n)
        exact InSet.v3
  | v3 =>
      rcases call_sub h with hl | rfl
      · exact InSet.leaf hl
      · exact InSet.vb
  | vb =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := KB) (x := "y") (e1 := call)
        (e2 := IntGuard.test) (F := 51) (cfg := cfgB m n) h
      obtain rfl : f = 49 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.vc
      · obtain rfl := ok_inj htc facts_of.c
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_call m n)
        exact InSet.vt
  | vc => exact InSet.leaf (callG_sub h)
  | vt =>
      exact InSet.leaf (SubStep.ite_noAppIte (ctx := L3) (F := 49) (cfg := cfgB3 m n) h rfl rfl
        rfl)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {m n : Int} {s : Step} (h : Reach (V0 m n) s) : InSet m n s := by
  induction h with
  | refl => exact InSet.v0
  | tail _ hsub ih => exact inSet_step ih hsub

private theorem reach_V3 (m n : Int) : Reach (V0 m n) (V3 m n) :=
  .tail (.tail (.single (SubStep.vletBody facts_of.lo (run_num (cfgE m n) 3)))
    (SubStep.vletBody facts_of.g (run_gD m (cfg1 m n) rfl)))
    (SubStep.vletBody facts_of.fT (run_fnF m n))

private theorem reach_VB (m n : Int) : Reach (V0 m n) (VB m n) := by
  refine .tail (reach_V3 m n) ?_
  exact SubStep.appFnBody (H := 51) (c2 := cfg3 m n) (v2 := .num 0)
    (c1 := { cfg3 m n with varEnv := (cfg3 m n).varEnv })
    facts_of.arg (run_num (cfg3 m n) 0) facts_of.fn (runF m n _ rfl) facts_of.ef
    (ThreadedAt.here_of_eq facts_of.ap member)
    (by rw [facts_of.tenv]; exact typing_tenv m n)

private theorem reach_VC (m n : Int) : Reach (V0 m n) (VC m n) :=
  .tail (reach_VB m n) SubStep.vletBound

private theorem reach_VT (m n : Int) : Reach (V0 m n) (VT m n) :=
  .tail (reach_VB m n) (SubStep.vletBody facts_of.c (run_call m n))

/-- The one conditional of a run, the test of the body. -/
private theorem inSet_ite {m n : Int} {s : Step} (hs : InSet m n s) {e1 e2 e3 : Expr}
    (he : s.e = .ite e1 e2 e3) : s = VT m n := by
  cases hs with
  | v0 => simp [V0, prog] at he
  | v1 => simp [V1, letG] at he
  | v2 => simp [V2, letF] at he
  | v3 => simp [V3, callF] at he
  | vb => simp [VB, bodyF] at he
  | vc => simp [VC, call] at he
  | vt => rfl
  | leaf hl => exact absurd he (noAppIte_ne_ite hl)

/-- A run makes one extern call, at `VC`. -/
private theorem inSet_call {m n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value} (hs : InSet m n s)
    (h : ExternCallAt s effects entry res cf o) :
    res = rM ∧ o = .num m ∧ cf = cfgB m n ∧ effects = [] := by
  cases hs with
  | vc => exact callG_call h
  | v3 => exact (call_noCall h).elim
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))
  | _ => cases h

/-- A run declares no extern value. -/
private theorem inSet_val {m n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet m n s) : ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

/-- A run reaches the call `g 5` in the body of `f`, typed against the one
    member of the type of `g`: the member result allocates tag 0, the guard
    `v >= lo` over `capE` (`lo` with number 1), which is true in its regime, and
    the call returns `m`. -/
theorem call_reached (m n : Int) :
    ∃ s entry res cf, Reach (V0 m n) s ∧ s.e = call ∧
      ExternCallAt s [] entry res cf (.num m) ∧ res.tagLog' = [gAlloc] ∧
      res.qualType.pred = .guardClosure 0 "v" loBody capE ∧ res.regime'.lookup? 0 = some true := by
  obtain ⟨entry, h⟩ := callG_at m n
  exact ⟨_, entry, rM, _, reach_VC m n, rfl, h, facts_of.logM, facts_of.predM, facts_of.regM⟩

/-! ## The view and the premises -/

/-- The view of a run from `x = n`: number 1 (`lo`) holds 3, number 2 (`g`) the
    closure of `g`, number 4 (`u`) 0, and number 6 (`y`) the value `m`. -/
def βe (m n : Int) : BindVals :=
  fun k =>
    if k = 1 then some (.num 3)
    else if k = 2 then some (gClo ((VarEnv.update [] "x" (.num n)).update "lo" (.num 3)))
    else if k = 4 then some (.num 0)
    else if k = 6 then some (.num m) else none

private theorem bind_L3 :
    L3.bindEnv =
      (((((∅ : BindEnv).insert "x" 0).insert "lo" 1).insert "g" 2).insert "u" 4).insert "y"
        6 := by
  show (BindEnv.bindParam (regTenv (arrowM EF)) "u" rFun.nextBind').insert "y"
    rC.nextBind' = _
  rw [facts_of.tenv, facts_of.bFun, facts_of.bC]
  rfl

private theorem get_L3 (z : Name) : L3.bindEnv.get? z =
    if z = "y" then some 6 else if z = "u" then some 4 else if z = "g" then some 2
    else if z = "lo" then some 1 else if z = "x" then some 0 else none := by
  rw [bind_L3]
  simp only [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, ExtTreeMap.getElem?_empty]
  by_cases hy : z = "y"
  · subst hy; simp
  · by_cases hu : z = "u"
    · subst hu; simp
    · by_cases hg : z = "g"
      · subst hg; simp
      · by_cases hl : z = "lo"
        · subst hl; simp
        · by_cases hx : z = "x"
          · subst hx; simp
          · simp [hy, hu, hg, hl, hx, Ne.symm hy, Ne.symm hu, Ne.symm hg, Ne.symm hl,
              Ne.symm hx]

/-- At the conditional every variable with a number other than 0 holds the
    value the view gives it. -/
private theorem view_T (m n : Int) (xs : List Name) :
    ViewAgreesOn (βe m n) L3.bindEnv (cfgB3 m n).varEnv xs := by
  intro z _ k hk hk0
  rw [get_L3] at hk
  by_cases hzy : z = "y"
  · subst hzy
    simp at hk
    subst hk
    simp [cfgB3, VarEnv.lookup, VarEnv.update, βe]
  · by_cases hzu : z = "u"
    · subst hzu
      simp at hk
      subst hk
      simp [cfgB3, cfgB, VarEnv.lookup, VarEnv.update, List.lookup, βe]
    · by_cases hzg : z = "g"
      · subst hzg
        simp at hk
        subst hk
        simp [cfgB3, cfgB, cfg2, cfg1, cfgE, VarEnv.lookup, VarEnv.update, List.lookup, βe]
      · by_cases hzl : z = "lo"
        · subst hzl
          simp at hk
          subst hk
          simp [cfgB3, cfgB, cfg2, cfg1, cfgE, VarEnv.lookup, VarEnv.update, List.lookup, βe]
        · by_cases hzx : z = "x"
          · subst hzx
            simp at hk
            exact absurd hk.symm hk0
          · simp [hzy, hzu, hzg, hzl, hzx] at hk

/-- Every run agrees with its view at the guards it tests. -/
theorem tests (m n : Int) : TestsAgreeWithView (βe m n) (V0 m n) where
  tests {ctx e1 e2 e3 f cfg k deps b d} hreach _ _ _ := by
    have hs := inSet_ite (inSet_reach hreach) (e1 := e1) (e2 := e2) (e3 := e3) rfl
    simp only [VT, Step.mk.injEq] at hs
    obtain ⟨rfl, _, _, rfl⟩ := hs
    exact view_T m n _

private theorem deep_VT :
    GuardDescInEnvsDeep L3.varEnv L3.memEnv 0
      { argName := "v", body := loBody, capEnv := capE } := by
  have hl : L3.varEnv.lookup "y" = some rC.qualType := VarTypeEnv_lookup_update_eq _ _ _
  exact GuardDescInEnvsDeep.intro rC.qualType 0 _
    (QTypInEnvs.inVar _ _ "y" _ _ hl (QTypInQTyp.self _))
    (by simp [qtypGuardDesc?, facts_of.predC])

/-- The conditional of the body is matched to the guard's tag, which the regime
    assigns true; a view that does not give number 1 the value of `lo` fails
    *TestsAgreeWithView*. -/
theorem view_needed (m n : Int) (β : BindVals) (hβ : β 1 ≠ some (.num 3)) :
    ¬ TestsAgreeWithView β (V0 m n) := by
  intro h
  obtain ⟨deps, hmatch⟩ := facts_of.sel
  have hv := h.tests (reach_VT m n) hmatch facts_of.reg3 deep_VT
  have hlo := hv "lo" (by simp [loBody, PExpr.freeVars]) 1
    (by rw [get_L3]; simp) (by decide)
  have h3 : (cfgB3 m n).varEnv.lookup "lo" = some (.num 3) := by
    simp [cfgB3, cfgB, cfg2, cfg1, cfgE, VarEnv.lookup, VarEnv.update, List.lookup]
  rw [h3] at hlo
  exact hβ hlo.symm

/-- *Match* under `loSat (βe m n)` holds exactly when `3 ≤ m`. -/
theorem match_iff (m n : Int) : ExternCallsMatch (loSat (βe m n)) (V0 m n) ↔ 3 ≤ m := by
  constructor
  · intro h
    obtain ⟨entry, hcall⟩ := callG_at m n
    have hcm := h.calls _ _ _ _ _ _ (reach_VC m n) hcall
    have hiff := hcm.ret gAlloc (by rw [facts_of.logM]; exact List.mem_singleton_self _) "v"
      loBody capE true facts_of.predM facts_of.regM
    obtain ⟨m', n', hβ, hv', hle⟩ := hiff.2 rfl
    simp [βe, loNum] at hβ
    cases hv'
    subst hβ
    exact hle
  · intro hm
    refine ⟨fun s effects entry res cf o hreach hcall => ?_,
      fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
    refine ⟨?_, fun _ _ _ _ hc => absurd hc EffectCell.not_nil⟩
    intro a ha _ _ _ b _ hR
    rw [facts_of.logM, List.mem_singleton] at ha
    subst ha
    have hb : b = true := by
      have hR' : rM.regime'.lookup? 0 = some b := hR
      rw [facts_of.regM] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [iff_true]
    exact ⟨3, m, rfl, rfl, hm⟩

private theorem capE_lo : (VarTypeEnv.ofCaptured capE).lookup "lo" = some intQt := by
  decide +kernel

private theorem capE_bind : (BindEnv.ofCaptured capE).get? "lo" = some loNum := by
  decide +kernel

private theorem pinSel : pinSelectsOf capE = true := by decide +kernel

/-- The laws on the table of the program. -/
theorem laws_program (β : BindVals) :
    PredSatLaws (loSat β) (programTable ∅ rootRes.tagLog') β := by
  rw [programTable_eq]
  exact IntGuard.loSat_lawful_cap capE capE_lo capE_bind β

/-- *Match* holds in a run, for any relation that satisfies the laws on the
    table of the program under a view that gives `lo` the value 3, exactly
    when `3 ≤ m`. -/
theorem match_iff_lawful (m n : Int) {predSat : PredSat} {β : BindVals}
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (hβ : β loNum = some (Value.num 3)) :
    ExternCallsMatch predSat (V0 m n) ↔ 3 ≤ m := by
  rw [programTable_eq] at hlaws
  have hpin := IntGuard.pin_lo_cap capE pinSel hlaws hβ
  constructor
  · intro h
    obtain ⟨entry, hcall⟩ := callG_at m n
    have hcm := h.calls _ _ _ _ _ _ (reach_VC m n) hcall
    have hiff := hcm.ret gAlloc (by rw [facts_of.logM]; exact List.mem_singleton_self _) "v"
      loBody capE true facts_of.predM facts_of.regM
    exact (hpin _ m).1 (hiff.2 rfl)
  · intro hm
    refine ⟨fun s effects entry res cf o hreach hcall => ?_,
      fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
    refine ⟨?_, fun _ _ _ _ hc => absurd hc EffectCell.not_nil⟩
    intro a ha _ _ _ b _ hR
    rw [facts_of.logM, List.mem_singleton] at ha
    subst ha
    have hb : b = true := by
      have hR' : rM.regime'.lookup? 0 = some b := hR
      rw [facts_of.regM] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [iff_true]
    exact (hpin _ m).2 hm

/-- With the registry returning `m < 3`, no relation and view meet the laws on
    the table of the program, the tests premise and *match* in a run: a view
    that gives `lo` the value 3 fails *match*, and any other view fails the
    tests premise. -/
theorem no_premises_lt (m n : Int) (hm : m < 3) (predSat : PredSat) (β : BindVals)
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (htests : TestsAgreeWithView β (V0 m n)) : ¬ ExternCallsMatch predSat (V0 m n) := by
  by_cases hβ : β 1 = some (Value.num 3)
  · rw [match_iff_lawful m n hlaws hβ]
    omega
  · exact absurd htests (view_needed m n β hβ)

/-- *Agreement* holds for every pair of runs with the same registry: the one
    call returns `m` in both. -/
theorem agree (m n₀ n₁ : Int) : ExternCallsAgree (V0 m n₀) (V0 m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ hr₁ _ _ _ hc₀ hc₁ _ => by
    obtain ⟨_, rfl, _, rfl⟩ := inSet_call (inSet_reach hr₀) hc₀
    obtain ⟨_, rfl, _, _⟩ := inSet_call (inSet_reach hr₁) hc₁
    exact callAgrees_nil rfl⟩

/-! ## The other premises of the theorem -/

private theorem trustedE (m : Int) : InitialContextTrusted (gReg m) prog K := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 250 ∧ d = gDecl := by
        simp only [prog, letG, letF, fnF, callF, bodyF, call, gD, IntGuard.test,
          IntGuard.cond] at hp
        cases hp with
        | vlet_bound h => cases h
        | vlet_body h =>
            cases h with
            | vlet_bound h =>
                cases h with
                | externPfn => exact ⟨rfl, rfl⟩
                | externPfn_return h => cases h
            | vlet_body h =>
                cases h with
                | vlet_bound h =>
                    cases h with
                    | fn_body h =>
                        cases h with
                        | vlet_bound h =>
                            cases h with
                            | app_fun h => cases h
                            | app_arg h => cases h
                        | vlet_body h =>
                            cases h with
                            | ite_cond h =>
                                cases h with
                                | op_left h => cases h
                                | op_right h => cases h
                            | ite_then h => cases h
                            | ite_else h => cases h
                | vlet_body h =>
                    cases h with
                    | app_fun h => cases h
                    | app_arg h => cases h
      obtain ⟨rfl, rfl⟩ := h
      simp [gReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := IntGuard.K_vars _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

/-- The starting configurations are well formed. -/
theorem wfCE (m n : Int) : wfConfig (cfgE m n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgE] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

/-- The registry `regC m` reserves no location. -/
theorem reservedWFE (m : Int) : RegistryReservedWF (regC m) ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regC_noLoc h).elim

/-- The registry `regC m` keeps the reservation discipline of `K`. -/
theorem disciplineE (m : Int) : ReservedDiscipline (regC m) K.declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regC_noLoc h).elim
  · intro id a h _ l
    exact (regC_noLoc h).elim

/-! ## The theorem -/

/-- **The theorem at
    `let lo = 3 in let g = extern pfn @250 n : ... -> ((int :> poisoned { 0, v => v >= lo })) in
     let f = fn u : int => (let y = g 5 in if y >= lo then 1 else x) : int in f 0`**,
    with the registry returning `m ≥ 3`: two runs from any `x` return the same
    value. The run from `x = n` has the relation `loSat (βe m n)` and the view
    `βe m n`. -/
theorem same_return (m : Int) (hm : 3 ≤ m) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgE m n₀) cf₀ o₀) (hr₁ : terminatesTo prog (cfgE m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  obtain ⟨htc, hety, hpz⟩ := typed_clean
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (gReg m) prog IntGuard.sV IntGuard.obsRet K
      IntGuard.externRegimeMatchesK (trustedE m) IntGuard.wfSpecV rfl IntGuard.ctxMatchesK
      IntGuard.wfCtxK rfl rfl rfl IntGuard.tagBoundedK
      ∅ IntGuard.wfTmK IntGuard.tmBoundedK 60 rootRes htc
      (And.intro (fun et h => by
          simp only [IntGuard.obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hety, hpz⟩)
        (fun _ _ h => by simp [IntGuard.obsRet, MemoryETypEnv.lookup] at h))
      ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (loSat (βe m n₀)) (loSat (βe m n₁)) (βe m n₀)
      (βe m n₁) (IntGuard.laws_start _) (IntGuard.laws_start _) (laws_program _)
      (laws_program _) IntGuard.wfRegimeK IntGuard.wfθ₀ IntGuard.wfθ₀
      (wfCE m n₀) (wfCE m n₁) (reservedWFE m) (reservedWFE m) (disciplineE m) (disciplineE m)
      (And.intro (fun h _ => by simp [IntGuard.sV] at h)
        (fun h _ => by simp [IntGuard.sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [IntGuard.sV] at h)
        (fun h _ => by simp [IntGuard.sV, VarTypeEnv.lookup] at h))
      (IntGuard.instantiatesK n₀) (IntGuard.instantiatesK n₁) (IntGuard.trustedInitK n₀)
      (IntGuard.trustedInitK n₁) IntGuard.consistentK IntGuard.consistentK
      ((match_iff m n₀).2 hm) ((match_iff m n₁).2 hm)
      (tests m n₀) (tests m n₁) IntGuard.agreeCriticalK IntGuard.agreeTrustedK
      (agree m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **The registry returns 5**: the runs from `x = 0` and `x = 1` both return 1,
    and the theorem gives the same. -/
theorem true_5 :
    terminatesTo prog (cfgE 5 0) (cfgE 5 0) (.num 1) ∧
    terminatesTo prog (cfgE 5 1) (cfgE 5 1) (.num 1) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo prog (cfgE 5 0) cf₀ o₀ → terminatesTo prog (cfgE 5 1) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_prog_ge 5 0 (by decide), run_prog_ge 5 1 (by decide),
    fun hr₀ hr₁ => same_return 5 (by decide) 0 1 hr₀ hr₁⟩

/-- **The registry returns 0**: the program is typed as a clean `int`, the runs
    from `x = 0` and `x = 1` return 0 and 1, and in each run no relation and
    view meet the laws on the table of the program, the tests premise and
    *match*. -/
theorem fails_0 :
    typecheck K prog 60 = .ok rootRes ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false ∧
    terminatesTo prog (cfgE 0 0) (cfgE 0 0) (.num 0) ∧
    terminatesTo prog (cfgE 0 1) (cfgE 0 1) (.num 1) ∧
    ∀ (n : Int) (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
      TestsAgreeWithView β (V0 0 n) → ¬ ExternCallsMatch predSat (V0 0 n) := by
  obtain ⟨h1, h2, h3⟩ := typed_clean
  exact ⟨h1, h2, h3, run_prog_lt 0 0 (by decide), run_prog_lt 0 1 (by decide),
    fun n predSat β hlaws htests => no_premises_lt 0 n (by decide) predSat β hlaws htests⟩

end CallInBody

end ExternCallsWitness
