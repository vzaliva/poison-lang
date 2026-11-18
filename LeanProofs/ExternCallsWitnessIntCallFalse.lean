import LeanProofs.ExternCallsWitnessInt
import LeanProofs.ExternCallsWitnessClosed

/-!
# An integer guard on the result of an extern function, under a false tag

The program of `ExternCallsWitnessIntCall` with `lo = 10` and the branches
swapped, under the assignment that gives every tag of `@250` the value false
(namespace `ExternCallsWitness.IntCallFalse`):

```text
let lo = 10 in
let g = extern pfn @250 n : (int :> clean {}) -> ((int :> poisoned { 0, v => v >= lo })) in
let y = g 5 in
if y >= lo then x else 1
```

typed in the context `KF`, the context `K` of `ExternCallsWitnessInt` (a
poisoned `x`) with every tag of `@250` false, as a clean `int`
(`typed_clean`): the conditional is matched to the guard's tag, false, and
takes the type of its else branch.

* The trusted entry of `g` (`gSpec`, registry `gReg m`). The implementation
  returns the value `m` whatever the argument (`gImpl m`); its call contracts
  are proved as in `ExternCallsWitnessIntCall`.
* The call allocates the guard's tag 0, which records `lo` with its number 1
  (`capC`); the table of the program is the guard over `capC`
  (`programTable_eq`), on which `loSat` is lawful (`laws_program`) and the
  laws fix any relation (`match_iff_lawful`).
* A run reaches the call, which returns `m` (`call_reached`). The view
  `βc m n` gives `lo` 10, `g` its closure and `y` the value `m` (`tests`,
  `view_needed`). *Match* under `loSat (βc m n)` holds exactly when `m < 10`
  (`match_iff`): the guard's tag is false, and the relation holds of `m`
  exactly when `10 ≤ m`. *Agreement* holds for two runs with the same
  registry (`agree`).
* `same_return`: for `m < 10`, two runs from any `x` return the same value,
  with every premise of the theorem proved. `false_5`: the registry returns 5;
  the runs from `x = 0` and `x = 1` return 1. `fails_10`: the registry returns
  10; the program is typed clean, the runs from `x = 0` and `x = 1` return 0
  and 1, and no relation and view meet the laws, the premise on tests and
  *match* (`no_premises_ge`).
-/

open Std LeanPoison ExternProofs

namespace ExternCallsWitness

namespace IntCallFalse

open IntGuard (loGuard loBody loNum intQt loSat loTmOf pinSelectsOf)

/-! ## The context -/

/-- The assignment that gives every tag of `@250` the value false. -/
def polF : ExternId → Tag → Option Bool := fun id _ => if id = 250 then some false else none

/-- The context `K` of `ExternCallsWitnessInt` with every tag of `@250` false. -/
def KF : TypeContext := { IntGuard.K with externRegime := polF }

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

/-- `if y >= lo then x else 1` -/
def testF : Expr := .ite IntGuard.cond (.var "x") (.num 1)

/-- `let y = g 5 in if y >= lo then x else 1` -/
def body2 : Expr := .vlet "y" call testF

/-- `let g = extern pfn @250 ... in let y = g 5 in if y >= lo then x else 1` -/
def body1 : Expr := .vlet "g" gD body2

/-- `let lo = 10 in let g = extern pfn @250 ... in let y = g 5 in if y >= lo then x else 1` -/
def prog : Expr := .vlet "lo" (.num 10) body1

/-- The starting state of a run from `x = n`, with the registry returning `m`. -/
def cfgC (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regC m }

/-- The closure a declaration of `g` evaluates to under `env`. -/
def gClo (env : VarEnv) : Value := .peClosure "n" gD env

/-! ## The typing -/

private def rLo : TypeResult := okVal (typecheckExpr KF (.num 10) 58)

/-- The context of the body of `let lo`. -/
private def L1 : TypeContext :=
  { ctxAfter KF rLo with
    varEnv := KF.varEnv.update "lo" rLo.qualType,
    bindEnv := KF.bindEnv.insert "lo" rLo.nextBind',
    nextBind := rLo.nextBind' + 1 }

private def rG : TypeResult := okVal (typecheckExpr L1 gD 56)

/-- The context of the body of `let g`. -/
private def L2 : TypeContext :=
  { ctxAfter L1 rG with
    varEnv := L1.varEnv.update "g" rG.qualType,
    bindEnv := L1.bindEnv.insert "g" rG.nextBind',
    nextBind := rG.nextBind' + 1 }

private def rC : TypeResult := okVal (typecheckExpr L2 call 54)

/-- The context of the conditional: `y` bound to the result of the call. -/
private def L3 : TypeContext :=
  { ctxAfter L2 rC with
    varEnv := L2.varEnv.update "y" rC.qualType,
    bindEnv := L2.bindEnv.insert "y" rC.nextBind',
    nextBind := rC.nextBind' + 1 }

/-- The typing of the program. -/
def rootRes : TypeResult := okVal (typecheckExpr KF prog 60)

/-- The member result of the call. -/
private def rM : TypeResult := iRes L2 (.var "g") (.num 5) 52

/-- The captured environment of the guard the call makes: `lo` with its number
    1, the extern's parameter `n` with the number of the call, 3, and the
    poisoned `x`. -/
def capC : CapturedVarEnv := [("lo", intQt, loNum), ("n", intQt, 3), ("x", pInt, 0)]

/-- The allocation of the guard at the call. -/
def gAlloc : TagAlloc := { tag := 0, argName := "v", body := loBody, capEnv := capC }

private def logOk (log : List TagAlloc) : Bool :=
  match log with
  | [a] => a.tag == 0 && a.argName == "v" && a.body == loBody && decide (a.capEnv = capC)
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

private def selects : Bool :=
  match matchGuard IntGuard.cond L3.memEnv L3.varEnv L3.bindEnv 52 with
  | .ok (k, _) => k == 0
  | .error _ => false

/-- What the typing gives, as a Boolean summary evaluated by the kernel. -/
private def facts : Bool :=
  isOkB (typecheckExpr KF prog 60) &&
  isOkB (typecheckExpr KF (.num 10) 58) &&
  isOkB (typecheckExpr L1 gD 56) &&
  isOkB (typecheckExpr L2 call 54) &&
  isOkB (typecheckExpr L2 (.num 5) 52) &&
  isOkB (typecheckExpr (ctxAfter L2 (iArg L2 (.num 5) 52)) (.var "g") 52) &&
  isParrow1 (iFun L2 (.var "g") (.num 5) 52).qualType.etyp &&
  (rLo.nextBind' == 1) &&
  (rG.nextBind' == 2) &&
  (rC.nextBind' == 4) &&
  (rM.regime'.lookup? 0 == some false) &&
  (L3.regime.lookup? 0 == some false) &&
  logOk rM.tagLog' &&
  logOk rootRes.tagLog' &&
  decide (rM.qualType.pred = .guardClosure 0 "v" loBody capC) &&
  decide (rM.qualType.etyp = .int) &&
  decide (rC.qualType.pred = .guardClosure 0 "v" loBody capC) &&
  selects &&
  decide (rootRes.qualType.etyp = .int) &&
  (rootRes.qualType.poison == false)

private theorem facts_ok : facts = true := by decide +kernel

private theorem facts_of :
    typecheckExpr KF prog 60 = .ok rootRes ∧
    typecheckExpr KF (.num 10) 58 = .ok rLo ∧
    typecheckExpr L1 gD 56 = .ok rG ∧
    typecheckExpr L2 call 54 = .ok rC ∧
    isOkB (typecheckExpr L2 (.num 5) 52) = true ∧
    isOkB (typecheckExpr (ctxAfter L2 (iArg L2 (.num 5) 52)) (.var "g") 52) = true ∧
    isParrow1 (iFun L2 (.var "g") (.num 5) 52).qualType.etyp = true ∧
    rLo.nextBind' = 1 ∧ rG.nextBind' = 2 ∧ rC.nextBind' = 4 ∧
    rM.regime'.lookup? 0 = some false ∧
    L3.regime.lookup? 0 = some false ∧
    rM.tagLog' = [gAlloc] ∧ rootRes.tagLog' = [gAlloc] ∧
    rM.qualType.pred = .guardClosure 0 "v" loBody capC ∧
    rM.qualType.etyp = .int ∧
    rC.qualType.pred = .guardClosure 0 "v" loBody capC ∧
    selects = true ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20⟩ := hf
  exact ⟨eq_okVal h1, eq_okVal h2, eq_okVal h3, eq_okVal h4, h5, h6, h7, h8, h9, h10, h11, h12,
    logOk_eq h13, logOk_eq h14, h15, h16, h17, h18, h19, h20⟩

/-- The member of the type of `g` at the call, and its application. -/
private theorem member_of :
    let E := (iFun L2 (.var "g") (.num 5) 52).qualType.etyp
    parrowM E = .extern 250 "n" gRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
      (extParts (parrowM E)).2.2 ∧
    isOkB (pfnApply L2 (iArg L2 (.num 5) 52) (iFun L2 (.var "g") (.num 5) 52)
      (parrowS1 E) (parrowS2 E) (parrowP E) 52 (parrowM E) (iCursor L2 (.var "g") (.num 5) 52)
        (iBind L2 (.var "g") (.num 5) 52)) = true := by
  decide +kernel

/-- The program is typed as a clean `int`. -/
theorem typed_clean :
    typecheck KF prog 60 = .ok rootRes ∧
      rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false :=
  ⟨facts_of.1, facts_of.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    facts_of.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The table of the program: the guard of tag 0 over `capC`. -/
theorem programTable_eq : programTable ∅ rootRes.tagLog' = loTmOf capC := by
  rw [facts_of.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  rfl


/-! ## The runs -/

private def cfg1 (m n : Int) : Config :=
  { cfgC m n with varEnv := (cfgC m n).varEnv.update "lo" (.num 10) }

private def cfg2 (m n : Int) : Config :=
  { cfg1 m n with varEnv := (cfg1 m n).varEnv.update "g" (gClo (cfg1 m n).varEnv) }

private def cfg3 (m n : Int) : Config :=
  { cfg2 m n with varEnv := (cfg2 m n).varEnv.update "y" (.num m) }

private theorem run_gD {m : Int} (cfg : Config) (hreg : cfg.registry = regC m) :
    terminatesTo gD cfg cfg (gClo cfg.varEnv) :=
  ⟨1, false, by unfold beval; simp [gD, hreg, regC_get', gImpl, gClo]⟩

private theorem run_g (m n : Int) :
    ∀ c, c.varEnv = (cfg2 m n).varEnv →
      terminatesTo (.var "g") c c (gClo (cfg1 m n).varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

/-- The call returns `m` and leaves the configuration. -/
private theorem run_call (m n : Int) : terminatesTo call (cfg2 m n) (cfg2 m n) (.num m) :=
  ⟨5, false, by
    simp [beval, call, cfg2, cfg1, cfgC, gClo, gD, gRet, VarEnv.lookup, VarEnv.update,
      regC_get', gImpl, constImpl, validateExternReturn, valueMatchesTyp, List.lookup]⟩

/-- A run with the value `m < 10` returns 1. -/
theorem run_prog_lt (m n : Int) (hm : m < 10) :
    terminatesTo prog (cfgC m n) (cfgC m n) (.num 1) := by
  refine ⟨10, false, ?_⟩
  simp [prog, body1, body2, call, gD, gRet, testF, IntGuard.cond, beval, cfgC,
    regC_get', gImpl, constImpl, validateExternReturn, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, Int.not_le.mpr hm]

/-- A run with the value `m ≥ 10` returns `x`. -/
theorem run_prog_ge (m n : Int) (hm : 10 ≤ m) :
    terminatesTo prog (cfgC m n) (cfgC m n) (.num n) := by
  refine ⟨10, false, ?_⟩
  simp [prog, body1, body2, call, gD, gRet, testF, IntGuard.cond, beval, cfgC,
    regC_get', gImpl, constImpl, validateExternReturn, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, hm]


/-! ## The steps of a run -/

/-- The root step. -/
def U0 (m n : Int) : Step := ⟨KF, prog, 60, cfgC m n⟩
private def U1 (m n : Int) : Step := ⟨L1, body1, 58, cfg1 m n⟩
private def U2 (m n : Int) : Step := ⟨L2, body2, 56, cfg2 m n⟩
private def U3 (m n : Int) : Step := ⟨L2, call, 54, cfg2 m n⟩
private def U4 (m n : Int) : Step := ⟨L3, testF, 54, cfg3 m n⟩

private theorem toPExpr?_gD : Expr.toPExpr? gD = none := rfl

/-- The steps of the call: the argument and the function, and no body, since the
    closure called is the extern's. -/
private theorem call_sub {m n : Int} {s' : Step} (h : SubStep (U3 m n) s') :
    noAppIte s'.e = true := by
  have hh := SubStep.app_inv (ctx := L2) (e1 := .var "g") (e2 := .num 5) (F := 54)
    (cfg := cfg2 m n) h
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
private theorem call_call {m n : Int} {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt (U3 m n) effects entry res cf o) :
    res = rM ∧ o = .num m ∧ cf = cfg2 m n ∧ effects = [] := by
  obtain ⟨_, _, _, _, hok2, hok1, hshape, _⟩ := facts_of
  have hh := ExternCallAt.app_inv (ctx := L2) (e1 := .var "g") (e2 := .num 5) (F := 54)
    (cfg := cfg2 m n) h
  clear h
  obtain ⟨G', hG, h⟩ := hh
  obtain rfl : G' = 52 := by omega
  rcases h with
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env', id, argTyp, argPoison, argPred, retSpec, captures,
      memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, bn, implFn,
      h2, hr2, h1, hr1, hety, hthr, hregl, _, himpl, hval, rfl, rfl, rfl⟩ |
    ⟨r2, r1, c2, c1, v2, x, y, env', id, argTyp, argPoison, argPred, retSpec, effs, captures,
      h2, hr2, h1, hr1⟩
  · obtain rfl : r2 = iArg L2 (.num 5) 52 := ok_inj h2 (eq_okVal hok2)
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 (run_num _ 5)
    subst c2
    obtain rfl : r1 = iFun L2 (.var "g") (.num 5) 52 := ok_inj h1 (eq_okVal hok1)
    obtain ⟨rfl, hc⟩ := terminatesTo_det hr1 (run_g m n _ rfl)
    simp only [gClo, Value.peClosure.injEq, gD, Expr.externPfn.injEq] at hc
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
    have hE := parrow1_eq hshape
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
private theorem call_at (m n : Int) :
    ∃ entry, ExternCallAt (U3 m n) [] entry rM (cfg2 m n) (.num m) := by
  obtain ⟨_, _, _, _, hok2, hok1, hshape, _⟩ := facts_of
  obtain ⟨hm, hap⟩ := member_of
  have hr1 : terminatesTo (.var "g") { cfg2 m n with varEnv := (cfg2 m n).varEnv }
      { cfg2 m n with varEnv := (cfg2 m n).varEnv }
      (.peClosure "n" (.externPfn 250 "n" Typ.int false .noPred gRet []) (cfg1 m n).varEnv) :=
    run_g m n _ rfl
  have hregl : ({ cfg2 m n with varEnv := (cfg2 m n).varEnv } : Config).registry.get? 250 =
      some (.pfn (constImpl m)) := regC_get m
  exact ⟨_, ExternCallAt.pfn (eq_okVal hok2) (run_num _ 5) (eq_okVal hok1) hr1
    (parrow1_eq hshape) (ThreadedAt.here_of_eq (eq_okVal hap) hm) hregl rfl rfl
    (by simp [validateExternReturn, gRet, valueMatchesTyp])⟩

private inductive InSet (m n : Int) : Step → Prop
  | u0 : InSet m n (U0 m n)
  | u1 : InSet m n (U1 m n)
  | u2 : InSet m n (U2 m n)
  | u3 : InSet m n (U3 m n)
  | u4 : InSet m n (U4 m n)
  | leaf {s : Step} : noAppIte s.e = true → InSet m n s

private theorem inSet_step {m n : Int} {s s' : Step} (hs : InSet m n s) (h : SubStep s s') :
    InSet m n s' := by
  obtain ⟨_, hLo, hG, hC, _⟩ := facts_of
  cases hs with
  | u0 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := KF) (x := "lo") (e1 := .num 10) (e2 := body1)
        (F := 60) (cfg := cfgC m n) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc hLo
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_num (cfgC m n) 10)
        exact InSet.u1
  | u1 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := L1) (x := "g") (e1 := gD) (e2 := body2)
        (F := 58) (cfg := cfg1 m n) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc hG
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_gD (m := m) (cfg1 m n) rfl)
        exact InSet.u2
  | u2 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := L2) (x := "y") (e1 := call)
        (e2 := testF) (F := 56) (cfg := cfg2 m n) h
      obtain rfl : f = 54 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.u3
      · obtain rfl := ok_inj htc hC
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_call m n)
        exact InSet.u4
  | u3 => exact InSet.leaf (call_sub h)
  | u4 =>
      exact InSet.leaf (SubStep.ite_noAppIte (ctx := L3) (F := 54) (cfg := cfg3 m n) h rfl rfl
        rfl)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {m n : Int} {s : Step} (h : Reach (U0 m n) s) : InSet m n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

private theorem reach_U2 (m n : Int) : Reach (U0 m n) (U2 m n) :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (SubStep.vletBody facts_of.2.1 (run_num (cfgC m n) 10)))
    (SubStep.vletBody facts_of.2.2.1 (run_gD (m := m) (cfg1 m n) rfl))

private theorem reach_U3 (m n : Int) : Reach (U0 m n) (U3 m n) :=
  Relation.ReflTransGen.tail (reach_U2 m n) SubStep.vletBound

private theorem reach_U4 (m n : Int) : Reach (U0 m n) (U4 m n) :=
  Relation.ReflTransGen.tail (reach_U2 m n) (SubStep.vletBody facts_of.2.2.2.1 (run_call m n))

/-- The only conditional of a run is `U4`. -/
private theorem inSet_ite {m n : Int} {s : Step} (hs : InSet m n s) {e1 e2 e3 : Expr}
    (he : s.e = .ite e1 e2 e3) : s = U4 m n := by
  cases hs with
  | u0 => simp [U0, prog] at he
  | u1 => simp [U1, body1] at he
  | u2 => simp [U2, body2] at he
  | u3 => simp [U3, call] at he
  | u4 => rfl
  | leaf hl => exact absurd he (noAppIte_ne_ite hl)

/-- A run makes one extern call, at `U3`. -/
private theorem inSet_call {m n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value} (hs : InSet m n s)
    (h : ExternCallAt s effects entry res cf o) :
    res = rM ∧ o = .num m ∧ cf = cfg2 m n ∧ effects = [] := by
  cases hs with
  | u3 => exact call_call h
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


/-! ## The view and the premises -/

/-- The view of a run from `x = n`: number 1 (`lo`) holds 10, number 2 (`g`) the
    closure of `g`, number 4 (`y`) the value `m`. -/
def βc (m n : Int) : BindVals :=
  fun k =>
    if k = 1 then some (.num 10)
    else if k = 2 then some (gClo ((cfgC m n).varEnv.update "lo" (.num 10)))
    else if k = 4 then some (.num m) else none

private theorem bind_L3 :
    L3.bindEnv = (((∅ : BindEnv).insert "lo" 1).insert "g" 2).insert "y" 4 := by
  obtain ⟨_, _, _, _, _, _, _, hLo, hG, hC, _⟩ := facts_of
  show ((KF.bindEnv.insert "lo" rLo.nextBind').insert "g" rG.nextBind').insert "y"
    rC.nextBind' = _
  rw [hLo, hG, hC]
  rfl

private theorem get_L3 (x : Name) : L3.bindEnv.get? x =
    if x = "y" then some 4 else if x = "g" then some 2 else if x = "lo" then some 1 else none := by
  rw [bind_L3]
  simp only [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, ExtTreeMap.getElem?_empty]
  by_cases hy : x = "y"
  · subst hy; simp
  · by_cases hg : x = "g"
    · subst hg; simp
    · by_cases hl : x = "lo"
      · subst hl; simp
      · simp [hy, hg, hl, Ne.symm hy, Ne.symm hg, Ne.symm hl]

/-- At the conditional every variable with a number holds the value the view
    gives it. -/
private theorem view_U4 (m n : Int) (xs : List Name) :
    ViewAgreesOn (βc m n) L3.bindEnv (cfg3 m n).varEnv xs := by
  intro x _ k hk _
  rw [get_L3] at hk
  by_cases hy : x = "y"
  · subst hy
    simp at hk
    subst hk
    simp [cfg3, cfg2, cfg1, cfgC, VarEnv.lookup, VarEnv.update, βc]
  · by_cases hg : x = "g"
    · subst hg
      simp at hk
      subst hk
      simp [cfg3, cfg2, cfg1, cfgC, VarEnv.lookup, VarEnv.update, List.lookup, βc]
    · by_cases hl : x = "lo"
      · subst hl
        simp at hk
        subst hk
        simp [cfg3, cfg2, cfg1, cfgC, VarEnv.lookup, VarEnv.update, List.lookup, βc]
      · simp [hy, hg, hl] at hk

/-- Every run agrees with its view at the guards it tests. -/
theorem tests (m n : Int) : TestsAgreeWithView (βc m n) (U0 m n) where
  tests {ctx e1 e2 e3 f cfg k deps b d} hreach _ _ _ := by
    have hs := inSet_ite (inSet_reach hreach) (e1 := e1) (e2 := e2) (e3 := e3) rfl
    simp only [U4, Step.mk.injEq] at hs
    obtain ⟨rfl, _, _, rfl⟩ := hs
    exact view_U4 m n _

private theorem selects_of :
    ∃ deps, matchGuard IntGuard.cond L3.memEnv L3.varEnv L3.bindEnv 52 = .ok (0, deps) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := facts_of
  unfold selects at h
  split at h
  · rename_i k d heq
    simp at h
    subst h
    exact ⟨d, heq⟩
  · simp at h

private theorem deep_U4 : GuardDescInEnvsDeep L3.varEnv L3.memEnv 0
    { argName := "v", body := loBody, capEnv := capC } := by
  have hl : L3.varEnv.lookup "y" = some rC.qualType := VarTypeEnv_lookup_update_eq _ _ _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ := facts_of
  exact GuardDescInEnvsDeep.intro rC.qualType 0 _
    (QTypInEnvs.inVar _ _ "y" _ _ hl (QTypInQTyp.self _)) (by simp [qtypGuardDesc?, hp])

/-- The conditional is matched to the guard's tag, which the regime assigns
    false; a view that does not give number 1 the value of `lo` fails
    *TestsAgreeWithView*. -/
theorem view_needed (m n : Int) (β : BindVals) (hβ : β 1 ≠ some (.num 10)) :
    ¬ TestsAgreeWithView β (U0 m n) := by
  intro h
  obtain ⟨deps, hmatch⟩ := selects_of
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hreg, _⟩ := facts_of
  have hv := h.tests (reach_U4 m n) hmatch hreg deep_U4
  have hlo := hv "lo" (by simp [loBody, PExpr.freeVars]) 1
    (by rw [get_L3]; simp) (by decide)
  have h3 : (cfg3 m n).varEnv.lookup "lo" = some (.num 10) := by
    simp [cfg3, cfg2, cfg1, cfgC, VarEnv.lookup, VarEnv.update, List.lookup]
  rw [h3] at hlo
  exact hβ hlo.symm

/-- A run reaches the call of `g`, which returns `m` and allocates the guard over
    `capC`. -/
theorem call_reached (m n : Int) :
    ∃ s entry res cf, Reach (U0 m n) s ∧ ExternCallAt s [] entry res cf (.num m) ∧
      res.tagLog' = [gAlloc] := by
  obtain ⟨entry, h⟩ := call_at m n
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlog, _⟩ := facts_of
  exact ⟨_, entry, rM, _, reach_U3 m n, h, hlog⟩

/-- *Match* under `loSat (βc m n)` holds exactly when `m < 10`: the guard's tag
    is false, and the relation holds of `m` exactly when `10 ≤ m`. -/
theorem match_iff (m n : Int) : ExternCallsMatch (loSat (βc m n)) (U0 m n) ↔ m < 10 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hreg, _, hlog, _, hp, _⟩ := facts_of
  constructor
  · intro h
    obtain ⟨entry, hcall⟩ := call_at m n
    have hcm := h.calls _ _ _ _ _ _ (reach_U3 m n) hcall
    have hiff := hcm.ret gAlloc (by rw [hlog]; exact List.mem_singleton_self _) "v" loBody capC
      false hp hreg
    by_contra hge
    have := hiff.1 ⟨10, m, rfl, rfl, by omega⟩
    simp at this
  · intro hm
    refine ⟨fun s effects entry res cf o hreach hcall => ?_,
      fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
    refine ⟨?_, fun _ _ _ _ hc => absurd hc EffectCell.not_nil⟩
    intro a ha _ _ _ b _ hR
    rw [hlog, List.mem_singleton] at ha
    subst ha
    have hb : b = false := by
      have hR' : rM.regime'.lookup? 0 = some b := hR
      rw [hreg] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨m', n', hβ, hv, hle⟩
    simp [βc, loNum] at hβ
    cases hv
    omega

private theorem capC_lo : (VarTypeEnv.ofCaptured capC).lookup "lo" = some intQt := by
  decide +kernel

private theorem capC_bind : (BindEnv.ofCaptured capC).get? "lo" = some loNum := by
  decide +kernel

private theorem pinSel : pinSelectsOf capC = true := by decide +kernel

/-- The laws on the table of the program. -/
theorem laws_program (β : BindVals) :
    PredSatLaws (loSat β) (programTable ∅ rootRes.tagLog') β := by
  rw [programTable_eq]
  exact IntGuard.loSat_lawful_cap capC capC_lo capC_bind β

/-- *Match* holds in a run, for any relation that satisfies the laws on the
    table of the program under a view that gives `lo` the value 10, exactly
    when `m < 10`. -/
theorem match_iff_lawful (m n : Int) {predSat : PredSat} {β : BindVals}
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (hβ : β loNum = some (Value.num 10)) :
    ExternCallsMatch predSat (U0 m n) ↔ m < 10 := by
  rw [programTable_eq] at hlaws
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hreg, _, hlog, _, hp, _⟩ := facts_of
  have hpin := IntGuard.pin_lo_cap capC pinSel hlaws hβ
  constructor
  · intro h
    obtain ⟨entry, hcall⟩ := call_at m n
    have hcm := h.calls _ _ _ _ _ _ (reach_U3 m n) hcall
    have hiff := hcm.ret gAlloc (by rw [hlog]; exact List.mem_singleton_self _) "v" loBody capC
      false hp hreg
    by_contra hge
    have := hiff.1 ((hpin _ m).2 (by omega))
    simp at this
  · intro hm
    refine ⟨fun s effects entry res cf o hreach hcall => ?_,
      fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
    refine ⟨?_, fun _ _ _ _ hc => absurd hc EffectCell.not_nil⟩
    intro a ha _ _ _ b _ hR
    rw [hlog, List.mem_singleton] at ha
    subst ha
    have hb : b = false := by
      have hR' : rM.regime'.lookup? 0 = some b := hR
      rw [hreg] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [Bool.false_eq_true, iff_false]
    intro h
    have := (hpin _ m).1 h
    omega

/-- With the registry returning `m ≥ 10`, no relation and view meet the laws on
    the table of the program, the tests premise and *match* in a run: a view
    that gives `lo` the value 10 fails *match*, and any other view fails the
    tests premise. -/
theorem no_premises_ge (m n : Int) (hm : 10 ≤ m) (predSat : PredSat) (β : BindVals)
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (htests : TestsAgreeWithView β (U0 m n)) : ¬ ExternCallsMatch predSat (U0 m n) := by
  by_cases hβ : β 1 = some (Value.num 10)
  · rw [match_iff_lawful m n hlaws hβ]
    omega
  · exact absurd htests (view_needed m n β hβ)

/-- *Agreement* holds for every pair of runs with the same registry: the one
    call returns `m` in both. -/
theorem agree (m n₀ n₁ : Int) : ExternCallsAgree (U0 m n₀) (U0 m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ hr₁ _ _ _ hc₀ hc₁ _ => by
    obtain ⟨_, rfl, _, rfl⟩ := inSet_call (inSet_reach hr₀) hc₀
    obtain ⟨_, rfl, _, _⟩ := inSet_call (inSet_reach hr₁) hc₁
    exact callAgrees_nil rfl⟩

/-! ## The other premises of the theorem -/

private theorem trustedC (m : Int) : InitialContextTrusted (gReg m) prog KF := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 250 ∧ d = gDecl := by
        simp only [prog, body1, body2, call, gD, testF, IntGuard.cond] at hp
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
theorem wfCC (m n : Int) : wfConfig (cfgC m n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgC] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

/-- The registry `regC m` reserves no location. -/
theorem reservedWFC (m : Int) : RegistryReservedWF (regC m) ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regC_noLoc h).elim

/-- The registry `regC m` keeps the reservation discipline of `KF`. -/
theorem disciplineC (m : Int) : ReservedDiscipline (regC m) KF.declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regC_noLoc h).elim
  · intro id a h _ l
    exact (regC_noLoc h).elim

/-- `KF`'s assignment of extern tags matches `sV`. -/
theorem externRegimeMatchesKF : ExternRegimeMatchesInputSpec IntGuard.sV KF := by
  refine ⟨fun {id} hid k => ?_, fun {id} hid k => ?_⟩
  · have h : id ≠ 250 := by simpa [IntGuard.sV] using hid
    simp [KF, polF, h]
  · simp only [IntGuard.sV, List.mem_singleton] at hid
    subst hid
    exact ⟨false, by simp [KF, polF]⟩

/-- The closures of the trusted variables at the start, from `x = n`. -/
theorem trustedInitKF {predSat : PredSat} (n : Int) :
    trustedVarsClosureRegimeInit predSat KF.regime IntGuard.sV KF ∅
      (VarEnv.update [] "x" (.num n)) ∅ := by
  refine trustedVarsClosureRegimeInit.intro ?_
  intro x qt v h _ hv
  have hq := IntGuard.K_vars x qt h
  subst hq
  have hx : x = "x" := by
    by_contra hx
    simp only [KF, IntGuard.K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h
  subst hx
  have hl : (VarEnv.update [] "x" (.num n)).lookup "x" = some (.num n) := by
    simp [VarEnv.update, VarEnv.lookup]
  rw [hl] at hv
  obtain rfl := Option.some.inj hv
  exact closureCapturedVarsRegime.intro
    (deepValueQTypProperty.nonClosure (fun _ _ _ hc => by cases hc)
      (fun _ _ _ hc => by cases hc))

/-! ## The theorem -/

/-- **The theorem at
    `let lo = 10 in let g = extern pfn @250 n : ... -> ((int :> poisoned { 0, v => v >= lo })) in
     let y = g 5 in if y >= lo then x else 1`** in `KF`, with the registry
    returning `m < 10`: two runs from any `x` return the same value. The run from
    `x = n` has the relation `loSat (βc m n)` and the view `βc m n`. -/
theorem same_return (m : Int) (hm : m < 10) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgC m n₀) cf₀ o₀) (hr₁ : terminatesTo prog (cfgC m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  obtain ⟨htc, hety, hpz⟩ := typed_clean
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (gReg m) prog IntGuard.sV IntGuard.obsRet KF
      externRegimeMatchesKF (trustedC m) IntGuard.wfSpecV rfl IntGuard.ctxMatchesK
      IntGuard.wfCtxK rfl rfl rfl IntGuard.tagBoundedK
      ∅ IntGuard.wfTmK IntGuard.tmBoundedK 60 rootRes htc
      (And.intro (fun et h => by
          simp only [IntGuard.obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hety, hpz⟩)
        (fun _ _ h => by simp [IntGuard.obsRet, MemoryETypEnv.lookup] at h))
      ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (loSat (βc m n₀)) (loSat (βc m n₁)) (βc m n₀)
      (βc m n₁) (IntGuard.laws_start _) (IntGuard.laws_start _) (laws_program _)
      (laws_program _) IntGuard.wfRegimeK IntGuard.wfθ₀ IntGuard.wfθ₀
      (wfCC m n₀) (wfCC m n₁) (reservedWFC m) (reservedWFC m) (disciplineC m) (disciplineC m)
      (And.intro (fun h _ => by simp [IntGuard.sV] at h)
        (fun h _ => by simp [IntGuard.sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [IntGuard.sV] at h)
        (fun h _ => by simp [IntGuard.sV, VarTypeEnv.lookup] at h))
      (IntGuard.instantiatesK n₀) (IntGuard.instantiatesK n₁) (trustedInitKF n₀)
      (trustedInitKF n₁) IntGuard.consistentK IntGuard.consistentK
      ((match_iff m n₀).2 hm) ((match_iff m n₁).2 hm)
      (tests m n₀) (tests m n₁) IntGuard.agreeCriticalK IntGuard.agreeTrustedK
      (agree m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **The registry returns 5**: the call returns 5 against the guard `v >= 10`
    under a false tag, the runs from `x = 0` and `x = 1` both return 1, and the
    theorem gives the same. -/
theorem false_5 :
    terminatesTo prog (cfgC 5 0) (cfgC 5 0) (.num 1) ∧
    terminatesTo prog (cfgC 5 1) (cfgC 5 1) (.num 1) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo prog (cfgC 5 0) cf₀ o₀ → terminatesTo prog (cfgC 5 1) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_prog_lt 5 0 (by decide), run_prog_lt 5 1 (by decide),
    fun hr₀ hr₁ => same_return 5 (by decide) 0 1 hr₀ hr₁⟩

/-- **The registry returns 10**: the program is typed as a clean `int`, the
    runs from `x = 0` and `x = 1` return 0 and 1, and in each run no relation
    and view meet the laws on the table of the program, the tests premise and
    *match*. -/
theorem fails_10 :
    typecheck KF prog 60 = .ok rootRes ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false ∧
    terminatesTo prog (cfgC 10 0) (cfgC 10 0) (.num 0) ∧
    terminatesTo prog (cfgC 10 1) (cfgC 10 1) (.num 1) ∧
    ∀ (n : Int) (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
      TestsAgreeWithView β (U0 10 n) → ¬ ExternCallsMatch predSat (U0 10 n) := by
  obtain ⟨h1, h2, h3⟩ := typed_clean
  exact ⟨h1, h2, h3, run_prog_ge 10 0 (by decide), run_prog_ge 10 1 (by decide),
    fun n predSat β hlaws htests => no_premises_ge 10 n (by decide) predSat β hlaws htests⟩

end IntCallFalse

end ExternCallsWitness
