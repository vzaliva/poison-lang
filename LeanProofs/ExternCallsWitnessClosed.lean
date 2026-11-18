import LeanProofs.ExternProofs
import LeanProofs.FaultRobustnessProofs
import LeanProofs.ExternCallsWitness

/-!
# The theorem at the witness programs

The module `ExternCallsWitness` proves the premises on extern calls
(`ExternCallsMatch`, `ExternCallsAgree`) for small programs that call the pure
extern `read`. This module proves every other premise of the theorem for those
programs and applies the theorem to them.

* The trusted entry of `read` (`readSpec`): its declaration, its implementation
  (the identity) and the five boundary contracts. The two call contracts are
  proved from the premises on extern calls: *match* gives the regime entry of
  the call's tag, *agreement* gives equal results when that tag is true.
* `closed_of`: the theorem applied to a program whose only extern is `read`
  (`ReadOnly`), in a context whose variables are poisoned integers, with the
  relation `geSat` and the empty starting table. Given the typing run, the
  laws on its program table, two runs from integer variables and the premises
  on extern calls, every other premise is proved here.
* `wrapper_closed`, `skipped_closed`, `twoRuns_closed`, `twoCalls_closed`: the
  four programs of `ExternCallsWitness`, with no hypothesis left.

Limits.

* In each instance the two runs start from the same state.
* Nothing is observed (`obsNone`): the result of `read` is poisoned in its
  type, so the observable constraints rule out the returned value. The
  conclusion therefore says only that both runs terminate.
* The evidence is in the proof: Lean accepts the theorem applied to a proof of
  each of its premises, the premises on extern calls and a trusted entry whose
  call contracts use them included.
-/

open Std LeanPoison ExternProofs

namespace ExternCallsWitness

/-- The declaration of `read`:
    `extern pfn @7 b : (int :> ap) -> (int :> poisoned {0, w => w >= 0})`, where
    `ap` says whether the argument may be poisoned. -/
def readDecl (ap : Bool) : ExternDeclaration := pfnExternDecl 7 "b" Typ.int readRet [] ap

/-- The implementation of `read`: the identity. -/
def readImpl : ExternImpl := .pfn idImpl

/-! ## A call of a pure extern with a simple return -/

/-- The result of a successful pure extern member with a simple return. -/
private theorem simplePfn_shape
    {id : ExternId} {x : Name} {typ : Typ} {poison : Bool} {spred : SyntaxPredicate}
    {tenv : CapturedVarEnv} {declaredArgQt : QTyp} {captures : List Capture}
    {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {ctx : TypeContext} {bodyState : TypeResult} {cursor : Tag × Loc} {bn : Nat} {fuel : Nat}
    {res : TypeResult}
    (happly : applyPFnTClosureAtCursor
      (PFnTClosure.extern id x (.simple typ poison spred) tenv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor bn fuel = .ok res) :
    ∃ fuel' tagMapping nextTag' resolvedPred retQt nextLoc',
      fuel = fuel' + 1 ∧
      collectAndAllocExternTags [spred] cursor.1 = .ok (tagMapping, nextTag') ∧
      resolveSyntaxPred spred
        (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
        (BindEnv.bindParam tenv x bn) tagMapping = .ok resolvedPred ∧
      returnSpecToQTyp typ poison resolvedPred cursor.2 = .ok (retQt, nextLoc') ∧
      res =
        { qualType := normalizeAppResultByProvenance (joinPoison p1 p)
            ⟨retQt.etyp, joinPoison p1 (joinPoison p (joinPoison ctx.pc retQt.poison)), retQt.pred⟩
          memEnv' := bodyState.memEnv'
          tagEnv' := installReturnGuard bodyState.tagEnv' resolvedPred
            (applyExternRegimePolicy bodyState.regime' id ctx.externRegime tagMapping) fuel'
          nextLoc' := nextLoc'
          nextTag' := nextTag'
          nextBind' := bn + 1
          regime' := applyExternRegimePolicy bodyState.regime' id ctx.externRegime tagMapping
          declared' := bodyState.declared'
          tagLog' := externTagLog [spred]
            (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
              ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
            (BindEnv.bindParam tenv x bn) tagMapping } := by
  cases fuel with
  | zero => simp [applyPFnTClosureAtCursor] at happly
  | succ fuel' =>
      simp only [applyPFnTClosureAtCursor, bind, Except.bind, pure, Except.pure] at happly
      split at happly
      · simp at happly
      cases hcol : collectAndAllocExternTags [spred] cursor.1 with
      | error _ => simp [hcol] at happly
      | ok tm =>
          obtain ⟨tagMapping, nextTag'⟩ := tm
          simp only [hcol] at happly
          cases hres : resolveSyntaxPred spred
              (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
              (BindEnv.bindParam tenv x bn) tagMapping with
          | error _ => simp [hres] at happly
          | ok resolvedPred =>
              simp only [hres] at happly
              cases hret : returnSpecToQTyp typ poison resolvedPred cursor.2 with
              | error _ => simp [hret] at happly
              | ok rq =>
                  obtain ⟨retQt, nextLoc'⟩ := rq
                  simp only [hret] at happly
                  split at happly
                  · exact nomatch happly
                  simp only [Except.ok.injEq] at happly
                  exact ⟨fuel', tagMapping, nextTag', resolvedPred, retQt, nextLoc', rfl,
                    rfl, hres, hret, happly.symm⟩

/-- `returnSpecToQTyp` keeps the predicate and the poison and yields a base type. -/
private theorem returnSpecToQTyp_ok {typ : Typ} {poison : Bool} {pred : Predicate} {nl : Loc}
    {retQt : QTyp} {nl' : Loc}
    (h : returnSpecToQTyp typ poison pred nl = .ok (retQt, nl')) :
    retQt.pred = pred ∧ retQt.poison = poison ∧ retQt.etyp.isFunctionType = false ∧
      (¬ ∃ ls, retQt.etyp = ETyp.ref ls) ∧ nl' = nl := by
  cases typ <;>
    simp [returnSpecToQTyp, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])

/-- A single guard-only predicate has no guard closure to name its tag. -/
private theorem collect_guardOnly_ne {idx : TagIndex} {t : Tag} {r : TagMapping × Tag} :
    collectAndAllocExternTags [SyntaxPredicate.guardOnly idx] t ≠ .ok r := by
  intro h
  simp [collectAndAllocExternTags, forIn, ForIn.forIn, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

/-- The guard tag of a simple pure extern result is allocated by the call. -/
private theorem simplePfn_guardTag_mem
    {id : ExternId} {x : Name} {typ : Typ} {poison : Bool} {spred : SyntaxPredicate}
    {tenv : CapturedVarEnv} {declaredArgQt : QTyp} {captures : List Capture}
    {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {ctx : TypeContext} {bodyState : TypeResult} {cursor : Tag × Loc} {bn : Nat} {fuel : Nat}
    {res : TypeResult}
    (happly : applyPFnTClosureAtCursor
      (PFnTClosure.extern id x (.simple typ poison spred) tenv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx bodyState cursor bn fuel = .ok res)
    {k : Tag} (hk : qtypGuardTag res.qualType = some k) :
    ∃ a ∈ res.tagLog', a.tag = k := by
  obtain ⟨fuel', tagMapping, nextTag', resolvedPred, retQt, nextLoc', _hfuel, hcol, hresolve,
    hret, rfl⟩ := simplePfn_shape happly
  obtain ⟨hpredEq, -, -, -, -⟩ := returnSpecToQTyp_ok hret
  by_cases hprov : joinPoison p1 p = true
  · simp [normalizeAppResultByProvenance, hprov, qtypGuardTag] at hk
  · have hk' : qtypGuardTag ⟨retQt.etyp, true, resolvedPred⟩ = some k := by
      simpa [normalizeAppResultByProvenance, hprov, qtypGuardTag, hpredEq] using hk
    cases spred with
    | noPred =>
        simp [resolveSyntaxPred, pure, Except.pure] at hresolve
        subst hresolve
        simp [qtypGuardTag] at hk'
    | guardOnly idx => exact absurd hcol collect_guardOnly_ne
    | guardClosure idx arg body =>
        cases hget : tagMapping[idx]? with
        | none => simp [resolveSyntaxPred, hget, throw, throwThe, MonadExceptOf.throw] at hresolve
        | some tag =>
            cases hpb : body.toPExpr with
            | error _ =>
                simp [resolveSyntaxPred, hget, hpb, Functor.map, Except.map] at hresolve
            | ok pbody =>
                simp [resolveSyntaxPred, hget, hpb, Functor.map, Except.map] at hresolve
                subst hresolve
                simp [qtypGuardTag] at hk'
                subst hk'
                simp [externTagLog, hget, hpb]

/-- From *match*: the value returned by the call is consistent with the regime
    after the call. -/
private theorem valueConsistent_of_callMatches {predSat : PredSat} {entry : ExternCallEntry}
    {effects : List Effect} {res : TypeResult} {cf : Config} {o : Value} {θ : RealizationMap}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hmatch : CallMatches predSat entry effects res cf o)
    (hvt : valueHasETyp θ o res.qualType.etyp)
    (hnotfun : res.qualType.etyp.isFunctionType = false) :
    valueConsistentWithRegime predSat res.regime' res.qualType cf.memory θ o := by
  have hccv : closureCapturedVarsRegime predSat res.regime' res.qualType cf.memory θ o :=
    closureCapturedVarsRegime_nonClosure_of_nonFunctionType hvt hnotfun
  cases hpred : res.qualType.pred with
  | noPred => exact .noTag (by simp [qtypGuardTag, hpred]) hccv
  | guardOnly k => exact .guardOnly_ok k hpred hccv
  | guardClosure k arg body cap =>
      have htag : qtypGuardTag res.qualType = some k := by simp [qtypGuardTag, hpred]
      obtain ⟨a, ha, hak⟩ := hhinge k htag
      cases hR : res.regime'.lookup? k with
      | none => exact .notInRegime k htag hR hccv
      | some b =>
          have hiff := hmatch.ret a ha arg body cap b (by rw [hak]; exact hpred) (by rw [hak]; exact hR)
          rw [hak] at hiff
          cases b with
          | true => exact .inRegimeTrue k htag hR (.guardClosure_ok hpred (hiff.mpr rfl)) hccv
          | false =>
              refine .inRegimeFalse k htag hR ?_ hccv
              intro hholds
              cases hholds with
              | noPred_ok h => rw [hpred] at h; cases h
              | guardClosure_ok h hSat =>
                  rw [hpred] at h
                  cases h
                  exact absurd (hiff.mp hSat) (by simp)
              | guardOnly_ok h => rw [hpred] at h; cases h

/-- From *agreement*: a poisoned result that is clean through a guard of the
    call agrees in the two runs. -/
private theorem resultAgreesIfClean_of_callAgrees {predSat₀ predSat₁ : PredSat} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {entry₀ entry₁ : ExternCallEntry} {effects : List Effect}
    {res : TypeResult} {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hpoison : res.qualType.poison = true)
    (hnotfun : res.qualType.etyp.isFunctionType = false)
    (hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls)
    (hagree : CallAgrees entry₀ entry₁ effects res cf₀ cf₁ o₀ o₁) :
    resultAgreesIfClean predSat₀ predSat₁ res.regime' μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
  intro hclean
  cases hclean with
  | clean hp => rw [hpoison] at hp; cases hp
  | guard k htag hR _ =>
      obtain ⟨a, ha, hak⟩ := hhinge k htag
      exact .withPred_true_eq k htag hR hnotfun hnotref
        (hagree.ret a ha (by rw [hak]; exact htag) (by rw [hak]; exact hR) hnotfun hnotref)

/-! ## The trusted entry of `read` -/

/-- From the cursor form of a member application to the plain form. -/
private theorem pfnAtCursor_plain {tcl : PFnTClosure} {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp}
    {argPoison : Poison} {argPred : Predicate} {ctx : TypeContext} {r1 : TypeResult}
    {cursor : Tag × Loc} {bn : Nat} {fuel : Nat} {r : TypeResult}
    (happly : applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 cursor
      bn fuel = .ok r) :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx
      { r1 with nextTag' := cursor.1, nextLoc' := cursor.2, nextBind' := bn } fuel = .ok r := by
  unfold applyPFnTClosure
  unfold applyPFnTClosureAtCursor at happly
  simpa using happly

/-- What the typing of a call to a pure extern with a simple `int` return gives
    about the member result, in terms of the body context. -/
private structure SimplePfnCallFacts (ctx : TypeContext) (res : TypeResult) (poison : Bool) : Prop where
  etyp : res.qualType.etyp = ETyp.int
  poison_true : poison = true → res.qualType.poison = true
  memEnv : res.memEnv' = ctx.memEnv
  nextLoc : res.nextLoc' = ctx.nextLoc
  declared : res.declared' = ctx.declaredExternRefs
  nextTag_le : ctx.nextTag ≤ res.nextTag'
  regime_some : ∀ k b, ctx.regime.lookup? k = some b → res.regime'.lookup? k = some b
  regime_back : ∀ k b, k < ctx.nextTag → res.regime'.lookup? k = some b →
    ctx.regime.lookup? k = some b
  tagEnv_cases : ∀ k tv, res.tagEnv'.get? k = some tv →
    ctx.tagEnv.get? k = some tv ∨
      (ctx.nextTag ≤ k ∧ k < res.nextTag' ∧ res.regime'.lookup? k = some tv.value)
  guard_mem : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k
  tagMeaning : ∀ tm, TagMeaningBounded tm ctx.nextTag →
    ∃ tm', tm ⊑ tm' ∧ TagMeaningBounded tm' res.nextTag' ∧
      QTypRespectsTagMeaning tm' res.qualType ∧ WithinLog tm res.tagLog' tm'

private theorem simplePfnCall_facts {d : ExternDeclaration} {poison : Bool} {spred : SyntaxPredicate}
    {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (hkind : d.kind = .pfn) (hret : d.retSpec = some (.simple .int poison spred))
    (htyped : ExternBoundaryTyping.Call d typedExpr entry res) :
    SimplePfnCallFacts entry.bodyCtx res poison := by
  cases htyped with
  | fnExternMember _ hkind' => rw [hkind] at hkind'; cases hkind'
  | pfnExternMember _hid _hkind' _htyp _harg hret' _hcap _hpin hbody happly _heffects =>
      rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
        id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec captures bodyCaptures tenv bn
      have hrs : retSpec = .simple .int poison spred := by
        rw [hret] at hret'; exact (Option.some.inj hret').symm
      subst hrs
      have hplain := pfnAtCursor_plain happly
      obtain ⟨fuel', tagMapping, nextTag', resolvedPred, retQt, nextLoc', hfuel, hcol, hresolve,
        hretQt, hres⟩ := simplePfn_shape happly
      obtain ⟨hpredEq, hpoisonEq, _hnf, _hnr, hnl⟩ := returnSpecToQTyp_ok hretQt
      have hetypEq : retQt.etyp = ETyp.int := by
        simp [returnSpecToQTyp, bind, Except.bind, pure, Except.pure] at hretQt
        rw [← hretQt.1]
      have hetypRes : res.qualType.etyp = ETyp.int := by
        rw [hres]; unfold normalizeAppResultByProvenance
        split <;> simp [hetypEq]
      have hguard : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k :=
        fun _ hk => simplePfn_guardTag_mem happly hk
      have hge : cursor.1 ≤ nextTag' :=
        collectAndAllocExternTags_nextTag_ge [spred] cursor.1 tagMapping nextTag' hcol
      rw [hbody]
      refine
        { etyp := ?_, poison_true := ?_, memEnv := ?_, nextLoc := ?_, declared := ?_,
          nextTag_le := ?_, regime_some := ?_, regime_back := ?_, tagEnv_cases := ?_,
          guard_mem := hguard, tagMeaning := ?_ }
      · exact hetypRes
      · intro hp
        rw [hres]; unfold normalizeAppResultByProvenance
        split <;> simp [hpoisonEq, hp, joinPoison]
      · rw [hres]
      · rw [hres]; simp [hnl]
      · rw [hres]
      · rw [hres]; exact hge
      · intro k b hk
        exact applyPFnTClosure_extern_regime_preserve_some (happly := hplain) (k := k) (b := b)
          (hk := hk)
      · intro k b hk h
        exact applyPFnTClosure_extern_regime_preserve_some_back (happly := hplain) (k := k)
          (b := b) (hk := hk) (h := h)
      · intro k tv h
        exact applyPFnTClosure_extern_tagEnv_get_cases (happly := hplain) (k := k) (tv := tv)
          (h := h)
      · intro tm hbnd
        obtain ⟨tm', hext⟩ := ExternBatchTagMeaningExtension.canonical_general tm [spred]
          (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
          (BindEnv.bindParam tenv x bn) tagMapping cursor.1 nextTag' hbnd hcol
        refine ⟨tm', hext.extends_tm, ?_, ?_, ?_⟩
        · rw [hres]; exact hext.bounded
        · have hpr : PredRespectsTagMeaning tm' resolvedPred :=
            resolveSyntaxPred_respectsTagMeaning tm' spred _ _ tagMapping [spred] resolvedPred
              hext.2.2.1
              (List.mem_singleton_self _) hresolve
          intro qt' k dsc hin hdesc
          have hq := QTypInQTyp_eq_of_nonFunctionTarget hin (by rw [hetypRes]; rfl)
          subst hq
          have hp := qtypGuardDesc?_eq_some_pred_guardClosure hdesc
          rw [hres] at hp
          unfold normalizeAppResultByProvenance at hp
          split at hp
          · simp at hp
          · simp only [hpredEq] at hp
            rw [hpr k dsc.argName dsc.body dsc.capEnv hp]
        · rw [hres]; exact hext.within

/-- The `read` runtime output: an integer, from an unchanged config. -/
private theorem read_callRun_output {ap : Bool} {entry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun (readDecl ap) readImpl entry res cf o) :
    (∃ n : Int, o = Value.num n) ∧ cf = entry.callConfig := by
  cases hrun with
  | fn hfacts => have h := hfacts.kind_fn; simp [readDecl, pfnExternDecl] at h
  | pfn hfacts =>
      refine ⟨?_, hfacts.output_config⟩
      rcases hfacts.impl_success with
        ⟨implPfn, retSpec, vRaw, himpl, hretSpec, _hargMatch, _hrunImpl, hvalRet⟩
      have hret : retSpec = readRet := by
        simp only [readDecl, pfnExternDecl] at hretSpec
        exact (Option.some.inj hretSpec).symm
      subst hret
      simp only [readRet, validateExternReturn] at hvalRet
      split at hvalRet
      · rename_i hm
        simp only [Except.ok.injEq] at hvalRet
        subst hvalRet
        cases vRaw <;> simp [valueMatchesTyp] at hm
        exact ⟨_, rfl⟩
      · simp at hvalRet

private theorem read_facts {ap : Bool} {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call (readDecl ap) typedExpr entry res) :
    SimplePfnCallFacts entry.bodyCtx res true :=
  simplePfnCall_facts (spred := geGuard) rfl rfl htyped

private theorem SimplePfnCallFacts.monotoneExt {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    (hf : SimplePfnCallFacts ctx res poison) :
    Regime.monotoneStepExt ctx.regime res.regime' (fun k => ctx.nextTag ≤ k) := by
  refine ⟨fun k b _ hk => Or.inl (hf.regime_some k b hk), fun k hk => ?_⟩
  by_cases hlt : k < ctx.nextTag
  · left
    cases hb : res.regime'.lookup? k with
    | none => exact absurd hb hk
    | some b => rw [hf.regime_back k b hlt hb]; simp
  · exact Or.inr (Nat.le_of_not_lt hlt)

private theorem SimplePfnCallFacts.notfun {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    (hf : SimplePfnCallFacts ctx res poison) : res.qualType.etyp.isFunctionType = false := by
  rw [hf.etyp]; rfl

private theorem SimplePfnCallFacts.notref {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    (hf : SimplePfnCallFacts ctx res poison) : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
  rw [hf.etyp]; rintro ⟨_, h⟩; cases h

/-- The regime after the call is consistent with the stored and bound types. -/
private theorem SimplePfnCallFacts.consistent {predSat : PredSat} {ctx : TypeContext} {res : TypeResult}
    {poison : Bool} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hf : SimplePfnCallFacts ctx res poison) (htag : TagBoundedCtx ctx)
    (hcons : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  have h := consistentWithRegimeMasked_unmask (masked := fun _ => False) (fun _ h => h.elim)
    (consistentWithRegimeMasked_monotoneExt (fun _ => False) predSat ctx.regime res.regime' ctx
      μ ρ θ hf.monotoneExt (fun _ hk => hk) htag (consistentWithRegime_to_masked hcons))
  simp only [consistentWithRegime, ctxAfter] at h ⊢
  rw [hf.memEnv]
  exact h

private theorem read_callSingle (ap : Bool) : ExternCallBoundarySingle (readDecl ap) readImpl := by
  intro typedExpr res predSat β tm entry ctx htyped _hpredlaws hframe hwfTm hTmBounded
    θ cf o _hθwf _hwfCtx htagBnd hric _hreg hcons _hwfcfg hrdIn hrun hmatch _hpc
  have hf : SimplePfnCallFacts ctx res true := read_facts htyped
  obtain ⟨⟨n, ho⟩, hcf⟩ := read_callRun_output hrun
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

private theorem SimplePfnCallFacts.agree {predSat₀ predSat₁ : PredSat} {ctx : TypeContext}
    {res : TypeResult}
    {poison : Bool} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hf : SimplePfnCallFacts ctx res poison) (htag : TagBoundedCtx ctx)
    (hagree : agreeOnClean predSat₀ predSat₁ ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat₀ predSat₁ (ctxAfter ctx res).regime (ctxAfter ctx res) μ₀ ρ₀ θ₀ μ₁ ρ₁
      θ₁ := by
  refine ⟨fun l qt hlookup hclean => ?_, fun x qt hlookup hclean => ?_⟩
  · have hl : ctx.memEnv.lookup l = some qt := by
      have h : res.memEnv'.lookup l = some qt := by simpa [ctxAfter] using hlookup
      rwa [hf.memEnv] at h
    have hclean' : qtypCleanUnder res.regime' qt := by simpa [ctxAfter] using hclean
    have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hf.monotoneExt (fun _ hk => hk)
        (TagBoundedCtx_memEnv_predTagBounded htag hl) hclean'
    cases hagree.1 l qt hl hclean0 with
    | agree_values _ _ a₀ a₁ n₀ n₁ h0 h1 h2 h3 hv =>
        refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ h0 h1 h2 h3 ?_
        have hb : etypClosuresFullBounded qt.etyp ctx.nextTag := by
          rw [memEnv_lookup_etyp_int ctx.memEnv l qt hl]; trivial
        simpa [ctxAfter] using
          agreeValueUnder_clean_transport_by_cleanBack_ext hf.monotoneExt (fun _ hk => hk) hb
            hclean' hv
    | both_unrealized _ _ h0 h1 => exact agreeLocUnder.both_unrealized l qt h0 h1
  · have hx : ctx.varEnv.lookup x = some qt := by simpa [ctxAfter] using hlookup
    have hclean' : qtypCleanUnder res.regime' qt := by simpa [ctxAfter] using hclean
    have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hf.monotoneExt (fun _ hk => hk)
        (TagBoundedCtx_varEnv_predTagBounded htag hx) hclean'
    cases hagree.2 x qt hx hclean0 with
    | agree_values _ _ v₀ v₁ h0 h1 hv =>
        refine agreeVarUnder.agree_values x qt v₀ v₁ h0 h1 ?_
        simpa [ctxAfter] using
          agreeValueUnder_clean_transport_by_cleanBack_ext hf.monotoneExt (fun _ hk => hk)
            (TagBoundedCtx_varEnv_etypClosures htag hx) hclean' hv
    | both_none _ _ h0 h1 => exact agreeVarUnder.both_none x qt h0 h1

private theorem SimplePfnCallFacts.tagBounded {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    (hf : SimplePfnCallFacts ctx res poison) (htag : TagBoundedCtx ctx) :
    TagBoundedCtx (ctxAfter ctx res) := by
  obtain ⟨hte, ⟨hpv, hpm⟩, hcl⟩ := htag
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show tagEnvBounded res.tagEnv' res.nextTag'
    intro k hk
    cases h : res.tagEnv'.get? k with
    | none => exact absurd h hk
    | some tv =>
        rcases hf.tagEnv_cases k tv h with h' | ⟨_, hlt, _⟩
        · exact Nat.lt_of_lt_of_le (hte k (by rw [h']; exact Option.some_ne_none _)) hf.nextTag_le
        · exact hlt
  · exact predTagsBoundedInVarEnv_mono hpv hf.nextTag_le
  · show predTagsBoundedInMemEnv res.memEnv' res.nextTag'
    rw [hf.memEnv]; exact predTagsBoundedInMemEnv_mono hpm hf.nextTag_le
  · exact varEnvClosuresCapturedBounded_mono hcl hf.nextTag_le

private theorem SimplePfnCallFacts.regimeConsistent {ctx : TypeContext} {res : TypeResult}
    {poison : Bool} (hf : SimplePfnCallFacts ctx res poison) (hreg : regimeConsistentWithCtx ctx) :
    regimeConsistentWithCtx (ctxAfter ctx res) := by
  intro k deps h
  rcases hf.tagEnv_cases k _ h with h' | ⟨_, _, hr⟩
  · exact hf.regime_some k true (hreg k deps h')
  · simpa [ctxAfter] using hr

private theorem SimplePfnCallFacts.wfCtx {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    (hf : SimplePfnCallFacts ctx res poison) (hwf : wfTypeContext ctx) :
    wfTypeContext (ctxAfter ctx res) := by
  simp only [wfTypeContext, ctxAfter]
  rw [hf.memEnv, hf.nextLoc]
  exact hwf

private theorem SimplePfnCallFacts.runtime {ctx : TypeContext} {res : TypeResult} {poison : Bool}
    {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hf : SimplePfnCallFacts ctx res poison) (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    runtimeInstantiatesCtx (ctxAfter ctx res) μ ρ θ := by
  refine ⟨fun l a hl => ?_, fun hx => hric.2 hx⟩
  show res.memEnv'.contains l ∧ _
  rw [hf.memEnv]; exact hric.1 l a hl

private theorem read_callFR (ap : Bool) : ExternCallBoundaryFR (readDecl ap) readImpl := by
  intro postExpr typedExpr₀ _typedExpr₁ res predSat₀ predSat₁ β₀ β₁ tm entry₀ entry₁ ctx hctx₁
    htyped₀ _htyped₁ _hpredlaws₀ _hpredlaws₁ hframe₀ hframe₁ hwfTm hTmBounded θ₀ θ₁ hbody
    cf₀ cf₁ o₀ o₁ hrun₀ hrun₁ hmatch₀ hmatch₁ hagree
  have hf : SimplePfnCallFacts ctx res true := read_facts htyped₀
  obtain ⟨⟨n₀, ho₀⟩, hcf₀⟩ := read_callRun_output hrun₀
  obtain ⟨⟨n₁, ho₁⟩, hcf₁⟩ := read_callRun_output hrun₁
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

/-- `read` returns its argument, so a well-formed argument gives a well-formed
    result. -/
private theorem readImpl_operationalSafe (ap : Bool) :
    ExternOperationalSafe (readDecl ap) readImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl _ _ _ _ _ _ _ _
    simp [readImpl] at himpl
  · intro implPfn himpl env vArg mem addr vRaw hrun _hmem _henv harg
    simp only [readImpl, ExternImpl.pfn.injEq] at himpl
    subst himpl
    simp only [idImpl, Except.ok.injEq] at hrun
    subst hrun
    exact harg
  · intro v himpl _ _
    simp [readImpl] at himpl
  · intro implFn himpl
    simp [readImpl] at himpl

/-- The trusted entry of `read`. -/
theorem readSpec (ap : Bool) : ExternBoundarySpec (readDecl ap) readImpl where
  declFR := pfnExternDecl_declFR 7 "b" Typ.int readRet [] readImpl ap
  callFR := read_callFR ap
  declSingle := pfnExternDecl_declSingle 7 "b" Typ.int readRet [] readImpl ap
  callSingle := read_callSingle ap
  operational := readImpl_operationalSafe ap

/-- The trusted registry that holds `read` only. -/
def readReg (ap : Bool) : TrustedRegistry := [⟨readDecl ap, readImpl, readSpec ap⟩]

/-! ## Programs whose only extern is `read` -/

/-- The expressions built from variables, integers, operators, conditionals,
    `let`, functions, applications and declarations of `read`. -/
inductive ReadOnly (ap : Bool) : Expr → Prop where
  | read : ReadOnly ap (Expr.externPfn 7 "b" Typ.int ap SyntaxPredicate.noPred readRet [])
  | var (x : Name) : ReadOnly ap (.var x)
  | num (n : Int) : ReadOnly ap (.num n)
  | op {a b : Expr} (o : Op) : ReadOnly ap a → ReadOnly ap b → ReadOnly ap (.op a o b)
  | ite {a b c : Expr} :
      ReadOnly ap a → ReadOnly ap b → ReadOnly ap c → ReadOnly ap (.ite a b c)
  | vlet {a b : Expr} (x : Name) : ReadOnly ap a → ReadOnly ap b → ReadOnly ap (.vlet x a b)
  | fn {b : Expr} (x : Name) (t r : Typ) : ReadOnly ap b → ReadOnly ap (.fn x t b r)
  | app {a b : Expr} : ReadOnly ap a → ReadOnly ap b → ReadOnly ap (.app a b)

/-- The only extern declaration in such a program is `read`. -/
private theorem ReadOnly.decl {ap : Bool} {e : Expr} {id : ExternId} {d : ExternDeclaration}
    (hp : ExternDeclarationInProgram e id d) (h : ReadOnly ap e) :
    id = 7 ∧ d = readDecl ap := by
  induction hp with
  | externPfn => cases h; exact ⟨rfl, rfl⟩
  | externPfn_return hret =>
      cases h
      unfold readRet at hret
      cases hret
  | op_left _ ih => cases h; exact ih ‹_›
  | op_right _ ih => cases h; exact ih ‹_›
  | ite_cond _ ih => cases h; exact ih ‹_›
  | ite_then _ ih => cases h; exact ih ‹_›
  | ite_else _ ih => cases h; exact ih ‹_›
  | vlet_bound _ ih => cases h; exact ih ‹_›
  | vlet_body _ ih => cases h; exact ih ‹_›
  | fn_body _ ih => cases h; exact ih ‹_›
  | fn_extern_body_runtime => cases h; contradiction
  | app_fun _ ih => cases h; exact ih ‹_›
  | app_arg _ ih => cases h; exact ih ‹_›
  | _ => cases h

/-! ## The context, the runs and the specifications -/

/-- The starting context of a witness program: the variables `vars` and the
    extern policy `pol`, and nothing else. -/
def ctxOf (pol : ExternId → Tag → Option Bool) (vars : VarTypeEnv) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := vars, tagEnv := ∅,
    nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := pol }

/-- The starting configuration of a run: the variables `ρ`, the empty memory and
    the registry of `read`. -/
def runCfg (ρ : VarEnv) : Config :=
  { memory := ∅, varEnv := ρ, nextAddr := 0, pureMode := false, registry := reg }

/-- No critical input; the scenario commits the tags of `read`. -/
def sRead : InputSpec := { locs := ∅, vars := ∅, regimeExterns := [7] }

/-- Nothing is observed. -/
def obsNone : ObservableSpec := { locs := ∅, retEtyp? := none }

/-- The variables of a run hold integers, one for each variable of the context. -/
structure IntRun (vars : VarTypeEnv) (ρ : VarEnv) : Prop where
  wf : wfVarEnv 0 ρ
  inst : ∀ x qt, vars.lookup x = some qt → ∃ n : Int, ρ.lookup x = some (.num n)

private theorem pInt_not_clean (R : Regime) : ¬ qtypCleanUnder R pInt := by
  intro h
  cases h with
  | clean hpoison => simp [pInt] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, pInt] at htag

private theorem reg_noVal {id : ExternId} {v : Value} (h : reg.get? id = some (.val v)) :
    False := by
  by_cases hid : id = 7
  · subst hid
    rw [reg_get] at h
    cases h
  · simp [reg, emptyExternRegistry, Ne.symm hid] at h

section Premises

variable {pol : ExternId → Tag → Option Bool} {vars : VarTypeEnv}

private theorem externRegimeMatches
    (hpol : ∀ id, id ≠ 7 → ∀ k, pol id k = none) (hpol7 : ∀ k, ∃ b, pol 7 k = some b) :
    ExternRegimeMatchesInputSpec sRead (ctxOf pol vars) := by
  refine ⟨fun {id} hid k => hpol id (by simpa [sRead] using hid) k, fun {id} hid k => ?_⟩
  simp only [sRead, List.mem_singleton] at hid
  subst hid
  exact hpol7 k

private theorem trusted {ap : Bool} {prog : Expr} (hprog : ReadOnly ap prog)
    (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    InitialContextTrusted (readReg ap) prog (ctxOf pol vars) := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      obtain ⟨rfl, rfl⟩ := ReadOnly.decl hp hprog
      simp [readReg, TrustedRegistry.lookup?, readDecl, pfnExternDecl] at hlookup
      subst hlookup
      rfl
  | var hlk hqt =>
      have hq := hvars _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

private theorem wfSpec : wfInputSpec sRead := by
  unfold wfInputSpec
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l qt h
    simp [sRead, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · refine And.intro ?_ ?_
      · exact Std.ExtTreeMap.nodup_keys
      · intro x qt h
        simp [sRead, VarTypeEnv.lookup] at h
    · intro x qt h
      simp [sRead, VarTypeEnv.lookup] at h
  · intro x qt h
    simp [sRead, VarTypeEnv.lookup] at h

private theorem wfObs : wfObsSpec obsNone := by
  simp [wfObsSpec, obsNone]

private theorem ctxMatches (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    ctxMatchesInputSpec sRead (ctxOf pol vars) := by
  unfold ctxMatchesInputSpec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l qt h
    simp [sRead, MemoryTypeEnv.lookup] at h
  · intro x qt h
    simp [sRead, VarTypeEnv.lookup] at h
  · intro l qt k h
    simp [ctxOf, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · intro x qt k h htag _
      rw [hvars x qt h] at htag
      simp [qtypGuardTag, pInt] at htag
    · intro x qt h
      rw [hvars x qt h]
      exact deepQTypProperty.other _ _ trivial

private theorem wfCtx (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    wfTypeContext (ctxOf pol vars) := by
  unfold wfTypeContext
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l h
    simp [ctxOf] at h
  · intro x qt h
    rw [hvars x qt h]
    exact trivial
  · intro x qt h
    rw [hvars x qt h]
    exact trivial

private theorem tagBounded (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    TagBoundedCtx (ctxOf pol vars) := by
  unfold TagBoundedCtx
  refine And.intro ?_ (And.intro (And.intro ?_ ?_) ?_)
  · intro k hk
    simp [ctxOf] at hk
  · intro x qt h
    rw [hvars x qt h]
    exact trivial
  · intro l qt h
    simp [ctxOf, MemoryTypeEnv.lookup] at h
  · intro x qt h
    rw [hvars x qt h]
    exact trivial

private theorem wfTm (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    wfTagMeaningCtx ∅ (ctxOf pol vars) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
      have hroot := hvars x qtRoot hlookup
      subst hroot
      have hqt : qt = pInt :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [pInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, pInt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
      simp [ctxOf, MemoryTypeEnv.lookup] at hlookup

private theorem tmBounded : TagMeaningBounded ∅ (ctxOf pol vars).nextTag := by
  intro k d h
  simp [TagMeaning.lookup] at h

private theorem lawsEmpty {β : BindVals} : PredSatLaws geSat ∅ β :=
  predSatLaws_geSat (fun k d h => by simp [TagMeaning.lookup] at h)

private theorem wfRegime₀ : wfRegime (ctxOf pol vars).regime sRead := by
  have htags : inputSpecTags sRead = [] := rfl
  refine And.intro ?_ ?_
  · intro k hk
    rw [htags] at hk
    cases hk
  · intro k hk
    simp [ctxOf, Regime.lookup?] at hk

private theorem wfθ₀ : wfRealizationMap ∅ := by
  intro l₁ l₂ a h
  simp [RealizationMap.lookup] at h

private theorem wfC {ρ : VarEnv} (hρ : IntRun vars ρ) : wfConfig (runCfg ρ) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [runCfg] at h
  · exact hρ.wf

private theorem reservedWF : RegistryReservedWF reg ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (reg_noVal h).elim

private theorem discipline :
    ReservedDiscipline reg (ctxOf pol vars).declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (reg_noVal h).elim
  · intro id a h _ l
    exact (reg_noVal h).elim

private theorem instantiates {ρ : VarEnv} (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt)
    (hρ : IntRun vars ρ) : runtimeInstantiatesCtx (ctxOf pol vars) ∅ ρ ∅ := by
  refine And.intro ?_ ?_
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    obtain ⟨n, hn⟩ := hρ.inst x qt h
    rw [hvars x qt h]
    exact ⟨_, hn, valueHasETyp.num n⟩

private theorem trustedInit {ρ : VarEnv} (hρ : IntRun vars ρ) :
    trustedVarsClosureRegimeInit geSat (ctxOf pol vars).regime sRead (ctxOf pol vars) ∅ ρ ∅ := by
  refine trustedVarsClosureRegimeInit.intro ?_
  intro x qt v h _ hv
  obtain ⟨n, hn⟩ := hρ.inst x qt h
  rw [hn] at hv
  obtain rfl := Option.some.inj hv
  exact closureCapturedVarsRegime.intro
    (deepValueQTypProperty.nonClosure (fun _ _ _ hc => by cases hc)
      (fun _ _ _ hc => by cases hc))

private theorem consistent {ρ : VarEnv} :
    consistentRegimeSpec geSat (ctxOf pol vars).regime sRead ∅ ρ ∅ := by
  unfold consistentRegimeSpec
  have hnil : memEnvToLocQTypList sRead.locs = [] := rfl
  have hnil' : sRead.vars.toList = [] := rfl
  rw [hnil, hnil']
  exact ⟨trivial, trivial⟩

private theorem agreeCritical {ρ₁ ρ₂ : VarEnv} :
    agreeOnCriticalInputsUnderRegimeSpec geSat geSat (ctxOf pol vars).regime sRead ∅ ρ₁ ∅ ∅ ρ₂
      ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [sRead, MemoryTypeEnv.lookup] at h
  · intro x qt h _
    simp [sRead, VarTypeEnv.lookup] at h

private theorem agreeTrusted {ρ₁ ρ₂ : VarEnv}
    (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) :
    agreeOnTrustedInputs geSat geSat (ctxOf pol vars).regime sRead (ctxOf pol vars)
      ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [ctxOf, MemoryTypeEnv.lookup] at h
  · intro x qt h _ hclean
    rw [hvars x qt h] at hclean
    exact absurd hclean (pInt_not_clean _)

end Premises

/-! ## The theorem at a witness program -/

/-- **The theorem at a program whose only extern is `read`.** The context
    holds poisoned integers and the policy `pol` commits every tag of `read`
    and no other. Given the typing run with the laws on its table, two runs
    from integer variables, and the premises on extern calls, the theorem
    applies: every other premise is proved here. -/
theorem closed_of {pol : ExternId → Tag → Option Bool} {vars : VarTypeEnv} {ap : Bool}
    {prog : Expr} {fuel : Nat} {res : TypeResult} {ρ₁ ρ₂ : VarEnv} {cf₁ cf₂ : Config}
    {o₁ o₂ : Value} {β₁ β₂ : BindVals}
    (hpol : ∀ id, id ≠ 7 → ∀ k, pol id k = none) (hpol7 : ∀ k, ∃ b, pol 7 k = some b)
    (hvars : ∀ x qt, vars.lookup x = some qt → qt = pInt) (hprog : ReadOnly ap prog)
    (htc : typecheck (ctxOf pol vars) prog fuel = .ok res)
    (hlaws : ∀ β, PredSatLaws geSat (programTable ∅ res.tagLog') β)
    (hρ₁ : IntRun vars ρ₁) (hρ₂ : IntRun vars ρ₂)
    (hm₁ : ExternCallsMatch geSat ⟨ctxOf pol vars, prog, fuel, runCfg ρ₁⟩)
    (hm₂ : ExternCallsMatch geSat ⟨ctxOf pol vars, prog, fuel, runCfg ρ₂⟩)
    (ht₁ : TestsAgreeWithView β₁ ⟨ctxOf pol vars, prog, fuel, runCfg ρ₁⟩)
    (ht₂ : TestsAgreeWithView β₂ ⟨ctxOf pol vars, prog, fuel, runCfg ρ₂⟩)
    (hag : ExternCallsAgree ⟨ctxOf pol vars, prog, fuel, runCfg ρ₁⟩
      ⟨ctxOf pol vars, prog, fuel, runCfg ρ₂⟩)
    (hrun₁ : terminatesTo prog (runCfg ρ₁) cf₁ o₁)
    (hrun₂ : terminatesTo prog (runCfg ρ₂) cf₂ o₂) :
    ∃ θ₁' θ₂' : RealizationMap, wfExtendsMap ∅ θ₁' ∧ wfExtendsMap ∅ θ₂' ∧
      observablesEqual obsNone θ₁' θ₂' cf₁ cf₂ o₁ o₂ :=
  TypeSystemEnforcesFaultRobustness (readReg ap) prog sRead obsNone (ctxOf pol vars)
    (externRegimeMatches hpol hpol7) (trusted hprog hvars) wfSpec wfObs (ctxMatches hvars)
    (wfCtx hvars) rfl rfl rfl (tagBounded hvars) ∅ (wfTm hvars) tmBounded
    fuel res htc
    (And.intro (fun _ h => by simp [obsNone] at h)
      (fun _ _ h => by simp [obsNone, MemoryETypEnv.lookup] at h))
    ∅ ∅ ρ₁ ρ₂ ∅ ∅ 0 0 false cf₁ cf₂ o₁ o₂ geSat geSat β₁ β₂ lawsEmpty lawsEmpty
    (hlaws β₁) (hlaws β₂) wfRegime₀ wfθ₀ wfθ₀ (wfC hρ₁) (wfC hρ₂)
    reservedWF reservedWF discipline discipline
    (And.intro (fun h _ => by simp [sRead] at h)
      (fun h _ => by simp [sRead, VarTypeEnv.lookup] at h))
    (And.intro (fun h _ => by simp [sRead] at h)
      (fun h _ => by simp [sRead, VarTypeEnv.lookup] at h))
    (instantiates hvars hρ₁) (instantiates hvars hρ₂) (trustedInit hρ₁) (trustedInit hρ₂)
    consistent consistent hm₁ hm₂ ht₁ ht₂ agreeCritical (agreeTrusted hvars) hag hrun₁ hrun₂

/-! ## The theorem at the four programs

Each program of `ExternCallsWitness` with two runs for which the premises on
extern calls hold: `Wrapper` and `Skipped` with two copies of their run under
the vector the run follows, `TwoRuns` with two runs from `x = 5`, and
`TwoCalls` with two runs from `x = 5, y = 7`. -/

private theorem on7_ne (f : Tag → Bool) : ∀ id, id ≠ 7 → ∀ k, on7 f id k = none := by
  intro id h k
  simp [on7, h]

private theorem on7_7 (f : Tag → Bool) : ∀ k, ∃ b, on7 f 7 k = some b :=
  fun k => ⟨f k, by simp [on7]⟩

private theorem vars_empty : ∀ x qt, (∅ : VarTypeEnv).lookup x = some qt → qt = pInt := by
  intro x qt h
  simp [VarTypeEnv.lookup] at h

private theorem vars_update {vars : VarTypeEnv}
    (h : ∀ x qt, vars.lookup x = some qt → qt = pInt) (y : Name) :
    ∀ x qt, (vars.update y pInt).lookup x = some qt → qt = pInt := by
  intro x qt hx
  by_cases hxy : x = y
  · subst hxy
    rw [VarTypeEnv_lookup_update_eq] at hx
    exact (Option.some.inj hx).symm
  · rw [VarTypeEnv_lookup_update_ne vars y x pInt hxy] at hx
    exact h x qt hx

private theorem intRun_empty : IntRun ∅ [] :=
  ⟨wfVarEnv.nil, fun x qt h => by simp [VarTypeEnv.lookup] at h⟩

private theorem IntRun.update {vars : VarTypeEnv} {ρ : VarEnv} (h : IntRun vars ρ) (y : Name)
    (n : Int) : IntRun (vars.update y pInt) (VarEnv.update ρ y (.num n)) := by
  refine ⟨wfVarEnv.cons _ _ _ (wfValue.num n) h.wf, fun x qt hx => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact ⟨n, by simp [VarEnv.update, VarEnv.lookup]⟩
  · rw [VarTypeEnv_lookup_update_ne vars y x pInt hxy] at hx
    obtain ⟨m, hm⟩ := h.inst x qt hx
    have hb : (x == y) = false := beq_false_of_ne hxy
    exact ⟨m, by simpa [VarEnv.update, VarEnv.lookup, List.lookup, hb] using hm⟩

/-- Whether an evaluation succeeds. -/
private def runOk : EvalResult → Bool
  | .success _ _ => true
  | _ => false

private theorem terminates_of_runOk {n : Nat} {c : Config} {e : Expr}
    (h : runOk (beval n c e false) = true) : ∃ cf o, terminatesTo e c cf o := by
  cases hrun : beval n c e false with
  | success cf o => exact ⟨cf, o, n, false, hrun⟩
  | outOfFuel => rw [hrun] at h; cases h
  | runtimeError _ => rw [hrun] at h; cases h

/-- What the theorem concludes for two runs of `prog` that start from `c₁` and
    `c₂`, with nothing observed: both runs terminate, and the realisation maps
    extend. -/
def ConclusionAt (prog : Expr) (c₁ c₂ : Config) : Prop :=
  ∃ (cf₁ cf₂ : Config) (o₁ o₂ : Value),
    terminatesTo prog c₁ cf₁ o₁ ∧ terminatesTo prog c₂ cf₂ o₂ ∧
    ∃ θ₁' θ₂' : RealizationMap, wfExtendsMap ∅ θ₁' ∧ wfExtendsMap ∅ θ₂' ∧
      observablesEqual obsNone θ₁' θ₂' cf₁ cf₂ o₁ o₂

/-- **The theorem at `Wrapper`**, two copies of its run under the vector it
    follows (tag 0 true, tag 1 false). -/
theorem wrapper_closed : ConclusionAt Wrapper.prog Wrapper.cfg0 Wrapper.cfg0 := by
  obtain ⟨htc, hmatch, hlaws⟩ := Wrapper.prog_real
  obtain ⟨cf, o, hrun⟩ :=
    terminates_of_runOk (n := 20) (c := Wrapper.cfg0) (e := Wrapper.prog) (by
      simp [beval, bevalFunctionBody, Wrapper.prog, Wrapper.B1, Wrapper.B2, Wrapper.B3,
        Wrapper.A1, Wrapper.A2, Wrapper.fnF, Wrapper.bodyF, neg3, Wrapper.cfg0, readD, readRet,
        VarEnv.lookup, VarEnv.update, reg_get', validateExternReturn, valueMatchesTyp, idImpl,
        List.lookup, evalOp, runOk])
  exact ⟨cf, cf, o, o, hrun, hrun,
    closed_of (pol := Wrapper.real) (vars := ∅) (ρ₁ := []) (ρ₂ := []) (on7_ne _) (on7_7 _)
      (β₁ := fun _ => none) (β₂ := fun _ => none)
      vars_empty (by repeat constructor) htc hlaws intRun_empty intRun_empty
      (hmatch geSat (fun _ => none) (hlaws _)) (hmatch geSat (fun _ => none) (hlaws _))
        (Wrapper.tests_real _)
      (Wrapper.tests_real _) Wrapper.agree_self hrun hrun⟩

/-- **The theorem at `Skipped`**, two copies of its run under the vector
    `realF` (tag 0 true, tags 1 and 2 false). -/
theorem skipped_closed : ConclusionAt Skipped.prog Wrapper.cfg0 Wrapper.cfg0 := by
  obtain ⟨_, htc, _, _, _, hmatch, _, hlaws, _⟩ := Skipped.prog_real
  obtain ⟨cf, o, hrun⟩ :=
    terminates_of_runOk (n := 20) (c := Wrapper.cfg0) (e := Skipped.prog) (by
      simp [beval, Skipped.prog, Skipped.Q1, Skipped.IT, Skipped.R1, Skipped.R2, Skipped.R3,
        ge0, neg3, Wrapper.cfg0, readD, readRet, VarEnv.lookup, VarEnv.update, reg_get',
        validateExternReturn, valueMatchesTyp, idImpl, List.lookup, evalOp, runOk])
  exact ⟨cf, cf, o, o, hrun, hrun,
    closed_of (pol := Skipped.realF) (vars := ∅) (ρ₁ := []) (ρ₂ := []) (on7_ne _) (on7_7 _)
      (β₁ := fun _ => none) (β₂ := fun _ => none)
      vars_empty (by repeat constructor) htc hlaws intRun_empty intRun_empty
      (hmatch geSat (fun _ => none) (hlaws _)) (hmatch geSat (fun _ => none) (hlaws _))
        (Skipped.tests_realF _)
      (Skipped.tests_realF _) Skipped.agree_self hrun hrun⟩

/-- **The theorem at `TwoRuns`**, two runs from `x = 5`. -/
theorem twoRuns_closed : ConclusionAt TwoRuns.prog (TwoRuns.cfgX 5) (TwoRuns.cfgX 5) := by
  obtain ⟨htc, _, _, hmatch, hlaws, hagree, _⟩ := TwoRuns.agree_case
  obtain ⟨cf, o, hrun⟩ :=
    terminates_of_runOk (n := 20) (c := TwoRuns.cfgX 5) (e := TwoRuns.prog) (by
      simp [beval, TwoRuns.prog, TwoRuns.call, TwoRuns.cfgX, readD, readRet, VarEnv.lookup,
        VarEnv.update, reg_get', validateExternReturn, valueMatchesTyp, idImpl, List.lookup,
        runOk])
  exact ⟨cf, cf, o, o, hrun, hrun,
    closed_of (pol := TwoRuns.allT) (vars := (∅ : VarTypeEnv).update "x" pInt)
      (ρ₁ := VarEnv.update [] "x" (.num 5)) (ρ₂ := VarEnv.update [] "x" (.num 5))
      (on7_ne _) (on7_7 _) (vars_update vars_empty "x") (by repeat constructor) htc hlaws
      (intRun_empty.update "x" 5) (intRun_empty.update "x" 5)
      (β₁ := fun _ => none) (β₂ := fun _ => none)
      (hmatch geSat (fun _ => none) (hlaws _)).1 (hmatch geSat (fun _ => none) (hlaws _)).1
        (TwoRuns.tests 5 _)
      (TwoRuns.tests 5 _) hagree hrun hrun⟩

/-- **The theorem at `TwoCalls`**, two runs from `x = 5, y = 7`. Each run makes
    two tagged calls, which return 5 and 7. -/
theorem twoCalls_closed :
    ConclusionAt TwoCalls.prog (TwoCalls.cfg0 5 7) (TwoCalls.cfg0 5 7) := by
  obtain ⟨htc, hmatch, hlaws, hagree, _⟩ := TwoCalls.two_calls_case
  obtain ⟨cf, o, hrun⟩ :=
    terminates_of_runOk (n := 20) (c := TwoCalls.cfg0 5 7) (e := TwoCalls.prog) (by
      simp [beval, TwoCalls.prog, TwoCalls.Q, TwoCalls.C1, TwoCalls.C2, TwoCalls.cfg0, readD,
        readRet, VarEnv.lookup, VarEnv.update, reg_get', validateExternReturn, valueMatchesTyp,
        idImpl, List.lookup, runOk])
  have hρ := (intRun_empty.update "x" 5).update "y" 7
  exact ⟨cf, cf, o, o, hrun, hrun,
    closed_of (pol := TwoCalls.allT)
      (vars := ((∅ : VarTypeEnv).update "x" pInt).update "y" pInt)
      (on7_ne _) (on7_7 _) (vars_update (vars_update vars_empty "x") "y")
      (β₁ := fun _ => none) (β₂ := fun _ => none)
      (by repeat constructor) htc hlaws hρ hρ (hmatch geSat (fun _ => none) (hlaws _)).1
      (hmatch geSat (fun _ => none) (hlaws _)).1 (TwoCalls.tests 5 7 _) (TwoCalls.tests 5 7 _)
        hagree hrun hrun⟩

end ExternCallsWitness
