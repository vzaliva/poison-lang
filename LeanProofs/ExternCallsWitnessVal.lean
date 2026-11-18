import LeanProofs.ExternCallsWitnessBase
import LeanProofs.FaultRobustnessProofs

/-!
# A trusted entry for a guarded `extern val`

`@250` is an extern value with a guard:

    extern val @250 : (int :> poisoned { 0, w => w >= 0 })

The typechecker types the declaration as a call of a constant pure extern
function with a simple return: the guard gets a fresh tag, the assignment of
values to the tags that externs allocate (`externRegime` of the context)
gives that tag its value, and the guard is recorded in the tag environment.

This module gives a trusted entry for `@250` whose implementation is the
value `m`, with the declaration contracts proved from the premise *match* on
the declared value (`ValMatches`), and applies the top-level theorem to a
program that declares the value and tests it, under both values of the tag.

* The entry. `v_declSingle` and `v_declFR` are the declaration contracts of
  `vDecl` with the implementation `vI m`; `vSpec` collects them with the call
  contracts (no call is typed against a declaration of kind `val`) and
  operational safety, and `vReg` is the trusted registry that holds `@250`
  alone. The single-run contract moves the consistency of the context to the
  regime after the declaration from the tag meaning of the context. The
  two-run contract proves *agreement* of the declared value: both runs read
  the same implementation.
* The program `prog`,
  `let v = extern val @250 : (int :> poisoned { 0, w => w >= 0 }) in if v >= 0 then v else 0`,
  typed under the assignment `polV b`, which gives every tag of `@250` the
  value `b`. Under both assignments it is a clean `int`. `match_iff`: *match*
  holds in a run exactly when `0 ≤ m ↔ b = true`; `val_case` proves it for
  the tag true with `m = 5` and the tag false with `m = -3`, and refutes it
  for the two other pairs. `agree`: *agreement* holds for every pair of runs,
  which make no extern call.
* `same_return`: under an assignment that the value matches, two runs from
  any `x` return the same value. `true_5`: tag true, value 5; the runs from
  `x = 4` and `x = 5` return 5. `false_neg3`: tag false, value -3; they
  return 0.

Limits. The proofs of the entry are specific to `@250`: one guard, on an
`int`. The runs differ only in `x`, which the program does not read.
-/

open Std LeanPoison

namespace ExternCallsWitness

namespace Val

/-! ## Consistency under the regime after the declaration

The declaration gives values to its fresh tags only. A regime that agrees
with the old one below `nextTag` keeps every fact of `consistentWithRegime`:
a guard without predicate imposes nothing, and the tag of a guard with a
predicate reachable from the environments, at any depth of closures, has an
entry in the tag meaning and is therefore below `nextTag`. -/

/-- `R'` agrees with `R` at the tag of every closure guard reachable from `qt`. -/
private def GoodIn (R R' : Regime) (qt : QTyp) : Prop :=
  ∀ qt', QTypInQTyp qt' qt → ∀ k a b c, qt'.pred = .guardClosure k a b c →
    R'.lookup? k = R.lookup? k

private theorem varsRegime_transport {predSat : PredSat} {R R' : Regime} {μ : Memory} {ρ : VarEnv}
    {e : Name × QTyp}
    (hk : ∀ k a b c, e.2.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : varsRegime predSat R μ ρ e) : varsRegime predSat R' μ ρ e := by
  cases h with
  | noPred_ok hp => exact .noPred_ok _ hp
  | guardOnly_ok k hgo => exact .guardOnly_ok _ k hgo
  | withPred_ok k a b c v bb hclos hregime hvar hcons =>
      exact .withPred_ok _ k a b c v bb hclos (by rw [hk k a b c hclos]; exact hregime) hvar hcons

private theorem locsRegime_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {θ : RealizationMap} {e : Loc × QTyp}
    (hk : ∀ k a b c, e.2.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : locsRegime predSat R μ θ e) : locsRegime predSat R' μ θ e := by
  cases h with
  | noPred_ok hp => exact .noPred_ok _ hp
  | guardOnly_ok k hgo => exact .guardOnly_ok _ k hgo
  | withPred_ok k a b c addr n bb hclos hregime hreal hmem hcons =>
      exact .withPred_ok _ k a b c addr n bb hclos (by rw [hk k a b c hclos]; exact hregime)
        hreal hmem hcons

/-- One level: an entry of a captured environment. -/
private theorem captured_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {σcap : CapturedVarEnv} {ρcap : VarEnv}
    (hgood : ∀ x qt_x, σcap.lookup x = some qt_x →
      ∀ k a b c, qt_x.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
    capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hg hR'
  cases hp : qt_x.pred with
  | noPred => simp [qtypGuardTag, hp] at hg
  | guardOnly k => exact .guardOnly_ok _ k hp
  | guardClosure k a b c =>
      have hkx : k = k_x := by simpa [qtypGuardTag, hp] using hg
      subst hkx
      have heq := hgood x qt_x hlook k a b c hp
      have hR : R.lookup? k ≠ none := by rw [← heq]; exact hR'
      exact varsRegime_transport (fun k' a' b' c' h' => by
        rw [hp] at h'; cases h'; exact heq) (h x qt_x k hlook hg hR)

/-- The deep part: every nesting level of a closure value. -/
private theorem deep_transport {predSat : PredSat} {R R' : Regime} {μ : Memory} {θ : RealizationMap}
    {qt : QTyp} {v : Value}
    (hdeep : deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
          capturedVarsTypingProperty θ σcap ρcap) qt v) :
    GoodIn R R' qt →
    deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R' μ σcap ρcap ∧
          capturedVarsTypingProperty θ σcap ρcap) qt v := by
  induction hdeep with
  | nonClosure hv hpe => intro _; exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem hPT _hrec hbody ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => QTypInQTyp.in_arrow qt_x _ st1 st2 p tcls _ x hetyp hmem
          (by simpa [fnCapturedEnv] using List_lookup_some_mem x qt_x σcap hs)
      refine .closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs)))) hbody
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => QTypInQTyp.in_arrow qt_x _ _ _ p tcls _ x hetyp hmem
          (by simpa [fnCapturedEnv] using List_lookup_some_mem x qt_x σcap hs)
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => QTypInQTyp.in_parrow qt_x _ st1 st2 p tcls _ x hetyp hmem
          (by simpa [pfnCapturedEnv] using List_lookup_some_mem x qt_x σcap hs)
      exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => QTypInQTyp.in_parrow qt_x _ _ _ p tcls _ x hetyp hmem
          (by simpa [pfnCapturedEnv] using List_lookup_some_mem x qt_x σcap hs)
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))

/-- A closure guard reachable from the environments has a tag below `nextTag`. -/
private theorem guardClosure_lt {tm : TagMeaning} {ctx : TypeContext} {qt : QTyp}
    {k : Tag} {a : Name} {b : PExpr} {c : CapturedVarEnv}
    (hwfTm : wfTagMeaningCtx tm ctx) (htmb : TagMeaningBounded tm ctx.nextTag)
    (hin : QTypInEnvs qt ctx.varEnv ctx.memEnv) (hp : qt.pred = .guardClosure k a b c) :
    k < ctx.nextTag := by
  rcases hwfTm with ⟨h⟩
  exact htmb k _ (h (GuardDescInEnvsDeep.intro qt k { argName := a, body := b, capEnv := c } hin
    (by simp [qtypGuardDesc?, hp])))

/-- Consistency of the context moves to a regime that agrees with the old one
    below `nextTag`, given the tag meaning of the context. -/
private theorem consistentWithRegime_of_agreeBelow {predSat : PredSat} {R R' : Regime}
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap} {tm : TagMeaning}
    (hwfTm : wfTagMeaningCtx tm ctx) (htmb : TagMeaningBounded tm ctx.nextTag)
    (hbelow : ∀ k, k < ctx.nextTag → R'.lookup? k = R.lookup? k)
    (h : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R' ctx μ ρ θ := by
  obtain ⟨hm, hv, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hR'
    cases hp : qt.pred with
    | noPred => simp [qtypGuardTag, hp] at hguard
    | guardOnly k' => exact .guardOnly_ok _ k' hp
    | guardClosure k' a b c =>
        have hkk : k' = k := by simpa [qtypGuardTag, hp] using hguard
        subst hkk
        have hlt := guardClosure_lt hwfTm htmb
          (QTypInEnvs.inMem _ _ l qt qt hlookup (QTypInQTyp.self qt)) hp
        have heq := hbelow k' hlt
        exact locsRegime_transport (fun k'' a' b' c' h' => by
            rw [hp] at h'; cases h'; exact heq)
          (hm l qt k' hlookup hguard (by rw [← heq]; exact hR'))
  · intro x qt k hlookup hguard hR'
    cases hp : qt.pred with
    | noPred => simp [qtypGuardTag, hp] at hguard
    | guardOnly k' => exact .guardOnly_ok _ k' hp
    | guardClosure k' a b c =>
        have hkk : k' = k := by simpa [qtypGuardTag, hp] using hguard
        subst hkk
        have hlt := guardClosure_lt hwfTm htmb
          (QTypInEnvs.inVar _ _ x qt qt hlookup (QTypInQTyp.self qt)) hp
        have heq := hbelow k' hlt
        exact varsRegime_transport (fun k'' a' b' c' h' => by
            rw [hp] at h'; cases h'; exact heq)
          (hv x qt k' hlookup hguard (by rw [← heq]; exact hR'))
  · intro x qt v hlookup hρ
    obtain ⟨hdeep⟩ := hc x qt v hlookup hρ
    exact ⟨deep_transport hdeep (fun qt' hin k a b c hp =>
      hbelow k (guardClosure_lt hwfTm htmb (QTypInEnvs.inVar _ _ x qt' qt hlookup hin) hp))⟩

/-! ## The entry -/

/-- `extern val @250 : (int :> poisoned { 0, w => w >= 0 })`. -/
def vDecl : ExternDeclaration :=
  { id := 250, kind := .val, typ := .int, argName := none, retSpec := none,
    effects := [], preds := [geGuard], argPoison := false }

/-- The implementation: the value `n`. -/
def vI (n : Int) : ExternImpl := .val (.num n)

/-- The tag mapping of the declaration at cursor `c`: index 0 gets `c`. -/
private def vMap (c : Tag) : TagMapping := (∅ : TagMapping).insert ⟨0⟩ c

private theorem v_alloc (c : Tag) : collectAndAllocExternTags [geGuard] c = .ok (vMap c, c + 1) := by
  rfl

private theorem v_log (env : VarTypeEnv) (c : Tag) :
    ∃ a ∈ externTagLog [geGuard] env (vMap c), a.tag = c := by
  simp [externTagLog, geGuard, vMap]
  exact ⟨_, rfl, rfl⟩

private theorem v_resolve {env : VarTypeEnv} {c : Tag} {rp : Predicate}
    (h : resolveSyntaxPred geGuard env (vMap c) = .ok rp) :
    ∃ arg body cap, rp = .guardClosure c arg body cap := by
  have hget : (vMap c).get? ⟨0⟩ = some c := rfl
  simp only [geGuard, resolveSyntaxPred, hget, bind, Except.bind, pure, Except.pure] at h
  cases hp : ((Expr.var "w").op Op.gte (Expr.num 0)).toPExpr with
  | error e => simp [hp] at h
  | ok pb =>
      simp only [hp, Except.ok.injEq] at h
      exact ⟨_, _, _, h.symm⟩

private theorem vPolicy_lookup (R : Regime) (id : ExternId) (pol : ExternId → Tag → Option Bool)
    (c k : Tag) (hk : k ≠ c) :
    (applyExternRegimePolicy R id pol (vMap c)).lookup? k = R.lookup? k := by
  have hR : applyExternRegimePolicy R id pol (vMap c) =
      (match pol id c with
       | some b => match R.lookup? c with
                   | none => R.insert c b
                   | some _ => R
       | none => R) := rfl
  rw [hR]
  cases pol id c with
  | none => rfl
  | some b =>
      cases R.lookup? c with
      | none =>
          have hcmp : compare c k ≠ .eq := by
            intro h; exact hk ((Nat.compare_eq_eq).1 h).symm
          simp [Regime.lookup?, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, hcmp]
      | some _ => rfl

/-- What the typing of the declaration gives. -/
private structure VFacts (ctx : TypeContext) (res : TypeResult) : Prop where
  etyp : res.qualType.etyp = .int
  poison : res.qualType.poison = true
  guard : ∃ arg body cap, res.qualType.pred = .guardClosure ctx.nextTag arg body cap
  logged : ∃ a ∈ res.tagLog', a.tag = ctx.nextTag
  nextTag : res.nextTag' = ctx.nextTag + 1
  memEnv : res.memEnv' = ctx.memEnv
  nextLoc : res.nextLoc' = ctx.nextLoc
  declared : res.declared' = 250 :: ctx.declaredExternRefs
  regime : ∀ k, k ≠ ctx.nextTag → res.regime'.lookup? k = ctx.regime.lookup? k

private theorem v_facts_of {ctx : TypeContext} {poison : Bool} {fuel : Nat} {res : TypeResult}
    (htc : typecheckExternVal ctx 250 .int poison geGuard fuel = .ok res) : VFacts ctx res := by
  obtain ⟨hpz, tagMapping, nextTag', rp, ⟨qt, ctx'⟩, halloc, hres, hsurf, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  rw [v_alloc] at halloc
  simp only [Except.ok.injEq, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  have hp : poison = true := by
    cases poison with
    | true => rfl
    | false => have h := hpz rfl; simp [geGuard] at h
  subst hp
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at hsurf
  obtain ⟨rfl, rfl⟩ := hsurf
  obtain ⟨arg, body, cap, hrp⟩ := v_resolve hres
  exact ⟨rfl, rfl, ⟨arg, body, cap, hrp⟩, v_log _ _, rfl, rfl, rfl, rfl,
    fun k hk => vPolicy_lookup _ _ _ _ _ hk⟩

/-- The typing of a declaration that the entry is about. -/
private theorem v_typed {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl vDecl postExpr ctx res) :
    ∃ (fuel : Nat) (poison : Bool),
      typecheck ctx postExpr (fuel + 1) = .ok res ∧
      typecheckExternVal ctx 250 .int poison geGuard fuel = .ok res := by
  cases htyped with
  | val htc =>
      rename_i fuel poison
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ f => exact ⟨f, poison, htc, by simpa [typecheck, typecheckExpr] using htc⟩

private theorem v_run {n : Int} {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (h : ExternDeclBoundaryRun vDecl (vI n) ctx res cᵢ cf o) : cf = cᵢ ∧ o = .num n := by
  cases h with
  | val f =>
      obtain ⟨v, hv, ho⟩ := f.impl_value
      simp only [vI, ExternImpl.val.injEq] at hv
      exact ⟨f.output_config, by rw [ho, ← hv]⟩
  | ref f => have h := f.kind_ref; simp [vDecl] at h
  | fn f => have h := f.kind_fn; simp [vDecl] at h
  | pfn f => have h := f.kind_pfn; simp [vDecl] at h

/-! ## Moving the context facts to the context after the declaration -/

private theorem consistent_envs {predSat : PredSat} {R : Regime} {ctx ctx' : TypeContext}
    {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : consistentWithRegime predSat R ctx μ ρ θ) : consistentWithRegime predSat R ctx' μ ρ θ := by
  unfold consistentWithRegime; rw [hm, hv]; exact h

private theorem agree_envs {predSat : PredSat} {R : Regime} {ctx ctx' : TypeContext}
    {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat R ctx' μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  unfold agreeOnClean; rw [hm, hv]; exact h

private theorem runtime_envs {ctx ctx' : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : runtimeInstantiatesCtx ctx μ ρ θ) : runtimeInstantiatesCtx ctx' μ ρ θ := by
  unfold runtimeInstantiatesCtx; rw [hm, hv]; exact h

namespace VFacts

variable {ctx : TypeContext} {res : TypeResult}

private theorem memEnv_after (hf : VFacts ctx res) : (ctxAfter ctx res).memEnv = ctx.memEnv := hf.memEnv

private theorem varEnv_after (_hf : VFacts ctx res) : (ctxAfter ctx res).varEnv = ctx.varEnv := rfl

private theorem below (hf : VFacts ctx res) :
    ∀ k, k < ctx.nextTag → res.regime'.lookup? k = ctx.regime.lookup? k :=
  fun k hk => hf.regime k (Nat.ne_of_lt hk)

private theorem guard_mem (hf : VFacts ctx res) :
    ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k := by
  intro k hk
  obtain ⟨arg, body, cap, hp⟩ := hf.guard
  have : k = ctx.nextTag := by simp [qtypGuardTag, hp] at hk; exact hk.symm
  subst this
  exact hf.logged

private theorem notfun (hf : VFacts ctx res) : res.qualType.etyp.isFunctionType = false := by
  rw [hf.etyp]; rfl

private theorem notref (hf : VFacts ctx res) : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
  rw [hf.etyp]; rintro ⟨_, h⟩; cases h

private theorem wfCtx (hf : VFacts ctx res) (hwf : wfTypeContext ctx) :
    wfTypeContext (ctxAfter ctx res) := by
  unfold wfTypeContext
  simp only [ctxAfter, hf.memEnv, hf.nextLoc]
  exact hwf

end VFacts

/-- Agreement moves to the regime after the declaration. -/
private theorem agree_regime {ctx : TypeContext} {R' : Regime} (htb : TagBoundedCtx ctx)
    (hmono : Regime.monotoneStepExt ctx.regime R' (fun k => ctx.nextTag ≤ k))
    {predSat : PredSat} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hagree : agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat R' ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  refine ⟨fun l qt hl hclean' => ?_, fun x qt hx hclean' => ?_⟩
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hmono (fun _ hk => hk)
        (TagBoundedCtx_memEnv_predTagBounded htb hl) hclean'
    cases hagree.1 l qt hl hclean0 with
    | agree_values _ _ a₀ a₁ n₀ n₁ h0 h1 h2 h3 hv =>
        refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ h0 h1 h2 h3 ?_
        have hb : etypClosuresFullBounded qt.etyp ctx.nextTag := by
          rw [memEnv_lookup_etyp_int ctx.memEnv l qt hl]; trivial
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hmono (fun _ hk => hk) hb
          hclean' hv
    | both_unrealized _ _ h0 h1 => exact agreeLocUnder.both_unrealized l qt h0 h1
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hmono (fun _ hk => hk)
        (TagBoundedCtx_varEnv_predTagBounded htb hx) hclean'
    cases hagree.2 x qt hx hclean0 with
    | agree_values _ _ v₀ v₁ h0 h1 hv =>
        refine agreeVarUnder.agree_values x qt v₀ v₁ h0 h1 ?_
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hmono (fun _ hk => hk)
          (TagBoundedCtx_varEnv_etypClosures htb hx) hclean' hv
    | both_none _ _ h0 h1 => exact agreeVarUnder.both_none x qt h0 h1

/-- From *match*: the declared value is consistent with the regime after the
    declaration. -/
private theorem valueConsistent_of_valMatches {predSat : PredSat} {res : TypeResult} {cf : Config}
    {o : Value} {θ : RealizationMap}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hmatch : ValMatches predSat res cf o)
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
          have hiff := hmatch a ha arg body cap b (by rw [hak]; exact hpred)
            (by rw [hak]; exact hR)
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

/-! ## The declaration contracts -/

/-- The single-run contract: the declared value is consistent with the regime
    after the declaration by *match* (`ValMatches`). -/
theorem v_declSingle (n : Int) : ExternDeclBoundarySingle vDecl (vI n) := by
  intro postExpr ctx res predSat tm htyped _hpredlaws hframe hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc hvm
  obtain ⟨fuel, poison, _htc, htcV⟩ := v_typed htyped
  have hf : VFacts ctx res := v_facts_of htcV
  obtain ⟨hcf, ho⟩ := v_run hrun
  subst hcf; subst ho
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 250 .int poison geGuard fuel res hwfTm hTmBounded
      htcV
  have hvt : valueHasETyp θ (Value.num n) res.qualType.etyp := by
    rw [hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm',
    BoundaryTagMeaningPost.of_isCanonical_predSat hco (TagFrame.laws_of_within hframe hw) hw,
    θ, ⟨fun _ _ h => h, fun h => h⟩, hvt,
    runtime_envs hf.memEnv_after hf.varEnv_after hric, ?_, ?_,
    PreservesInheritedFinalCleanLocsOneRun.refl hric, ?_, ?_⟩
  · exact consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcons)
  · exact valueConsistent_of_valMatches hf.guard_mem (hvm rfl) hvt hf.notfun
  · intro l qt hnc hlk _hclean
    rw [hf.memEnv] at hlk
    exact absurd (memEnv_contains_of_lookup_some _ l qt hlk) hnc
  · show ReservedDiscipline registry res.declared' θ
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrdIn

/-- The two-run contract. *Agreement* of the declared value is proved here: the
    two runs read the same implementation, so they declare the same value. -/
theorem v_declFR (n : Int) : ExternDeclBoundaryFR vDecl (vI n) := by
  intro postExpr ctx res predSat tm htyped _hpredlaws hframe hwfTm hTmBounded
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ hwf htb hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrd₀ hrd₁ hrun₀ hrun₁ hvm₀ hvm₁
  obtain ⟨fuel, poison, htc, htcV⟩ := v_typed htyped
  have hf : VFacts ctx res := v_facts_of htcV
  obtain ⟨hcf₀, ho₀⟩ := v_run hrun₀.run
  obtain ⟨hcf₁, ho₁⟩ := v_run hrun₁.run
  subst hcf₀; subst hcf₁; subst ho₀; subst ho₁
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 250 .int poison geGuard fuel res hwfTm hTmBounded
      htcV
  have hpost :=
    BoundaryTagMeaningPost.of_isCanonical_predSat hco (TagFrame.laws_of_within hframe hw) hw
  have hmono : Regime.monotoneStepExt ctx.regime res.regime' (fun k => ctx.nextTag ≤ k) := by
    simpa [ctxAfter] using regime_monotoneExt ctx postExpr (fuel + 1) res htc
  have hvt : ∀ θ : RealizationMap, valueHasETyp θ (Value.num n) res.qualType.etyp := by
    intro θ; rw [hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm', hpost, hpost.laws, hpost.respectsResult, θ₀, θ₁,
    ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩, hvt θ₀, hvt θ₁, hpost.wfCtx,
    hf.wfCtx hwf, typecheckExpr_preserves_TagBoundedCtx ctx postExpr (fuel + 1) res htc htb,
    hwfcfg₀, hwfcfg₁,
    runtime_envs hf.memEnv_after hf.varEnv_after hric₀,
    runtime_envs hf.memEnv_after hf.varEnv_after hric₁,
    typecheckExpr_preserves_regimeConsistentWithCtx ctx postExpr (fuel + 1) res hreg htc,
    consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcwr₀),
    consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcwr₁),
    agree_envs hf.memEnv_after hf.varEnv_after (agree_regime htb hmono hagree),
    valueConsistent_of_valMatches hf.guard_mem (hvm₀ rfl) (hvt θ₀) hf.notfun,
    valueConsistent_of_valMatches hf.guard_mem (hvm₁ rfl) (hvt θ₁) hf.notfun,
    ?_, ?_, ?_⟩
  · -- Agreement: the two runs declare the same value.
    intro hclean
    cases hclean with
    | clean hp => rw [hf.poison] at hp; cases hp
    | guard k htag hR _ => exact .withPred_true_eq k htag hR hf.notfun hf.notref rfl
  · show ReservedDiscipline registry res.declared' θ₀
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrd₀
  · show ReservedDiscipline registry res.declared' θ₁
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrd₁

/-! ## The call contracts, operational safety and the registry -/

private theorem v_callFR (m : Int) : ExternCallBoundaryFR vDecl (vI m) := by
  intro _ _ _ _ _ _ _ _ _ _ htyped₀
  cases htyped₀ with
  | fnExternMember _ hkind => simp [vDecl] at hkind
  | pfnExternMember _ hkind => simp [vDecl] at hkind

private theorem v_callSingle (m : Int) : ExternCallBoundarySingle vDecl (vI m) := by
  intro _ _ _ _ _ _ htyped
  cases htyped with
  | fnExternMember _ hkind => simp [vDecl] at hkind
  | pfnExternMember _ hkind => simp [vDecl] at hkind

private theorem v_operationalSafe (m : Int) : ExternOperationalSafe vDecl (vI m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn h; simp [vI] at h
  · intro implPfn h; simp [vI] at h
  · intro v h _ _ _ _ _
    simp only [vI, ExternImpl.val.injEq] at h
    subst h
    exact wfValue.num m
  · intro implFn h; simp [vI] at h

/-- The trusted entry of `@250` with the implementation `m`. -/
theorem vSpec (m : Int) : ExternBoundarySpec vDecl (vI m) where
  declFR := v_declFR m
  callFR := v_callFR m
  declSingle := v_declSingle m
  callSingle := v_callSingle m
  operational := v_operationalSafe m

/-- The trusted registry that holds the extern value alone. -/
def vReg (m : Int) : TrustedRegistry := [⟨vDecl, vI m, vSpec m⟩]

/-- The registry of the runs. -/
def regV (m : Int) : ExternRegistry := emptyExternRegistry.insert 250 (.val (.num m))

theorem vReg_runtime (m : Int) : (vReg m).toRuntimeRegistry = regV m := rfl

private theorem regV_noLoc {m : Int} {id : ExternId} {a : Address}
    (h : (regV m).get? id = some (.val (.loc a))) : False := by
  by_cases hid : id = 250
  · subst hid; simp [regV] at h
  · simp [regV, emptyExternRegistry, Ne.symm hid] at h

/-! ## The program -/

/-- `extern val @250 : (int :> poisoned { 0, w => w >= 0 })` -/
def valD : Expr := .externVal 250 .int true geGuard

/-- `if v >= 0 then v else 0` -/
def test : Expr := .ite (.op (.var "v") .gte (.num 0)) (.var "v") (.num 0)

/-- `let v = extern val @250 : (int :> poisoned { 0, w => w >= 0 }) in if v >= 0 then v else 0` -/
def prog : Expr := .vlet "v" valD test

/-- The assignment of the extern's tags: every tag of `@250` gets `b`. -/
def polV (b : Bool) : ExternId → Tag → Option Bool :=
  fun id _ => if id = 250 then some b else none

/-- The starting context: a poisoned integer `x`, and the assignment `polV b`. -/
def K (b : Bool) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := (∅ : VarTypeEnv).update "x" pInt,
    tagEnv := ∅, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := polV b }

/-- The starting state of a run from `x = n`, with the registry holding `m`. -/
def cfgX (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regV m }

/-- The typing of the declaration and of the program. -/
private def r1 (b : Bool) : TypeResult := okVal (typecheckExpr (K b) valD 58)
def rootRes (b : Bool) : TypeResult := okVal (typecheckExpr (K b) prog 60)

private def facts (b : Bool) : Bool :=
  isOkB (typecheckExpr (K b) prog 60) &&
  isOkB (typecheckExpr (K b) valD 58) &&
  ((r1 b).regime'.lookup? 0 == some b) &&
  descGe (programTable ∅ (rootRes b).tagLog') 0 &&
  allGe (rootRes b).tagLog' &&
  ((rootRes b).qualType.etyp == ETyp.int) &&
  ((rootRes b).qualType.poison == false)

private theorem facts_ok (b : Bool) : facts b = true := by
  cases b <;> decide +kernel

private theorem facts_of (b : Bool) :
    typecheckExpr (K b) prog 60 = .ok (rootRes b) ∧
    typecheckExpr (K b) valD 58 = .ok (r1 b) ∧
    (r1 b).regime'.lookup? 0 = some b ∧
    descGe (programTable ∅ (rootRes b).tagLog') 0 = true ∧
    allGe (rootRes b).tagLog' = true ∧
    (rootRes b).qualType.etyp = .int ∧ (rootRes b).qualType.poison = false := by
  have hf := facts_ok b
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨eq_okVal h1, eq_okVal h2, h3, h4, h5, h6, h7⟩

private theorem r1_facts (b : Bool) : VFacts (K b) (r1 b) := by
  have h := (facts_of b).2.1
  exact v_facts_of (fuel := 57) (poison := true) (by simpa [typecheckExpr, valD] using h)

/-! ## The runs -/

/-- The declaration returns the value of the registry and leaves the state. -/
private theorem run_valD (m n : Int) : terminatesTo valD (cfgX m n) (cfgX m n) (.num m) :=
  ⟨1, false, by simp [beval, valD, cfgX, regV, valueMatchesTyp]⟩

/-- A run with the value `m ≥ 0` returns `m`. -/
theorem run_prog_nonneg (m n : Int) (hm : 0 ≤ m) :
    terminatesTo prog (cfgX m n) (cfgX m n) (.num m) := by
  refine ⟨6, false, ?_⟩
  simp [prog, valD, test, beval, cfgX, regV, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, hm]

/-- A run with the value `m < 0` returns `0`. -/
theorem run_prog_neg (m n : Int) (hm : m < 0) :
    terminatesTo prog (cfgX m n) (cfgX m n) (.num 0) := by
  refine ⟨6, false, ?_⟩
  simp [prog, valD, test, beval, cfgX, regV, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, Int.not_le.mpr hm]

/-! ## Inversion -/

/-- The root step and the declaration step. -/
def U0 (b : Bool) (m n : Int) : Step := ⟨K b, prog, 60, cfgX m n⟩
private def U1 (b : Bool) (m n : Int) : Step := ⟨K b, valD, 58, cfgX m n⟩

private inductive InSet (b : Bool) (m n : Int) : Step → Prop
  | u0 : InSet b m n (U0 b m n)
  | u1 : InSet b m n (U1 b m n)
  | leaf {s : Step} : noApp s.e = true → InSet b m n s

private theorem inSet_step {b : Bool} {m n : Int} {s s' : Step} (hs : InSet b m n s)
    (h : SubStep s s') : InSet b m n s' := by
  cases hs with
  | u0 =>
      have hh := SubStep.vlet_inv (ctx := K b) (x := "v") (e1 := valD) (e2 := test) (F := 60)
        (cfg := cfgX m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩
      · exact InSet.u1
      · exact InSet.leaf rfl
  | u1 => cases h
  | leaf hl => exact InSet.leaf (SubStep.noApp h hl)

private theorem inSet_reach {b : Bool} {m n : Int} {s : Step} (h : Reach (U0 b m n) s) :
    InSet b m n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

/-- The run makes no extern call. -/
private theorem inSet_call {b : Bool} {m n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet b m n s) : ¬ ExternCallAt s effects entry res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternCallAt.not_of_reach_noApp hl (Reach.refl _) h
  | _ => cases h

/-- The run declares the extern value once, at `U1`. -/
private theorem inSet_val {b : Bool} {m n : Int} {s : Step} {res : TypeResult} {cf : Config}
    {o : Value} (hs : InSet b m n s) (h : ExternValAt s res cf o) :
    res = r1 b ∧ cf = cfgX m n ∧ o = .num m := by
  cases hs with
  | leaf hl => exact absurd h (ExternValAt.not_of_reach_noApp hl (Reach.refl _))
  | u0 => cases h
  | u1 =>
      cases h with
      | mk htc hrun =>
          obtain ⟨_, h2, _⟩ := facts_of b
          obtain rfl := ok_inj htc h2
          obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_valD m n)
          exact ⟨rfl, rfl, rfl⟩

private theorem reach_val (b : Bool) (m n : Int) : Reach (U0 b m n) (U1 b m n) :=
  Relation.ReflTransGen.single SubStep.vletBound

private theorem val_mk (b : Bool) (m n : Int) : ExternValAt (U1 b m n) (r1 b) (cfgX m n) (.num m) :=
  ExternValAt.mk (facts_of b).2.1 (run_valD m n)

/-! ## The premises -/

/-- *Match* holds exactly when the value satisfies the guard as the assignment
    says: `m ≥ 0` when the tag is true, `m < 0` when it is false. -/
theorem match_iff (b : Bool) (m n : Int) (predSat : PredSat)
    (hlaws : PredSatLaws predSat (programTable ∅ (rootRes b).tagLog')) :
    ExternCallsMatch predSat (U0 b m n) ↔ (0 ≤ m ↔ b = true) := by
  obtain ⟨_, _, hreg, hdesc, _⟩ := facts_of b
  have hf := r1_facts b
  have hpin := pin hlaws hdesc
  constructor
  · intro h
    have hv := h.vals _ _ _ _ (reach_val b m n) (val_mk b m n)
    obtain ⟨arg, body, cap, hp⟩ := hf.guard
    obtain ⟨a, ha, hat⟩ := hf.logged
    have hiff := hv a ha arg body cap b (by rw [hat]; exact hp) (by rw [hat]; exact hreg)
    rw [hat, show (K b).nextTag = 0 from rfl, hpin] at hiff
    exact hiff
  · intro hm
    refine ⟨fun _ _ _ _ _ _ hreach hcall => absurd hcall (inSet_call (inSet_reach hreach)),
      fun s res cf o hreach hval => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := inSet_val (inSet_reach hreach) hval
    intro a ha arg body cap b' hp hR
    obtain ⟨arg', body', cap', hp'⟩ := hf.guard
    have hat : a.tag = 0 := by
      rw [hp'] at hp
      simp only [Predicate.guardClosure.injEq] at hp
      exact hp.1.symm
    rw [hat] at hR ⊢
    rw [hreg, Option.some.injEq] at hR
    subst hR
    rw [hpin]
    exact hm

/-- *Agreement* holds for every pair of runs: they make no extern call. -/
theorem agree (b : Bool) (m n₀ n₁ : Int) : ExternCallsAgree (U0 b m n₀) (U0 b m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ _ _ _ _ hc₀ _ _ =>
    absurd hc₀ (inSet_call (inSet_reach hr₀))⟩

/-! ## The other premises of the theorem -/

/-- No critical input; the scenario commits the tags of `@250`. -/
def sV : InputSpec := { locs := ∅, vars := ∅, regimeExterns := [250] }

/-- The observation: the returned integer. -/
def obsRet : ObservableSpec := { locs := ∅, retEtyp? := some .int }

private theorem K_vars (b : Bool) : ∀ x qt, (K b).varEnv.lookup x = some qt → qt = pInt := by
  intro x qt h
  by_cases hx : x = "x"
  · subst hx
    simp only [K, VarTypeEnv_lookup_update_eq, Option.some.injEq] at h
    exact h.symm
  · simp only [K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h

private theorem pInt_not_clean (R : Regime) : ¬ qtypCleanUnder R pInt := by
  intro h
  cases h with
  | clean hpoison => simp [pInt] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, pInt] at htag

private theorem externRegimeMatchesK (b : Bool) : ExternRegimeMatchesInputSpec sV (K b) := by
  refine ⟨fun {id} hid k => ?_, fun {id} hid k => ?_⟩
  · have h : id ≠ 250 := by simpa [sV] using hid
    simp [K, polV, h]
  · simp only [sV, List.mem_singleton] at hid
    subst hid
    exact ⟨b, by simp [K, polV]⟩

private theorem trustedK (b : Bool) (m : Int) : InitialContextTrusted (vReg m) prog (K b) := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 250 ∧ d = vDecl := by
        simp only [prog, valD, test] at hp
        cases hp with
        | vlet_bound h => cases h; exact ⟨rfl, rfl⟩
        | vlet_body h =>
            cases h with
            | ite_cond h =>
                cases h with
                | op_left h => cases h
                | op_right h => cases h
            | ite_then h => cases h
            | ite_else h => cases h
      obtain ⟨rfl, rfl⟩ := h
      simp [vReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K_vars b _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

private theorem wfSpecV : wfInputSpec sV := by
  unfold wfInputSpec
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · refine And.intro ?_ ?_
      · exact Std.ExtTreeMap.nodup_keys
      · intro x qt h
        simp [sV, VarTypeEnv.lookup] at h
    · intro x qt h
      simp [sV, VarTypeEnv.lookup] at h
  · intro x qt h
    simp [sV, VarTypeEnv.lookup] at h

private theorem ctxMatchesK (b : Bool) : ctxMatchesInputSpec sV (K b) := by
  unfold ctxMatchesInputSpec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · intro x qt h
    simp [sV, VarTypeEnv.lookup] at h
  · intro l qt k h
    simp [K, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · intro x qt k h htag _
      rw [K_vars b x qt h] at htag
      simp [qtypGuardTag, pInt] at htag
    · intro x qt h
      rw [K_vars b x qt h]
      exact deepQTypProperty.other _ _ trivial

private theorem wfCtxK (b : Bool) : wfTypeContext (K b) := by
  unfold wfTypeContext
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l h
    simp [K] at h
  · intro x qt h
    rw [K_vars b x qt h]
    exact trivial
  · intro x qt h
    rw [K_vars b x qt h]
    exact trivial

private theorem tagBoundedK (b : Bool) : TagBoundedCtx (K b) := by
  unfold TagBoundedCtx
  refine And.intro ?_ (And.intro (And.intro ?_ ?_) ?_)
  · intro k hk
    simp [K] at hk
  · intro x qt h
    rw [K_vars b x qt h]
    exact trivial
  · intro l qt h
    simp [K, MemoryTypeEnv.lookup] at h
  · intro x qt h
    rw [K_vars b x qt h]
    exact trivial

private theorem wfTmK (b : Bool) : wfTagMeaningCtx ∅ (K b) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
      have hroot := K_vars b x qtRoot hlookup
      subst hroot
      have hqt : qt = pInt :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [pInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, pInt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
      simp [K, MemoryTypeEnv.lookup] at hlookup

private theorem tmBoundedK (b : Bool) : TagMeaningBounded ∅ (K b).nextTag := by
  intro k d h
  simp [TagMeaning.lookup] at h

private theorem lawsEmpty : PredSatLaws geSat ∅ :=
  predSatLaws_geSat (fun k d h => by simp [TagMeaning.lookup] at h)

private theorem wfRegimeK (b : Bool) : wfRegime (K b).regime sV := by
  have htags : inputSpecTags sV = [] := rfl
  refine And.intro ?_ ?_
  · intro k hk
    rw [htags] at hk
    cases hk
  · intro k hk
    simp [K, Regime.lookup?] at hk

private theorem wfθ₀ : wfRealizationMap ∅ := by
  intro l₁ l₂ a h
  simp [RealizationMap.lookup] at h

private theorem wfCX (m n : Int) : wfConfig (cfgX m n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgX] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

private theorem reservedWFV (m : Int) : RegistryReservedWF (regV m) ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regV_noLoc h).elim

private theorem disciplineK (b : Bool) (m : Int) :
    ReservedDiscipline (regV m) (K b).declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regV_noLoc h).elim
  · intro id a h _ l
    exact (regV_noLoc h).elim

private theorem lookupX (n : Int) :
    (VarEnv.update [] "x" (.num n)).lookup "x" = some (.num n) := by
  simp [VarEnv.update, VarEnv.lookup]

private theorem instantiatesK (b : Bool) (n : Int) :
    runtimeInstantiatesCtx (K b) ∅ (VarEnv.update [] "x" (.num n)) ∅ := by
  refine And.intro ?_ ?_
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    have hq := K_vars b x qt h
    subst hq
    have hx : x = "x" := by
      by_contra hx
      simp only [K] at h
      rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
      simp [VarTypeEnv.lookup] at h
    subst hx
    exact ⟨_, lookupX n, valueHasETyp.num n⟩

private theorem trustedInitK (b : Bool) (n : Int) :
    trustedVarsClosureRegimeInit geSat (K b).regime sV (K b) ∅
      (VarEnv.update [] "x" (.num n)) ∅ := by
  refine trustedVarsClosureRegimeInit.intro ?_
  intro x qt v h _ hv
  have hq := K_vars b x qt h
  subst hq
  have hx : x = "x" := by
    by_contra hx
    simp only [K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h
  subst hx
  rw [lookupX n] at hv
  obtain rfl := Option.some.inj hv
  exact closureCapturedVarsRegime.intro
    (deepValueQTypProperty.nonClosure (fun _ _ _ hc => by cases hc)
      (fun _ _ _ hc => by cases hc))

private theorem consistentK (b : Bool) {ρ : VarEnv} :
    consistentRegimeSpec geSat (K b).regime sV ∅ ρ ∅ := by
  unfold consistentRegimeSpec
  have hnil : memEnvToLocQTypList sV.locs = [] := rfl
  have hnil' : sV.vars.toList = [] := rfl
  rw [hnil, hnil']
  exact ⟨trivial, trivial⟩

private theorem agreeCriticalK (b : Bool) {ρ₁ ρ₂ : VarEnv} :
    agreeOnCriticalInputsUnderRegimeSpec geSat (K b).regime sV ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · intro x qt h _
    simp [sV, VarTypeEnv.lookup] at h

private theorem agreeTrustedK (b : Bool) {ρ₁ ρ₂ : VarEnv} :
    agreeOnTrustedInputs geSat (K b).regime sV (K b) ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [K, MemoryTypeEnv.lookup] at h
  · intro x qt h _ hclean
    rw [K_vars b x qt h] at hclean
    exact absurd hclean (pInt_not_clean _)

/-! ## The theorem -/

/-- The typing and the premises: under both assignments the program is typed
    as a clean `int`, and *match* holds exactly when the value satisfies the
    guard as the assignment says. -/
theorem val_case :
    (∀ b, typecheck (K b) prog 60 = .ok (rootRes b) ∧
      (rootRes b).qualType.etyp = .int ∧ (rootRes b).qualType.poison = false ∧
      PredSatLaws geSat (programTable ∅ (rootRes b).tagLog')) ∧
    ExternCallsMatch geSat (U0 true 5 4) ∧ ExternCallsMatch geSat (U0 false (-3) 4) ∧
    ¬ ExternCallsMatch geSat (U0 false 5 4) ∧ ¬ ExternCallsMatch geSat (U0 true (-3) 4) := by
  have hl : ∀ b, PredSatLaws geSat (programTable ∅ (rootRes b).tagLog') :=
    fun b => predSatLaws_geSat (geTable_of_allGe (facts_of b).2.2.2.2.1)
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, _, _, _, _, h6, h7⟩ := facts_of b
    exact ⟨h1, h6, h7, hl b⟩
  · exact (match_iff true 5 4 geSat (hl true)).2 (by decide)
  · exact (match_iff false (-3) 4 geSat (hl false)).2 (by decide)
  · rw [match_iff false 5 4 geSat (hl false)]; decide
  · rw [match_iff true (-3) 4 geSat (hl true)]; decide

/-- **The theorem at
    `let v = extern val @250 : (int :> poisoned { 0, w => w >= 0 }) in if v >= 0 then v else 0`**
    under the assignment `b`, with the registry holding `m`: when the value
    satisfies the guard as the assignment says, two runs from any `x` return
    the same value. -/
theorem same_return (b : Bool) (m : Int) (hm : 0 ≤ m ↔ b = true) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgX m n₀) cf₀ o₀) (hr₁ : terminatesTo prog (cfgX m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  obtain ⟨htc, _, _, _, hall, hety, hpz⟩ := facts_of b
  have hlaws := predSatLaws_geSat (geTable_of_allGe hall)
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (vReg m) prog sV obsRet (K b) (externRegimeMatchesK b)
      (trustedK b m) wfSpecV rfl (ctxMatchesK b) (wfCtxK b) rfl rfl rfl (tagBoundedK b)
      geSat ∅ (wfTmK b) (tmBoundedK b) lawsEmpty 60 (rootRes b) htc
      (And.intro (fun et h => by
          simp only [obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hety, hpz⟩)
        (fun _ _ h => by simp [obsRet, MemoryETypEnv.lookup] at h))
      hlaws ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (wfRegimeK b) wfθ₀ wfθ₀
      (wfCX m n₀) (wfCX m n₁) (reservedWFV m) (reservedWFV m) (disciplineK b m) (disciplineK b m)
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (instantiatesK b n₀) (instantiatesK b n₁) (trustedInitK b n₀) (trustedInitK b n₁)
      (consistentK b) (consistentK b) ((match_iff b m n₀ geSat hlaws).2 hm)
      ((match_iff b m n₁ geSat hlaws).2 hm) (agreeCriticalK b) (agreeTrustedK b)
      (agree b m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **Tag true, value 5**: the runs from `x = 4` and `x = 5` both return 5. -/
theorem true_5 :
    terminatesTo prog (cfgX 5 4) (cfgX 5 4) (.num 5) ∧
    terminatesTo prog (cfgX 5 5) (cfgX 5 5) (.num 5) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo prog (cfgX 5 4) cf₀ o₀ → terminatesTo prog (cfgX 5 5) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_prog_nonneg 5 4 (by decide), run_prog_nonneg 5 5 (by decide),
    fun hr₀ hr₁ => same_return true 5 (by decide) 4 5 hr₀ hr₁⟩

/-- **Tag false, value -3**: the runs from `x = 4` and `x = 5` both return 0. -/
theorem false_neg3 :
    terminatesTo prog (cfgX (-3) 4) (cfgX (-3) 4) (.num 0) ∧
    terminatesTo prog (cfgX (-3) 5) (cfgX (-3) 5) (.num 0) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo prog (cfgX (-3) 4) cf₀ o₀ → terminatesTo prog (cfgX (-3) 5) cf₁ o₁ →
        o₀ = o₁ :=
  ⟨run_prog_neg (-3) 4 (by decide), run_prog_neg (-3) 5 (by decide),
    fun hr₀ hr₁ => same_return false (-3) (by decide) 4 5 hr₀ hr₁⟩

end Val

end ExternCallsWitness
