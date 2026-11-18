/-
  ExternCallsWitnessValCell.lean - A guarded `extern val` whose guard reads a cell,
  and the theorem applied to a program that declares it and tests the guard.

  The program
      let a = ref 5 in
      let v = extern val @251 : (int :> poisoned { 0, w => w > !a }) in
      if v > !a then v else 0
  declares an extern value whose guard `w => w > !a` reads the cell of `a`. The
  test `v > !a` matches the guard, so under either value of the tag the program is
  typed as a clean `int` (`typing_case`).

  * The trusted entry `vSpec` of `@251` (implementation `vI m`): the declaration
    contracts `v_declSingle` and `v_declFR`, the call contracts (no call is typed
    against a declaration of kind `val`), operational safety, and the registry
    `vReg`.
  * The relation `cellSat`: the checked value is a number greater than the content
    of the address the realisation map gives to location `0`. It meets both laws of
    `PredSatLaws` for every table whose guards are `w => w > !a` at tag `0` with
    `a : ref {0}` captured (`cellSat_lawful`), in particular for the empty table
    (`cellLaws_empty`) and for the program table of the typing run.
  * *Match* of the declared value holds exactly when `5 < m ↔ b = true`
    (`match_iff`); the runs make no extern call (`agree`).
  * `same_return`: under an assignment where the value matches, two runs from any
    poisoned `x`, which the program does not read, return the same value. Every
    premise of `TypeSystemEnforcesFaultRobustness` is proved, including
    `GuardCapsBelow` of the starting context. The instances `true_7` and `false_3`
    exhibit runs that meet every premise.

  Imports `ExternCallsWitnessBase` and `FaultRobustnessProofs`; not on the FR
  proof path.
-/
import LeanProofs.ExternCallsWitnessBase
import LeanProofs.FaultRobustnessProofs

open Std LeanPoison

namespace ExternCallsWitness

namespace ValCell

/-! ## The program -/

/-- `extern val @251 : (int :> poisoned { 0, w => w > !a })` -/
def cellGuard : SyntaxPredicate :=
  .guardClosure ⟨0⟩ "w" (Expr.op (Expr.var "w") Op.gt (Expr.deref (Expr.var "a")))

def valD : Expr := .externVal 251 .int true cellGuard

/-- `if v > !a then v else 0` -/
def test : Expr := .ite (.op (.var "v") .gt (.deref (.var "a"))) (.var "v") (.num 0)

/-- `let a = ref 5 in let v = extern val @251 : ... in if v > !a then v else 0` -/
def progA : Expr := .vlet "a" (.newRef (.num 5)) (.vlet "v" valD test)

/-- The assignment of the extern's tags: every tag of `@251` gets `b`. -/
def polV (b : Bool) : ExternId → Tag → Option Bool :=
  fun id _ => if id = 251 then some b else none

/-- The starting context: a poisoned integer `x`, and the assignment `polV b`. -/
def K (b : Bool) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := (∅ : VarTypeEnv).update "x" pInt,
    tagEnv := ∅, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := polV b }

/-- The registry of the runs. -/
def regA (m : Int) : ExternRegistry := emptyExternRegistry.insert 251 (.val (.num m))

/-- The starting state of a run from `x = n`, with the registry holding `m`. -/
def cfgX (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regA m }

/-- The location `0`, as the type of `a`. -/
def cS0 : LocSet := LocSet.singleton 0
def cRef : QTyp := { etyp := ETyp.ref cS0, poison := false, pred := Predicate.noPred }

/-- The body `w > !a` of the guard. -/
def cbody : PExpr := PExpr.op (PExpr.var "w") Op.gt (PExpr.deref (PExpr.var "a"))

/-- The typing of `ref 5`, the context after the binding of `a`, the typing of the
    declaration and of the program. -/
def rN (b : Bool) : TypeResult := okVal (typecheckExpr (K b) (.newRef (.num 5)) 58)
def ctxA (b : Bool) : TypeContext :=
  { ctxAfter (K b) (rN b) with varEnv := (K b).varEnv.update "a" (rN b).qualType }
def rD (b : Bool) : TypeResult := okVal (typecheckExpr (ctxA b) valD 56)
def rootRes (b : Bool) : TypeResult := okVal (typecheckExpr (K b) progA 60)

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

private theorem varsRegime_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {θ : RealizationMap} {ρ : VarEnv} {e : Name × QTyp}
    (hk : ∀ k a b c, e.2.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : varsRegime predSat R μ θ ρ e) : varsRegime predSat R' μ θ ρ e := by
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
    {θ : RealizationMap} {σcap : CapturedVarEnv} {ρcap : VarEnv}
    (hgood : ∀ x qt_x, σcap.lookup x = some qt_x →
      ∀ k a b c, qt_x.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : capturedVarsRegimeProperty predSat R μ θ σcap ρcap) :
    capturedVarsRegimeProperty predSat R' μ θ σcap ρcap := by
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
        capturedVarsRegimeProperty predSat R μ θ σcap ρcap ∧
          capturedVarsTypingProperty θ σcap ρcap) qt v) :
    GoodIn R R' qt →
    deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R' μ θ σcap ρcap ∧
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

/-- `extern val @251 : (int :> poisoned { 0, w => w > !a })`. -/
def vDecl : ExternDeclaration :=
  { id := 251, kind := .val, typ := .int, argName := none, retSpec := none,
    effects := [], preds := [cellGuard], argPoison := false }

/-- The implementation: the value `n`. -/
def vI (n : Int) : ExternImpl := .val (.num n)

/-- The tag mapping of the declaration at cursor `c`: index 0 gets `c`. -/
private def vMap (c : Tag) : TagMapping := (∅ : TagMapping).insert ⟨0⟩ c

private theorem v_alloc (c : Tag) : collectAndAllocExternTags [cellGuard] c = .ok (vMap c, c + 1) := by
  rfl

private theorem v_log (env : VarTypeEnv) (c : Tag) :
    ∃ a ∈ externTagLog [cellGuard] env (vMap c), a.tag = c := by
  have h : externTagLog [cellGuard] env (vMap c) =
      [⟨c, "w", cbody, VarTypeEnv.toCaptured env⟩] := by
    rfl
  refine ⟨⟨c, "w", cbody, VarTypeEnv.toCaptured env⟩, ?_, rfl⟩
  rw [h]
  simp

private theorem v_resolve {env : VarTypeEnv} {c : Tag} {rp : Predicate}
    (h : resolveSyntaxPred cellGuard env (vMap c) = .ok rp) :
    ∃ arg body cap, rp = .guardClosure c arg body cap := by
  have hget : (vMap c).get? ⟨0⟩ = some c := rfl
  simp only [cellGuard, resolveSyntaxPred, hget, bind, Except.bind, pure, Except.pure] at h
  cases hp : ((Expr.var "w").op Op.gt (Expr.deref (Expr.var "a"))).toPExpr with
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
structure VFacts (ctx : TypeContext) (res : TypeResult) : Prop where
  etyp : res.qualType.etyp = .int
  poison : res.qualType.poison = true
  guard : ∃ arg body cap, res.qualType.pred = .guardClosure ctx.nextTag arg body cap
  logged : ∃ a ∈ res.tagLog', a.tag = ctx.nextTag
  nextTag : res.nextTag' = ctx.nextTag + 1
  memEnv : res.memEnv' = ctx.memEnv
  nextLoc : res.nextLoc' = ctx.nextLoc
  declared : res.declared' = 251 :: ctx.declaredExternRefs
  regime : ∀ k, k ≠ ctx.nextTag → res.regime'.lookup? k = ctx.regime.lookup? k

theorem v_facts_of {ctx : TypeContext} {poison : Bool} {fuel : Nat} {res : TypeResult}
    (htc : typecheckExternVal ctx 251 .int poison cellGuard fuel = .ok res) : VFacts ctx res := by
  obtain ⟨hpz, tagMapping, nextTag', rp, ⟨qt, ctx'⟩, halloc, hres, hsurf, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  rw [v_alloc] at halloc
  simp only [Except.ok.injEq, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  have hp : poison = true := by
    cases poison with
    | true => rfl
    | false => have h := hpz rfl; simp [cellGuard] at h
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
      typecheckExternVal ctx 251 .int poison cellGuard fuel = .ok res := by
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
    declaration, under a map that realises the context of the step at its start. -/
private theorem valueConsistent_of_valMatches {predSat : PredSat} {s : Step} {res : TypeResult}
    {cf : Config} {o : Value} {θ : RealizationMap}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hmatch : ValMatches predSat s res cf o)
    (hθ : runtimeInstantiatesCtx s.ctx s.cfg.memory s.cfg.varEnv θ)
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
            (by rw [hak]; exact hR) θ hθ
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
  intro postExpr ctx res predSat tm htyped _hpredlaws hframe hwfTm hTmBounded _hfp
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc hvm
  obtain ⟨fuel, poison, _htc, htcV⟩ := v_typed htyped
  have hf : VFacts ctx res := v_facts_of htcV
  obtain ⟨hcf, ho⟩ := v_run hrun
  subst hcf; subst ho
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 251 .int poison cellGuard fuel res hwfTm hTmBounded
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
  · exact valueConsistent_of_valMatches hf.guard_mem (hvm rfl) hric hvt hf.notfun
  · intro l qt hnc hlk _hclean
    rw [hf.memEnv] at hlk
    exact absurd (memEnv_contains_of_lookup_some _ l qt hlk) hnc
  · refine ⟨?_, MapKeepsBelow.refl _ _, KeepsFootprints.refl _ _ _ _⟩
    show ReservedDiscipline registry res.declared' θ
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrdIn

/-- The two-run contract. *Agreement* of the declared value is proved here: the
    two runs read the same implementation, so they declare the same value. -/
theorem v_declFR (n : Int) : ExternDeclBoundaryFR vDecl (vI n) := by
  intro postExpr ctx res predSat tm htyped _hpredlaws hframe hwfTm hTmBounded _hfp
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ hwf htb hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrd₀ hrd₁ hrun₀ hrun₁ hvm₀ hvm₁
  obtain ⟨fuel, poison, htc, htcV⟩ := v_typed htyped
  have hf : VFacts ctx res := v_facts_of htcV
  obtain ⟨hcf₀, ho₀⟩ := v_run hrun₀.run
  obtain ⟨hcf₁, ho₁⟩ := v_run hrun₁.run
  subst hcf₀; subst hcf₁; subst ho₀; subst ho₁
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 251 .int poison cellGuard fuel res hwfTm hTmBounded
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
    valueConsistent_of_valMatches hf.guard_mem (hvm₀ rfl) hric₀ (hvt θ₀) hf.notfun,
    valueConsistent_of_valMatches hf.guard_mem (hvm₁ rfl) hric₁ (hvt θ₁) hf.notfun,
    ?_, ?_, ?_,
    MapKeepsBelow.refl _ _, MapKeepsBelow.refl _ _,
    KeepsFootprints.refl _ _ _ _, KeepsFootprints.refl _ _ _ _⟩
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

/-- The trusted entry of `@251` with the implementation `m`. -/
theorem vSpec (m : Int) : ExternBoundarySpec vDecl (vI m) where
  declFR := v_declFR m
  callFR := v_callFR m
  declSingle := v_declSingle m
  callSingle := v_callSingle m
  operational := v_operationalSafe m

/-- The trusted registry that holds the extern value alone. -/
def vReg (m : Int) : TrustedRegistry := [⟨vDecl, vI m, vSpec m⟩]

private theorem vReg_runtime (m : Int) : (vReg m).toRuntimeRegistry = regA m := rfl

private theorem regA_noLoc {m : Int} {id : ExternId} {a : Address}
    (h : (regA m).get? id = some (.val (.loc a))) : False := by
  by_cases hid : id = 251
  · subst hid; simp [regA] at h
  · simp [regA, emptyExternRegistry, Ne.symm hid] at h

/-! ## The relation and its laws

`cellSat` says: the checked value is a number greater than the content of the
cell at which the map puts location `0`. -/

def cellSat : PredSat := fun _ θ μ v =>
  ∃ (a : Address) (n m' : Int), θ.lookup 0 = some a ∧ μ.lookup a = some n ∧
    v = Value.num m' ∧ n < m'

/-- Every guard of the table is `w => w > !a`, with `a : ref {0}` captured, at tag 0. -/
def CellTable (P : TagMeaning) : Prop :=
  ∀ k d, P.lookup k = some d →
    k = 0 ∧ d.argName = "w" ∧ d.body = cbody ∧
      (VarTypeEnv.ofCaptured d.capEnv).lookup "a" = some cRef

private theorem eqW_deref_w {e1 e2 : CapturedVarEnv} :
    ∀ (pe : PExpr) (f : Nat),
      PExpr.equalWithEnvs (PExpr.var "w") e1 pe e2
        (some ("w", PExpr.deref (PExpr.var "w"))) f = true → False := by
  intro pe
  induction pe with
  | deref pe' ih =>
    intro f h
    rcases f with _ | _ | f
    · simp [PExpr.equalWithEnvs] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
      exact ih f h
  | _ =>
    intro f h
    rcases f with _ | _ | f <;> simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h

private theorem eqW_var {e1 e2 : CapturedVarEnv} {x : Name} {pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "w") e1 pe e2 (some ("w", PExpr.var x)) f = true) :
    pe = PExpr.var x := by
  rcases f with _ | _ | f
  · simp [PExpr.equalWithEnvs] at h
  · by_cases hx : x = "w"
    · subst hx
      cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
  · by_cases hx : x = "w"
    · subst hx
      cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]

private theorem eqW_deref {e1 e2 : CapturedVarEnv} {x : Name} {pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "w") e1 pe e2
      (some ("w", PExpr.deref (PExpr.var x))) f = true) :
    pe = PExpr.deref (PExpr.var x) := by
  by_cases hx : x = "w"
  · subst hx
    exact (eqW_deref_w pe f h).elim
  · rcases f with _ | _ | _ | f
    · simp [PExpr.equalWithEnvs] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
      rename_i pe'
      cases pe' <;> simp_all

private theorem eqW_body {e1 e2 : CapturedVarEnv} {arg pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs cbody e1 pe e2 (some ("w", arg)) f = true) :
    ∃ pe1 f', pe = PExpr.op pe1 Op.gt (PExpr.deref (PExpr.var "a")) ∧
      PExpr.equalWithEnvs (PExpr.var "w") e1 pe1 e2 (some ("w", arg)) f' = true := by
  rcases f with _ | f
  · simp [PExpr.equalWithEnvs] at h
  · cases pe with
    | op p1 o p2 =>
      simp only [cbody, PExpr.equalWithEnvs, Bool.and_eq_true] at h
      obtain ⟨⟨ho, h1⟩, h2⟩ := h
      refine ⟨p1, f, ?_, h1⟩
      have ho' : o = Op.gt := by
        cases o <;> revert ho <;> decide
      subst ho'
      rcases f with _ | _ | f
      · simp [PExpr.equalWithEnvs] at h2
      · cases p2 <;> simp [PExpr.equalWithEnvs] at h2
      · cases p2 with
        | deref q =>
          cases q <;> simp_all [PExpr.equalWithEnvs, BEq.beq]
        | _ => simp [PExpr.equalWithEnvs] at h2
    | _ => simp [cbody, PExpr.equalWithEnvs] at h

private theorem toPExpr?_var' {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.var x)) : e = Expr.var x := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_deref' {e : Expr} {pe : PExpr}
    (h : e.toPExpr? = some (PExpr.deref pe)) : ∃ e', e = Expr.deref e' ∧ e'.toPExpr? = some pe := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_op' {e : Expr} {p1 p2 : PExpr} {o : Op}
    (h : e.toPExpr? = some (PExpr.op p1 o p2)) :
    ∃ e1 e2, e = Expr.op e1 o e2 ∧ e1.toPExpr? = some p1 ∧ e2.toPExpr? = some p2 := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

/-- The guard's dependency set, whenever it is computed, contains location `0`. -/
private theorem deps_mem_zero {cap : CapturedVarEnv}
    (hcap : (VarTypeEnv.ofCaptured cap).get? "a" = some cRef) {fuel : Nat} {deps : Deps}
    (h : extractDepsFromPred (Predicate.guardClosure 0 "w" cbody cap) fuel = .ok deps) :
    0 ∈ deps := by
  have hcap' : (VarTypeEnv.ofCaptured cap)["a"]? = some cRef := hcap
  rcases fuel with _ | _ | _ | f
  all_goals simp [extractDepsFromPred, extractDepsFromPred.extractDepsFromPExpr, cbody,
    hcap', cRef] at h
  all_goals simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, bind, Except.bind] at h
  subst h
  simp [cS0, LocSet.union, LocSet.singleton, LocSet.empty]

/-- The dependency set is computed with fuel 3. -/
private theorem deps_three {cap : CapturedVarEnv}
    (hcap : (VarTypeEnv.ofCaptured cap).get? "a" = some cRef) :
    ∃ deps, extractDepsFromPred (Predicate.guardClosure 0 "w" cbody cap) 3 = .ok deps := by
  have hcap' : (VarTypeEnv.ofCaptured cap)["a"]? = some cRef := hcap
  cases hh : extractDepsFromPred (Predicate.guardClosure 0 "w" cbody cap) 3 with
  | ok d => exact ⟨d, rfl⟩
  | error e =>
      exfalso
      simp [extractDepsFromPred, extractDepsFromPred.extractDepsFromPExpr, cbody,
        hcap', cRef] at hh
      simp [pure, Except.pure] at hh

/-- The in-scope rule gives `a` its captured type in the context. -/
private theorem a_in_scope {S : VarTypeEnv} {cap : CapturedVarEnv} (h : GuardInScope S "w" cbody cap)
    (hcap : (VarTypeEnv.ofCaptured cap).lookup "a" = some cRef) :
    S.lookup "a" = some cRef := by
  obtain ⟨qt, _, _, hcap', hS, _, _, _⟩ := h.reads "a" (by simp [PExpr.freeVars, cbody])
  have : qt = cRef := Option.some.inj (hcap'.symm.trans hcap)
  subst this
  exact hS

/-- In a context where `a` is `ref {0}`, `a` holds the address of location `0`. -/
theorem a_at_zero {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {a0 : Address}
    (hA : ctx.varEnv.lookup "a" = some cRef)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hρ : ρ.lookup "a" = some (Value.loc a0)) :
    θ.lookup 0 = some a0 := by
  obtain ⟨w, hw, hty⟩ := hric.2 hA
  rw [hρ] at hw
  cases hw
  cases hty with
  | loc hl hin =>
    rename_i l
    have : l = 0 := by
      simp only [cS0, LocSet.singleton, Std.ExtTreeSet.mem_insert,
        Std.ExtTreeSet.not_mem_empty, or_false] at hin
      exact ((Nat.compare_eq_eq).1 hin).symm
    subst this
    exact hl

private theorem cellSat_iff {θ : RealizationMap} {μ : Memory} {a0 : Address} {n m : Int} {b : Bool}
    {k : Tag} (hθ : θ.lookup 0 = some a0) (hμ : μ.lookup a0 = some n)
    (hev : LeanPoison.evalOp Op.gt (Value.num m) (Value.num n) = some (Value.bool b)) :
    (b = true ↔ cellSat k θ μ (Value.num m)) := by
  simp only [LeanPoison.evalOp, Option.some.injEq, Value.bool.injEq] at hev
  subst hev
  constructor
  · intro h
    exact ⟨a0, n, m, hθ, hμ, rfl, by simpa using h⟩
  · rintro ⟨a, n', m', ha, hn, hv, hlt⟩
    rw [hθ] at ha
    cases ha
    rw [hμ] at hn
    cases hn
    cases hv
    simpa using hlt

theorem cellSat_cell {θ : RealizationMap} {μ : Memory} {a0 : Address} {n m : Int} {k : Tag}
    (hθ : θ.lookup 0 = some a0) (hμ : μ.lookup a0 = some n) :
    cellSat k θ μ (Value.num m) ↔ n < m := by
  constructor
  · rintro ⟨a, n', m', ha, hn, hv, hlt⟩
    rw [hθ] at ha
    cases ha
    rw [hμ] at hn
    cases hn
    cases hv
    exact hlt
  · intro h
    exact ⟨a0, n, m, hθ, hμ, rfl, h⟩

/-- **`cellSat` meets the laws for every table of guards `w => w > !a`**, against the
    real `matchGuard`, with no hypothesis beyond the law's own. -/
theorem cellSat_lawful {P : TagMeaning} (hP : CellTable P) : PredSatLaws cellSat P := by
  refine ⟨?_, ?_⟩
  · intro condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hric hterm
    obtain ⟨pe, hpe, hown⟩ := matchGuard_ok_matched_owner_inScope ctx condition k deps hmatch
    rcases hown with
      ⟨x, qt, arg, pbody, pcap, hlookup, hpred, heq, hscope⟩ |
      ⟨x, qt, ls, arg, pbody, pcap, hlookup, hetyp, _hpois, hne, hall, heq, hscope⟩
    · obtain ⟨rfl, harg, hbody, hcap⟩ := hP _ _ (hwf.1
        (GuardDescInEnvsDeep.intro qt k ⟨arg, pbody, pcap⟩
          (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt))
          (by simp [qtypGuardDesc?, hpred])))
      have harg' : arg = "w" := harg
      have hbody' : pbody = cbody := hbody
      have hcap' : (VarTypeEnv.ofCaptured pcap).lookup "a" = some cRef := hcap
      subst harg' hbody'
      have hA := a_in_scope hscope hcap'
      obtain ⟨pe1, f', rfl, h1⟩ := eqW_body heq
      have hpe1 := eqW_var h1
      subst hpe1
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_op' hpe
      have := toPExpr?_var' he1
      subst this
      obtain ⟨e2', rfl, he2'⟩ := toPExpr?_deref' he2
      have := toPExpr?_var' he2'
      subst this
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨v', hρ, rfl, hv1⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      subst hv1
      obtain ⟨c2, a0, n, ht2', hμ, rfl, _, _, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht2
      obtain ⟨va, hρa, rfl, hva⟩ := terminatesTo_var_inv' _ _ _ _ ht2'
      subst hva
      have hθ := a_at_zero hA hric hρa
      cases v1 with
      | num m =>
        exact ⟨Value.num m, Or.inl ⟨x, qt, "w", cbody, pcap, hlookup, hpred, hρ⟩,
          cellSat_iff hθ hμ hev⟩
      | _ => simp [LeanPoison.evalOp] at hev
    · obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
        have hlist : ls.toList.isEmpty = false := by
          rw [ExtTreeSet.isEmpty_toList]; exact hne
        cases htl : ls.toList with
        | nil => simp [htl] at hlist
        | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
      obtain ⟨memQt, hmem, hpredm⟩ := hall l hl
      obtain ⟨rfl, harg, hbody, hcap⟩ := hP _ _ (hwf.1
        (GuardDescInEnvsDeep.intro memQt k ⟨arg, pbody, pcap⟩
          (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt))
          (by simp [qtypGuardDesc?, hpredm])))
      have harg' : arg = "w" := harg
      have hbody' : pbody = cbody := hbody
      have hcap' : (VarTypeEnv.ofCaptured pcap).lookup "a" = some cRef := hcap
      subst harg' hbody'
      have hA := a_in_scope hscope hcap'
      obtain ⟨pe1, f', rfl, h1⟩ := eqW_body heq
      have hpe1 := eqW_deref h1
      subst hpe1
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_op' hpe
      obtain ⟨e1', rfl, he1'⟩ := toPExpr?_deref' he1
      have := toPExpr?_var' he1'
      subst this
      obtain ⟨e2', rfl, he2'⟩ := toPExpr?_deref' he2
      have := toPExpr?_var' he2'
      subst this
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨c1', a1, m, ht1', hμ1, rfl, hmem1, hvar1, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht1
      obtain ⟨vx, hρx, rfl, hvx⟩ := terminatesTo_var_inv' _ _ _ _ ht1'
      subst hvx
      obtain ⟨c2, a0, n, ht2', hμ, rfl, _, _, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht2
      obtain ⟨va, hρa, rfl, hva⟩ := terminatesTo_var_inv' _ _ _ _ ht2'
      subst hva
      have hρa' : ρ.lookup "a" = some (Value.loc a0) := by
        rw [hvar1] at hρa; exact hρa
      have hμ' : μ.lookup a0 = some n := by
        rw [hmem1] at hμ; exact hμ
      have hθ := a_at_zero hA hric hρa'
      obtain ⟨w, hw, hty⟩ := hric.2 hlookup
      rw [hρx] at hw
      cases hw
      rw [hetyp] at hty
      cases hty with
      | loc hl1 hin1 =>
        rename_i l1
        obtain ⟨memQt1, hmem1', hpred1⟩ := hall l1 hin1
        refine ⟨Value.num m, Or.inr ⟨x, qt, memQt1, ls, l1, a1, m, "w", cbody, pcap,
          hlookup, hetyp, hin1, hmem1', hpred1, hl1, hμ1, rfl⟩, ?_⟩
        exact cellSat_iff hθ hμ' hev
  · intro k d θ θ' μ μ' v hd hagree
    obtain ⟨rfl, harg, hbody, hcap⟩ := hP k d hd
    obtain ⟨d3, hd3⟩ := deps_three (cap := d.capEnv) hcap
    have hd3' : extractDepsFromPred (Predicate.guardClosure 0 d.argName d.body d.capEnv) 3 =
        .ok d3 := by
      rw [harg, hbody]; exact hd3
    have h0 : (0 : Loc) ∈ d3 := deps_mem_zero hcap hd3
    obtain ⟨hθ, hμ⟩ := hagree 3 d3 hd3'
    have hθ0 := hθ 0 h0
    constructor
    · rintro ⟨a, n, m, ha, hn, hv, hlt⟩
      refine ⟨a, n, m, hθ0.symm.trans ha, ?_, hv, hlt⟩
      rw [← hμ 0 h0 a ha]; exact hn
    · rintro ⟨a, n, m, ha, hn, hv, hlt⟩
      have ha' : θ.lookup 0 = some a := hθ0.trans ha
      refine ⟨a, n, m, ha', ?_, hv, hlt⟩
      rw [hμ 0 h0 a ha']; exact hn

theorem cellLaws_empty : PredSatLaws cellSat ∅ :=
  cellSat_lawful (fun k d h => by simp [TagMeaning.lookup] at h)

/-! ## The typing of the program -/

/-- Every guard of the log is `w => w > !a` at tag 0, with `a : ref {0}` captured. -/
def logOk (log : List TagAlloc) : Bool :=
  log.all fun a => a.tag == 0 && a.argName == "w" && a.body == cbody &&
    decide ((VarTypeEnv.ofCaptured a.capEnv).lookup "a" = some cRef)

theorem cellTable_of_log {log : List TagAlloc} (h : logOk log = true) :
    CellTable (programTable ∅ log) := by
  intro k d hk
  rcases programTable_within ∅ log k d hk with h0 | ⟨a, ha, hat, rfl⟩
  · simp [TagMeaning.lookup] at h0
  · simp only [logOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h a ha
    exact ⟨hat.symm.trans h1, h2, h3, h4⟩

def factsB (b : Bool) : Bool :=
  isOkB (typecheckExpr (K b) progA 60) &&
  isOkB (typecheckExpr (K b) (.newRef (.num 5)) 58) &&
  decide ((rN b).qualType = cRef) &&
  (ctxA b).memEnv.contains 0 &&
  ((ctxA b).nextTag == 0) &&
  isOkB (typecheckExpr (ctxA b) valD 56) &&
  ((rD b).regime'.lookup? 0 == some b) &&
  logOk (rootRes b).tagLog' &&
  ((rootRes b).qualType.etyp == ETyp.int) &&
  ((rootRes b).qualType.poison == false)

private theorem factsB_ok (b : Bool) : factsB b = true := by
  cases b <;> decide +kernel

structure Facts (b : Bool) : Prop where
  root : typecheckExpr (K b) progA 60 = .ok (rootRes b)
  newref : typecheckExpr (K b) (.newRef (.num 5)) 58 = .ok (rN b)
  rN_qt : (rN b).qualType = cRef
  memEnv0 : (ctxA b).memEnv.contains 0 = true
  nextTag0 : (ctxA b).nextTag = 0
  decl : typecheckExpr (ctxA b) valD 56 = .ok (rD b)
  regime0 : (rD b).regime'.lookup? 0 = some b
  log : logOk (rootRes b).tagLog' = true
  etyp : (rootRes b).qualType.etyp = .int
  poison : (rootRes b).qualType.poison = false

theorem facts_of (b : Bool) : Facts b := by
  have hf := factsB_ok b
  simp only [factsB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
  exact ⟨eq_okVal h1, eq_okVal h2, h3, h4, h5, eq_okVal h6, h7, h8, h9, h10⟩

private theorem rD_facts (b : Bool) : VFacts (ctxA b) (rD b) := by
  have h := (facts_of b).decl
  exact v_facts_of (fuel := 55) (poison := true) (by simpa [typecheckExpr, valD] using h)

/-! ## The runs -/

/-- The state after `ref 5`: the cell at address 0 holds 5. -/
def cA (m n : Int) : Config :=
  { cfgX m n with memory := (cfgX m n).memory.update 0 5, nextAddr := 1 }

/-- The state at the declaration: `a` is bound to the address 0. -/
def cfgA (m n : Int) : Config :=
  { cA m n with varEnv := (cfgX m n).varEnv.update "a" (.loc 0) }

theorem run_newRef (m n : Int) : terminatesTo (.newRef (.num 5)) (cfgX m n) (cA m n) (.loc 0) :=
  ⟨3, false, by simp [beval, freshAddr, cA, cfgX]⟩

/-- The declaration returns the value of the registry and leaves the state. -/
private theorem run_valD (m n : Int) : terminatesTo valD (cfgA m n) (cfgA m n) (.num m) :=
  ⟨1, false, by simp [beval, valD, cfgA, cA, cfgX, regA, valueMatchesTyp]⟩

private theorem mem0 (m n : Int) : (cfgA m n).memory.lookup 0 = some 5 := by
  show ((∅ : Memory).insert 0 5).get? 0 = some 5
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]

/-- A run with the value `m > 5` returns `m`. -/
private theorem run_progA_gt (m n : Int) (hm : 5 < m) :
    terminatesTo progA (cfgX m n) (cA m n) (.num m) := by
  refine ⟨10, false, ?_⟩
  simp [progA, valD, test, beval, freshAddr, cA, cfgX, regA, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, hm, Memory.update]

/-- A run with the value `m ≤ 5` returns `0`. -/
private theorem run_progA_le (m n : Int) (hm : m ≤ 5) :
    terminatesTo progA (cfgX m n) (cA m n) (.num 0) := by
  refine ⟨10, false, ?_⟩
  simp [progA, valD, test, beval, freshAddr, cA, cfgX, regA, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, Int.not_lt.mpr hm, Memory.update]

/-! ## Inversion -/

/-- The root step, the step of the body of `a`, and the declaration step. -/
def U0 (b : Bool) (m n : Int) : Step := ⟨K b, progA, 60, cfgX m n⟩
def UA (b : Bool) (m n : Int) : Step := ⟨ctxA b, .vlet "v" valD test, 58, cfgA m n⟩
def UD (b : Bool) (m n : Int) : Step := ⟨ctxA b, valD, 56, cfgA m n⟩

inductive InSet (b : Bool) (m n : Int) : Step → Prop
  | u0 : InSet b m n (U0 b m n)
  | uA : InSet b m n (UA b m n)
  | uD : InSet b m n (UD b m n)
  | leaf {s : Step} : noApp s.e = true → InSet b m n s

private theorem inSet_step {b : Bool} {m n : Int} {s s' : Step} (hs : InSet b m n s)
    (h : SubStep s s') : InSet b m n s' := by
  cases hs with
  | u0 =>
      have hh := SubStep.vlet_inv (ctx := K b) (x := "a") (e1 := .newRef (.num 5))
        (e2 := .vlet "v" valD test) (F := 60) (cfg := cfgX m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r, c, v, hr, hc, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r = rN b := ok_inj hr (facts_of b).newref
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hc (run_newRef m n)
        exact InSet.uA
  | uA =>
      have hh := SubStep.vlet_inv (ctx := ctxA b) (x := "v") (e1 := valD) (e2 := test)
        (F := 58) (cfg := cfgA m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩
      · exact InSet.uD
      · exact InSet.leaf rfl
  | uD => cases h
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

/-- The run declares the extern value once, at `UD`. -/
private theorem inSet_val {b : Bool} {m n : Int} {s : Step} {res : TypeResult} {cf : Config}
    {o : Value} (hs : InSet b m n s) (h : ExternValAt s res cf o) :
    res = rD b ∧ cf = cfgA m n ∧ o = .num m ∧ s = UD b m n := by
  cases hs with
  | leaf hl => exact absurd h (ExternValAt.not_of_reach_noApp hl (Reach.refl _))
  | u0 => cases h
  | uA => cases h
  | uD =>
      cases h with
      | mk htc hrun =>
          obtain rfl := ok_inj htc (facts_of b).decl
          obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_valD m n)
          exact ⟨rfl, rfl, rfl, rfl⟩

private theorem reach_A (b : Bool) (m n : Int) : Reach (U0 b m n) (UA b m n) :=
  Relation.ReflTransGen.single (SubStep.vletBody (facts_of b).newref (run_newRef m n))

private theorem reach_D (b : Bool) (m n : Int) : Reach (U0 b m n) (UD b m n) :=
  Relation.ReflTransGen.tail (reach_A b m n) SubStep.vletBound

private theorem val_mk (b : Bool) (m n : Int) : ExternValAt (UD b m n) (rD b) (cfgA m n) (.num m) :=
  ExternValAt.mk (facts_of b).decl (run_valD m n)

/-! ## The starting state -/

theorem K_vars (b : Bool) : ∀ x qt, (K b).varEnv.lookup x = some qt → qt = pInt := by
  intro x qt h
  by_cases hx : x = "x"
  · subst hx
    simp only [K, VarTypeEnv_lookup_update_eq, Option.some.injEq] at h
    exact h.symm
  · simp only [K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h

private theorem lookupX (n : Int) :
    (VarEnv.update [] "x" (.num n)).lookup "x" = some (.num n) := by
  simp [VarEnv.update, VarEnv.lookup]

theorem instantiatesK (b : Bool) (n : Int) :
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

/-! ## The premises -/

def θ0 : RealizationMap := (∅ : RealizationMap).insert 0 0

private theorem θ0_lookup {l : Loc} {a : Address} (h : θ0.lookup l = some a) : l = 0 ∧ a = 0 := by
  simp only [θ0, RealizationMap.lookup] at h
  by_cases hl : l = 0
  · subst hl
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self] at h
    simp at h
    exact ⟨rfl, h.symm⟩
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at h
    have hc : ¬ compare 0 l = Ordering.eq := by
      intro hc; exact hl ((Nat.compare_eq_eq).1 hc).symm
    simp [hc] at h

private theorem θ0_zero : θ0.lookup 0 = some 0 := by simp [θ0, RealizationMap.lookup]

theorem ctxA_a (b : Bool) : (ctxA b).varEnv.lookup "a" = some cRef := by
  show ((K b).varEnv.update "a" (rN b).qualType).lookup "a" = some cRef
  rw [VarTypeEnv_lookup_update_eq, (facts_of b).rN_qt]

private theorem cfgA_a (m n : Int) : (cfgA m n).varEnv.lookup "a" = some (Value.loc 0) := by
  simp [cfgA, cfgX, VarEnv.update, VarEnv.lookup]

/-- The map `θ0` realises the context at the declaration in the state there: `a`
    holds the address 0, whose cell holds 5. -/
private theorem ricA (b : Bool) (m n : Int) :
    runtimeInstantiatesCtx (ctxA b) (cfgA m n).memory (cfgA m n).varEnv θ0 := by
  refine ⟨?_, ?_⟩
  · intro l a h
    obtain ⟨rfl, rfl⟩ := θ0_lookup h
    refine ⟨(facts_of b).memEnv0, ?_⟩
    simp [cfgA, cA, cfgX, Memory.update]
  · intro x qt h
    have h' : ((K b).varEnv.update "a" (rN b).qualType).lookup x = some qt := h
    by_cases hx : x = "a"
    · subst hx
      rw [VarTypeEnv_lookup_update_eq, Option.some.injEq] at h'
      subst h'
      rw [(facts_of b).rN_qt]
      refine ⟨Value.loc 0, cfgA_a m n, ?_⟩
      exact valueHasETyp.loc (l := 0) θ0_zero (by simp [cS0, LocSet.singleton])
    · rw [VarTypeEnv_lookup_update_ne _ "a" x _ hx] at h'
      have hq := K_vars b x qt h'
      subst hq
      have hx' : x = "x" := by
        by_contra hx'
        simp only [K] at h'
        rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx'] at h'
        simp [VarTypeEnv.lookup] at h'
      subst hx'
      exact ⟨Value.num n, by simp [cfgA, cfgX, VarEnv.update, VarEnv.lookup, List.lookup],
        valueHasETyp.num n⟩

/-- *Match* holds exactly when the value satisfies the guard as the assignment says:
    the cell holds 5 at the declaration, so `5 < m` when the tag is true and
    `m ≤ 5` when it is false. -/
theorem match_iff (b : Bool) (m n : Int) :
    ExternCallsMatch cellSat (U0 b m n) ↔ (5 < m ↔ b = true) := by
  have hF := facts_of b
  have hf := rD_facts b
  constructor
  · intro h
    have hv := h.vals _ _ _ _ (reach_D b m n) (val_mk b m n)
    obtain ⟨arg, body, cap, hp⟩ := hf.guard
    obtain ⟨a, ha, hat⟩ := hf.logged
    have hiff := hv a ha arg body cap b (by rw [hat]; exact hp)
      (by rw [hat, hF.nextTag0]; exact hF.regime0) θ0 (ricA b m n)
    rw [hat, hF.nextTag0] at hiff
    exact (cellSat_cell (k := 0) (μ := (cfgA m n).memory) (θ := θ0) θ0_zero (mem0 m n)).symm.trans
      hiff
  · intro hm
    refine ⟨fun _ _ _ _ _ _ hreach hcall => absurd hcall (inSet_call (inSet_reach hreach)),
      fun s res cf o hreach hval => ?_⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSet_val (inSet_reach hreach) hval
    intro a ha arg body cap b' hp hR θ hθ
    obtain ⟨arg', body', cap', hp'⟩ := hf.guard
    have hat : a.tag = 0 := by
      rw [hp'] at hp
      simp only [Predicate.guardClosure.injEq] at hp
      exact hp.1.symm.trans hF.nextTag0
    rw [hat] at hR ⊢
    rw [hF.regime0, Option.some.injEq] at hR
    subst hR
    have hθ0 : θ.lookup 0 = some 0 := a_at_zero (ctxA_a b) hθ (cfgA_a m n)
    rw [cellSat_cell hθ0 (mem0 m n)]
    exact hm

/-- *Agreement* holds for every pair of runs: they make no extern call. -/
theorem agree (b : Bool) (m n₀ n₁ : Int) : ExternCallsAgree (U0 b m n₀) (U0 b m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ _ _ _ _ hc₀ _ _ =>
    absurd hc₀ (inSet_call (inSet_reach hr₀))⟩

/-! ## The other premises of the theorem -/

/-- No critical input; the scenario commits the tags of `@251`. -/
def sV : InputSpec := { locs := ∅, vars := ∅, regimeExterns := [251] }

/-- The observation: the returned integer. -/
def obsRet : ObservableSpec := { locs := ∅, retEtyp? := some .int }

private theorem pInt_not_clean (R : Regime) : ¬ qtypCleanUnder R pInt := by
  intro h
  cases h with
  | clean hpoison => simp [pInt] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, pInt] at htag

theorem externRegimeMatchesK (b : Bool) : ExternRegimeMatchesInputSpec sV (K b) := by
  refine ⟨fun {id} hid k => ?_, fun {id} hid k => ?_⟩
  · have h : id ≠ 251 := by simpa [sV] using hid
    simp [K, polV, h]
  · simp only [sV, List.mem_singleton] at hid
    subst hid
    exact ⟨b, by simp [K, polV]⟩

theorem wfSpecV : wfInputSpec sV := by
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

theorem ctxMatchesK (b : Bool) : ctxMatchesInputSpec sV (K b) := by
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

theorem wfCtxK (b : Bool) : wfTypeContext (K b) := by
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

theorem tagBoundedK (b : Bool) : TagBoundedCtx (K b) := by
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

/-- The starting context has no guard: `x` is a poisoned `int` without predicate. -/
private theorem noGuardK (b : Bool) {k : Tag} {d : GuardDesc} :
    ¬ GuardDescInEnvsDeep (K b).varEnv (K b).memEnv k d := by
  intro hdeep
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

theorem wfTmK (b : Bool) : wfTagMeaningCtx ∅ (K b) :=
  EnvRespectsTagMeaning.intro (fun hdeep => absurd hdeep (noGuardK b))

theorem guardCapsK (b : Bool) : GuardCapsBelow (K b) :=
  fun _ _ hdeep => absurd hdeep (noGuardK b)

theorem tmBoundedK (b : Bool) : TagMeaningBounded ∅ (K b).nextTag := by
  intro k d h
  simp [TagMeaning.lookup] at h
theorem wfRegimeK (b : Bool) : wfRegime (K b).regime sV := by
  have htags : inputSpecTags sV = [] := rfl
  refine And.intro ?_ ?_
  · intro k hk
    rw [htags] at hk
    cases hk
  · intro k hk
    simp [K, Regime.lookup?] at hk

theorem wfθ₀ : wfRealizationMap ∅ := by
  intro l₁ l₂ a h
  simp [RealizationMap.lookup] at h

theorem wfCX (m n : Int) : wfConfig (cfgX m n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgX] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

theorem reservedWFV (m : Int) : RegistryReservedWF (regA m) ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regA_noLoc h).elim

theorem disciplineK (b : Bool) (m : Int) :
    ReservedDiscipline (regA m) (K b).declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regA_noLoc h).elim
  · intro id a h _ l
    exact (regA_noLoc h).elim

theorem trustedInitK (b : Bool) (n : Int) :
    trustedVarsClosureRegimeInit cellSat (K b).regime sV (K b) ∅
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

theorem consistentK (b : Bool) {ρ : VarEnv} :
    consistentRegimeSpec cellSat (K b).regime sV ∅ ρ ∅ := by
  unfold consistentRegimeSpec
  have hnil : memEnvToLocQTypList sV.locs = [] := rfl
  have hnil' : sV.vars.toList = [] := rfl
  rw [hnil, hnil']
  exact ⟨trivial, trivial⟩

theorem agreeCriticalK (b : Bool) {ρ₁ ρ₂ : VarEnv} :
    agreeOnCriticalInputsUnderRegimeSpec cellSat (K b).regime sV ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · intro x qt h _
    simp [sV, VarTypeEnv.lookup] at h

theorem agreeTrustedK (b : Bool) {ρ₁ ρ₂ : VarEnv} :
    agreeOnTrustedInputs cellSat (K b).regime sV (K b) ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [K, MemoryTypeEnv.lookup] at h
  · intro x qt h _ hclean
    rw [K_vars b x qt h] at hclean
    exact absurd hclean (pInt_not_clean _)

theorem inProg_test {id : ExternId} {d : ExternDeclaration}
    (h : ExternDeclarationInProgram test id d) : False := by
  simp only [test] at h
  cases h with
  | ite_cond h =>
      cases h with
      | op_left h => cases h
      | op_right h => cases h with | deref h => cases h
  | ite_then h => cases h
  | ite_else h => cases h

private theorem trustedK (b : Bool) (m : Int) : InitialContextTrusted (vReg m) progA (K b) := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 251 ∧ d = vDecl := by
        simp only [progA, valD] at hp
        cases hp with
        | vlet_bound h => cases h with | newRef h => cases h
        | vlet_body h =>
            cases h with
            | vlet_bound h => cases h; exact ⟨rfl, rfl⟩
            | vlet_body h => exact (inProg_test h).elim
      obtain ⟨rfl, rfl⟩ := h
      simp [vReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K_vars b _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt


/-! ## The theorem -/

/-- The typing and the premises: under both assignments the program is typed as a
    clean `int`, the laws hold of the program table, and *match* holds exactly when
    the cell and the value are as the assignment says. -/
theorem typing_case :
    (∀ b, typecheck (K b) progA 60 = .ok (rootRes b) ∧
      (rootRes b).qualType.etyp = .int ∧ (rootRes b).qualType.poison = false ∧
      PredSatLaws cellSat (programTable ∅ (rootRes b).tagLog')) ∧
    ExternCallsMatch cellSat (U0 true 7 4) ∧ ExternCallsMatch cellSat (U0 false 3 4) ∧
    ¬ ExternCallsMatch cellSat (U0 false 7 4) ∧ ¬ ExternCallsMatch cellSat (U0 true 3 4) := by
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
  · have hF := facts_of b
    exact ⟨hF.root, hF.etyp, hF.poison, cellSat_lawful (cellTable_of_log hF.log)⟩
  · exact (match_iff true 7 4).2 (by decide)
  · exact (match_iff false 3 4).2 (by decide)
  · rw [match_iff false 7 4]; decide
  · rw [match_iff true 3 4]; decide

/-- **The theorem at
    `let a = ref 5 in let v = extern val @251 : (int :> poisoned { 0, w => w > !a }) in if v > !a then v else 0`**
    under the assignment `b`, with the registry holding `m`: when the value satisfies
    the guard as the assignment says (`5 < m ↔ b = true`), two runs from any `x`
    return the same value. -/
theorem same_return (b : Bool) (m : Int) (hm : 5 < m ↔ b = true) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo progA (cfgX m n₀) cf₀ o₀) (hr₁ : terminatesTo progA (cfgX m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  have hF := facts_of b
  have hlaws := cellSat_lawful (cellTable_of_log hF.log)
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (vReg m) progA sV obsRet (K b) (externRegimeMatchesK b)
      (trustedK b m) wfSpecV rfl (ctxMatchesK b) (wfCtxK b) rfl rfl rfl (tagBoundedK b)
      (guardCapsK b) cellSat ∅ (wfTmK b) (tmBoundedK b) cellLaws_empty 60 (rootRes b) hF.root
      (And.intro (fun et h => by
          simp only [obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hF.etyp, hF.poison⟩)
        (fun _ _ h => by simp [obsRet, MemoryETypEnv.lookup] at h))
      hlaws ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (wfRegimeK b) wfθ₀ wfθ₀
      (wfCX m n₀) (wfCX m n₁) (reservedWFV m) (reservedWFV m) (disciplineK b m) (disciplineK b m)
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (instantiatesK b n₀) (instantiatesK b n₁) (trustedInitK b n₀) (trustedInitK b n₁)
      (consistentK b) (consistentK b) ((match_iff b m n₀).2 hm)
      ((match_iff b m n₁).2 hm) (agreeCriticalK b) (agreeTrustedK b)
      (agree b m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **Tag true, value 7**: the runs from `x = 4` and `x = 5` both return 7. -/
theorem true_7 :
    terminatesTo progA (cfgX 7 4) (cA 7 4) (.num 7) ∧
    terminatesTo progA (cfgX 7 5) (cA 7 5) (.num 7) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo progA (cfgX 7 4) cf₀ o₀ → terminatesTo progA (cfgX 7 5) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_progA_gt 7 4 (by decide), run_progA_gt 7 5 (by decide),
    fun hr₀ hr₁ => same_return true 7 (by decide) 4 5 hr₀ hr₁⟩

/-- **Tag false, value 3**: the runs from `x = 4` and `x = 5` both return 0. -/
theorem false_3 :
    terminatesTo progA (cfgX 3 4) (cA 3 4) (.num 0) ∧
    terminatesTo progA (cfgX 3 5) (cA 3 5) (.num 0) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo progA (cfgX 3 4) cf₀ o₀ → terminatesTo progA (cfgX 3 5) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_progA_le 3 4 (by decide), run_progA_le 3 5 (by decide),
    fun hr₀ hr₁ => same_return false 3 (by decide) 4 5 hr₀ hr₁⟩

end ValCell

end ExternCallsWitness
