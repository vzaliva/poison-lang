-- Regime consistency definitions shared by Preservation and FaultRobustness.
-- Extracted for Issue #112 fix to avoid circular imports.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.TypeSafety
import LeanProofs.JoinMemEnv
import LeanProofs.SemanticsProperties
import Std.Data.ExtTreeMap
open Std

-- Abstract predicate satisfaction: does a predicate with the given tag hold
-- for a value in a given memory state?
abbrev PredSat := Tag → Memory → Value → Prop

-- Guard descriptor (arg name, body, captured env) for tag-meaning tracking
structure GuardDesc where
  argName : Name
  body    : PExpr
  capEnv  : CapturedVarEnv
  deriving Repr, BEq

abbrev TagMeaning := ExtTreeMap Tag GuardDesc

namespace TagMeaning
  @[inline] def lookup (tm : TagMeaning) (k : Tag) : Option GuardDesc :=
    tm.get? k

  @[inline] def update (tm : TagMeaning) (k : Tag) (d : GuardDesc) : TagMeaning :=
    tm.insert k d

  /-- `tm` contains a binding for `k`. -/
  def hasKey (tm : TagMeaning) (k : Tag) : Prop :=
    tm.contains k
end TagMeaning

/-- Extract (tag, descriptor) from a guardClosure predicate. -/
def qtypGuardDesc? (qt : QTyp) : Option (Tag × GuardDesc) :=
  match qt.pred with
  | Predicate.guardClosure k arg body cap =>
      some (k, { argName := arg, body := body, capEnv := cap })
  | _ => none

/-- When `qtypGuardDesc?` returns `some (k, d)`, the predicate is that guard closure. -/
lemma qtypGuardDesc?_eq_some_pred_guardClosure
    {qt : QTyp} {k : Tag} {d : GuardDesc}
    (h : qtypGuardDesc? qt = some (k, d)) :
    qt.pred = Predicate.guardClosure k d.argName d.body d.capEnv := by
  cases qt with
  | mk _ _ pred =>
      cases pred with
      | noPred => simp [qtypGuardDesc?] at h
      | guardOnly _ => simp [qtypGuardDesc?] at h
      | guardClosure k' arg body cap =>
        have heq := Option.some.inj h
        have hk : k' = k := (Prod.mk.inj heq).1
        have hd : { argName := arg, body := body, capEnv := cap } = d := (Prod.mk.inj heq).2
        subst hk hd
        rfl

/-- Extract captured typing env from closures. -/
def fnCapturedEnv : FnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ _ ρ => ρ

def pfnCapturedEnv : PFnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ ρ => ρ

/-- Deep occurrence of a QTyp inside another QTyp. -/
inductive QTypInQTyp : QTyp → QTyp → Prop where
  | self (qt : QTyp) :
      QTypInQTyp qt qt
  | in_arrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List FnTClosure)
      (tcl : FnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.arrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ fnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter
  | in_parrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List PFnTClosure)
      (tcl : PFnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.parrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ pfnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter
  | trans (qt₁ qt₂ qt₃ : QTyp) :
      QTypInQTyp qt₁ qt₂ →
      QTypInQTyp qt₂ qt₃ →
      QTypInQTyp qt₁ qt₃

/-- Deep occurrence of a QTyp in (σ, Γ): start from top-level entries, then descend
    through closure-captured environments using `QTypInQTyp`. -/
inductive QTypInEnvs : QTyp → VarTypeEnv → MemoryTypeEnv → Prop where
  | inVar (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (x : Name) (qt qtRoot : QTyp) :
      σ.lookup x = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ
  | inMem (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (l : Loc) (qt qtRoot : QTyp) :
      Γ.lookup l = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ

/-- Deep membership of guard descriptors reachable from (σ, Γ). -/
inductive GuardDescInEnvsDeep (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Tag → GuardDesc → Prop where
  | intro (qt : QTyp) (k : Tag) (d : GuardDesc) :
      QTypInEnvs qt σ Γ →
      qtypGuardDesc? qt = some (k, d) →
      GuardDescInEnvsDeep σ Γ k d

inductive EnvRespectsTagMeaning (tm : TagMeaning) (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Prop where
  | intro :
      (∀ {k d}, GuardDescInEnvsDeep σ Γ k d → tm.lookup k = some d) →
      EnvRespectsTagMeaning tm σ Γ

/-- Context respects tag meaning: all guard descriptors in ctx are in tm. -/
def wfTagMeaningCtx (tm : TagMeaning) (ctx : TypeContext) : Prop :=
  EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv

/-- Lookup after var-env update at the same key. -/
lemma VarTypeEnv_lookup_update_eq (env : VarTypeEnv) (x : Name) (qt : QTyp) :
  (env.update x qt).lookup x = some qt := by
  simp [VarTypeEnv.update, VarTypeEnv.lookup]

/-- Lookup after var-env update at a different key. -/
lemma VarTypeEnv_lookup_update_ne (env : VarTypeEnv) (x y : Name) (qt : QTyp) (h_ne : y ≠ x) :
  (env.update x qt).lookup y = env.lookup y := by
  by_cases h_eq : varTypeEnvCmp x y = .eq
  · have hxy : x = y := LawfulEqCmp.eq_of_compare h_eq
    exact (h_ne hxy.symm).elim
  · simp [VarTypeEnv.update, VarTypeEnv.lookup, ExtTreeMap.getElem?_insert, h_eq]

/-- Lookup after mem-env update at the same location. -/
lemma MemoryTypeEnv_lookup_update_eq (Γ : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (Γ.update l qt).lookup l = some qt := by
  simp [MemoryTypeEnv.update, MemoryTypeEnv.lookup]

/-- Lookup after mem-env update at a different location. -/
lemma MemoryTypeEnv_lookup_update_ne (Γ : MemoryTypeEnv) (l l' : Loc) (qt : QTyp) (h_ne : l' ≠ l) :
  (Γ.update l qt).lookup l' = Γ.lookup l' := by
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have hl : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact h_ne hl.symm
  simp [MemoryTypeEnv.update, MemoryTypeEnv.lookup, ExtTreeMap.getElem?_insert, hcmp]

/-- If the target type is not a function type, deep inclusion collapses to equality. -/
lemma QTypInQTyp_eq_of_nonFunctionTarget {qtInner qtOuter : QTyp}
    (h : QTypInQTyp qtInner qtOuter)
    (hnotfun : qtOuter.etyp.isFunctionType = false) :
    qtInner = qtOuter := by
  induction h with
  | self qt =>
      rfl
  | in_arrow _qtInner _qtOuter st₁ st₂ p tcls tcl x hetyp _ _ =>
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | in_parrow _qtInner _qtOuter st₁ st₂ p tcls tcl x hetyp _ _ =>
      simp [hetyp, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun
  | trans qt₁ qt₂ qt₃ h12 h23 ih12 ih23 =>
      have h23eq : qt₂ = qt₃ := ih23 hnotfun
      subst h23eq
      exact ih12 hnotfun

/-- Transport deep-membership across qualified types with the same expression type.
    Either the witness is the root itself, or it is still deeply included in the
    target with matching `etyp`. -/
lemma QTypInQTyp_transport_etyp
    {qtInner qtOuter qtOuter' : QTyp}
    (h : QTypInQTyp qtInner qtOuter)
    (hetyp : qtOuter.etyp = qtOuter'.etyp) :
    qtInner = qtOuter ∨ QTypInQTyp qtInner qtOuter' := by
  induction h generalizing qtOuter' with
  | self qt =>
      exact Or.inl rfl
  | in_arrow qtInner qtOuter st₁ st₂ p tcls tcl x houterEtyp htcl hcap =>
      have houterEtyp' : qtOuter'.etyp = ETyp.arrow st₁ st₂ p tcls := by
        calc
          qtOuter'.etyp = qtOuter.etyp := by simp [hetyp]
          _ = ETyp.arrow st₁ st₂ p tcls := by simpa using houterEtyp
      exact Or.inr (QTypInQTyp.in_arrow qtInner qtOuter' st₁ st₂ p tcls tcl x houterEtyp' htcl hcap)
  | in_parrow qtInner qtOuter st₁ st₂ p tcls tcl x houterEtyp htcl hcap =>
      have houterEtyp' : qtOuter'.etyp = ETyp.parrow st₁ st₂ p tcls := by
        calc
          qtOuter'.etyp = qtOuter.etyp := by simp [hetyp]
          _ = ETyp.parrow st₁ st₂ p tcls := by simpa using houterEtyp
      exact Or.inr (QTypInQTyp.in_parrow qtInner qtOuter' st₁ st₂ p tcls tcl x houterEtyp' htcl hcap)
  | trans qt₁ qt₂ qt₃ h12 h23 ih12 ih23 =>
      have h23' := ih23 hetyp
      cases h23' with
      | inl hEq23 =>
          subst hEq23
          have h12' := ih12 hetyp
          cases h12' with
          | inl hEq12 =>
              exact Or.inl hEq12
          | inr hIn12 =>
              exact Or.inr hIn12
      | inr hIn23 =>
          exact Or.inr (QTypInQTyp.trans qt₁ qt₂ qtOuter' h12 hIn23)

/-- Extend EnvRespectsTagMeaning when memEnv gets one new binding, provided all
    guard descriptors reachable from the inserted `qt` are covered by `tm`. -/
lemma EnvRespectsTagMeaning_memEnv_ext
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (h : EnvRespectsTagMeaning tm σ Γ)
    (hqt : ∀ {qt' k d}, QTypInQTyp qt' qt → qtypGuardDesc? qt' = some (k, d) → tm.lookup k = some d) :
    EnvRespectsTagMeaning tm σ (Γ.update l qt) := by
  let lIns := l
  exact EnvRespectsTagMeaning.intro fun gd =>
    match gd with
    | .intro qt' k d hin hm =>
      match hin with
      | .inVar _ _ x _qt qtRoot hlookup hinq =>
        h.1 (GuardDescInEnvsDeep.intro _qt k d
          (QTypInEnvs.inVar σ Γ x _qt qtRoot hlookup hinq) hm)
      | .inMem _ _ l0 _qt qtRoot hlookup hinq =>
        if h_eq : l0 = lIns then by
          subst h_eq
          have hroot : qtRoot = qt := by
            have hself : (Γ.update lIns qt).lookup lIns = some qt := MemoryTypeEnv_lookup_update_eq Γ lIns qt
            have : some qtRoot = some qt := by
              calc
                some qtRoot = (Γ.update lIns qt).lookup lIns := by
                  symm
                  simpa [lIns] using hlookup
                _ = some qt := hself
            exact Option.some.inj this
          subst hroot
          exact hqt hinq hm
        else
          have hlookup_old : Γ.lookup l0 = some qtRoot := by
            simpa [lIns, MemoryTypeEnv_lookup_update_ne Γ lIns l0 qt h_eq] using hlookup
          h.1 (GuardDescInEnvsDeep.intro _qt k d
            (QTypInEnvs.inMem σ Γ l0 _qt qtRoot hlookup_old hinq) hm)

/-- wfTagMeaningCtx is preserved when context is extended by typecheck result:
    this is immediate once we already know `tm` respects `ctx.varEnv` and `res.memEnv'`. -/
lemma wfTagMeaningCtx_ctxAfter (tm : TagMeaning) (ctx : TypeContext) (res : TypeResult)
    (h : EnvRespectsTagMeaning tm ctx.varEnv res.memEnv') :
    wfTagMeaningCtx tm (ctxAfter ctx res) := by
  simpa [wfTagMeaningCtx, ctxAfter] using h

/-- wfTagMeaningCtx is preserved when varEnv is extended with one binding
    (as in vlet), assuming all deep guard descriptors in `qt` are covered by tm. -/
lemma wfTagMeaningCtx_varEnv_ext (tm : TagMeaning) (ctx : TypeContext) (x : Name) (qt : QTyp)
    (h : wfTagMeaningCtx tm ctx)
    (hqt : ∀ {qt' k d}, QTypInQTyp qt' qt → qtypGuardDesc? qt' = some (k, d) → tm.lookup k = some d) :
    wfTagMeaningCtx tm { ctx with varEnv := ctx.varEnv.update x qt } := by
  let xIns := x
  unfold wfTagMeaningCtx at h ⊢
  exact EnvRespectsTagMeaning.intro fun gd =>
    match gd with
    | .intro qt' k d hin hm =>
      match hin with
      | .inVar _ _ y _qt qtRoot hlookup hinq =>
        if h_eq : y = xIns then by
          subst h_eq
          have hlookup' : (ctx.varEnv.update xIns qt).lookup xIns = some qtRoot := by
            simpa [xIns] using hlookup
          have hroot : qtRoot = qt := by
            have hself : (ctx.varEnv.update xIns qt).lookup xIns = some qt :=
              VarTypeEnv_lookup_update_eq ctx.varEnv xIns qt
            have : some qtRoot = some qt := by
              calc
                some qtRoot = (ctx.varEnv.update xIns qt).lookup xIns := by symm; exact hlookup'
                _ = some qt := hself
            exact Option.some.inj this
          subst hroot
          exact hqt hinq hm
        else
          have hlookup' : (ctx.varEnv.update xIns qt).lookup y = some qtRoot := by
            simpa [xIns] using hlookup
          have hlookup_old : ctx.varEnv.lookup y = some qtRoot := by
            simpa [xIns, VarTypeEnv_lookup_update_ne ctx.varEnv xIns y qt h_eq] using hlookup'
          h.1 (GuardDescInEnvsDeep.intro _qt k d
            (QTypInEnvs.inVar ctx.varEnv ctx.memEnv y _qt qtRoot hlookup_old hinq) hm)
      | .inMem _ _ l0 _qt qtRoot hlookup hinq =>
        h.1 (GuardDescInEnvsDeep.intro _qt k d
          (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l0 _qt qtRoot hlookup hinq) hm)

/-- All deep guard descriptors reachable from `qt` are mapped by `tm`. -/
@[reducible] def QTypRespectsTagMeaning (tm : TagMeaning) (qt : QTyp) : Prop :=
  ∀ {qt' k d}, QTypInQTyp qt' qt → qtypGuardDesc? qt' = some (k, d) → tm.lookup k = some d

/-- Transport `QTypRespectsTagMeaning` across qualified types with the same
    expression type and predicate (poison may differ). -/
lemma QTypRespectsTagMeaning_transport_etyp_pred
    (tm : TagMeaning) (qt qt' : QTyp)
    (hqt : QTypRespectsTagMeaning tm qt)
    (hetyp : qt'.etyp = qt.etyp)
    (hpred : qt'.pred = qt.pred) :
    QTypRespectsTagMeaning tm qt' := by
  intro q k d hinq hqd
  have htr := QTypInQTyp_transport_etyp hinq hetyp
  cases htr with
  | inl hEq =>
      subst hEq
      have hqd' : qtypGuardDesc? qt = some (k, d) := by
        simpa [qtypGuardDesc?, hpred] using hqd
      exact hqt (QTypInQTyp.self qt) hqd'
  | inr hinq' =>
      exact hqt hinq' hqd

/-- Any top-level variable type in a tag-meaning-respecting context also
    respects tag meaning for all of its deep descendants. -/
lemma wfTagMeaningCtx_var_lookup_qtyp
    (tm : TagMeaning) (ctx : TypeContext) (x : Name) (qt : QTyp)
    (h : wfTagMeaningCtx tm ctx)
    (hlookup : ctx.varEnv.lookup x = some qt) :
    QTypRespectsTagMeaning tm qt := by
  intro qt' k d hinq hqd
  exact h.1 (GuardDescInEnvsDeep.intro qt' k d
    (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt' qt hlookup hinq) hqd)

/-- Any top-level memory type in an environment that respects tag meaning
    also respects tag meaning for all of its deep descendants. -/
lemma EnvRespectsTagMeaning_mem_lookup_qtyp
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (h : EnvRespectsTagMeaning tm σ Γ)
    (hlookup : Γ.lookup l = some qt) :
    QTypRespectsTagMeaning tm qt := by
  intro qt' k d hinq hqd
  exact h.1 (GuardDescInEnvsDeep.intro qt' k d
    (QTypInEnvs.inMem σ Γ l qt' qt hlookup hinq) hqd)

/-- Any top-level memory type in a tag-meaning-respecting context also
    respects tag meaning for all of its deep descendants. -/
lemma wfTagMeaningCtx_mem_lookup_qtyp
    (tm : TagMeaning) (ctx : TypeContext) (l : Loc) (qt : QTyp)
    (h : wfTagMeaningCtx tm ctx)
    (hlookup : ctx.memEnv.lookup l = some qt) :
    QTypRespectsTagMeaning tm qt := by
  intro qt' k d hinq hqd
  exact h.1 (GuardDescInEnvsDeep.intro qt' k d
    (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l qt' qt hlookup hinq) hqd)

/-- Transport `QTypRespectsTagMeaning` across qualified types with the same
    expression type when the target has no guard descriptor at the root. -/
lemma QTypRespectsTagMeaning_transport_etyp_noGuard
    (tm : TagMeaning) (qt qt' : QTyp)
    (hqt : QTypRespectsTagMeaning tm qt)
    (hetyp : qt'.etyp = qt.etyp)
    (hguard : qtypGuardDesc? qt' = none) :
    QTypRespectsTagMeaning tm qt' := by
  intro q k d hinq hqd
  have htr := QTypInQTyp_transport_etyp hinq hetyp
  cases htr with
  | inl hEq =>
      subst hEq
      rw [hguard] at hqd
      cases hqd
  | inr hinq' =>
      exact hqt hinq' hqd

/-- When both envs have something at `l`, the joined root at `l` respects tag meaning. -/
lemma QTypRespectsTagMeaning_joinMem_lookup
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ1 Γ2 : MemoryTypeEnv) (l : Loc) (qtRoot : QTyp)
    (h1 : EnvRespectsTagMeaning tm σ Γ1)
    (_h2 : EnvRespectsTagMeaning tm σ Γ2)
    (hlookup : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot)
    (h1_some : Γ1[l]? ≠ none)
    (h2_some : Γ2[l]? ≠ none) :
    QTypRespectsTagMeaning tm qtRoot := by
  cases h1_val : Γ1[l]? with
  | none => exact (h1_some h1_val).elim
  | some qt1 =>
  cases h2_val : Γ2[l]? with
  | none => exact (h2_some h2_val).elim
  | some qt2 =>
  have hqt1 : Γ1[l]? = some qt1 := h1_val
  have hqt2 : Γ2[l]? = some qt2 := h2_val
  have hqt1' : Γ1.lookup l = some qt1 := by
    rw [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?]; exact hqt1
  have hqt2' : Γ2.lookup l = some qt2 := by
    rw [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?]; exact hqt2
  have h1_tm : QTypRespectsTagMeaning tm qt1 :=
    EnvRespectsTagMeaning_mem_lookup_qtyp tm σ Γ1 l qt1 h1 hqt1'
  have h_in : l ∈ (Γ1.keys ++ Γ2.keys).eraseDups := by
    have hmem : l ∈ Γ1 := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 (by simp [hqt1])
    have hkeys : l ∈ Γ1.keys := (ExtTreeMap.mem_keys).2 hmem
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys)
  have hgo := combineExtTreeMaps_go_get_mem Γ1 Γ2
    (fun _ oq1 oq2 => match oq1, oq2 with
      | some qt1, none => some qt1
      | none, some qt2 => some qt2
      | some qt1, some qt2 =>
        let ⟨t1, p1, pred1⟩ := qt1
        let ⟨t2, p2, pred2⟩ := qt2
        if t1 == t2 then some ⟨t1, joinPoison p1 p2, joinPredicates pred1 pred2⟩ else none
      | none, none => none)
    (Γ1.keys ++ Γ2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hjoin' : (combineExtTreeMaps.go Γ1 Γ2 (fun _ oq1 oq2 => match oq1, oq2 with
      | some qt1, none => some qt1
      | none, some qt2 => some qt2
      | some qt1, some qt2 =>
        let ⟨t1, p1, pred1⟩ := qt1
        let ⟨t2, p2, pred2⟩ := qt2
        if t1 == t2 then some ⟨t1, joinPoison p1 p2, joinPredicates pred1 pred2⟩ else none
      | none, none => none) (Γ1.keys ++ Γ2.keys).eraseDups ({} : MemoryTypeEnv))[l]? = some qtRoot := by
    simpa [joinMemEnvs, combineExtTreeMaps, MemoryTypeEnv.lookup] using hlookup
  rw [hgo] at hjoin'
  have h1'' : ExtTreeMap.get? Γ1 l = some qt1 := by simpa [MemoryTypeEnv.lookup] using hqt1'
  have h2'' : ExtTreeMap.get? Γ2 l = some qt2 := by simpa [MemoryTypeEnv.lookup] using hqt2'
  simp only [h1'', h2''] at hjoin'
  cases qt1 with
  | mk t1 p1 pred1 =>
      cases qt2 with
      | mk t2 p2 pred2 =>
          unfold QTypRespectsTagMeaning
          intro qt' k d hinq hqd
          by_cases ht_eq : (t1 == t2) = true
          · -- Both maps had the value; types matched; joined value at root
            have heq_inner : QTyp.mk t1 (joinPoison p1 p2) (joinPredicates pred1 pred2) = qtRoot := by
              have hmatch := hjoin'
              simp only [ht_eq] at hmatch
              exact Option.some.inj hmatch
            have hetyp : qtRoot.etyp = t1 := congr_arg QTyp.etyp heq_inner.symm
            have hpred_eq : qtRoot.pred = joinPredicates pred1 pred2 := congr_arg QTyp.pred heq_inner.symm
            have hetyp' : qtRoot.etyp = (QTyp.mk t1 p1 pred1).etyp := hetyp.trans (by rfl)
            by_cases hguard : qtypGuardDesc? qtRoot = none
            · exact (QTypRespectsTagMeaning_transport_etyp_noGuard tm (QTyp.mk t1 p1 pred1) qtRoot h1_tm hetyp' hguard) hinq hqd
            · obtain ⟨⟨k0, d0⟩, hqd_root⟩ := Option.ne_none_iff_exists'.1 hguard
              have hpred_gc : qtRoot.pred = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv :=
                qtypGuardDesc?_eq_some_pred_guardClosure hqd_root
              have hjoin_gc :
                  joinPredicates pred1 pred2 =
                    Predicate.guardClosure k0 d0.argName d0.body d0.capEnv := by
                calc
                  joinPredicates pred1 pred2 = qtRoot.pred := hpred_eq.symm
                  _ = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv := hpred_gc
              have ⟨hp1, _hp2⟩ := joinPredicates_eq_guardClosure hjoin_gc
              have hpred_root_eq_pred1 : qtRoot.pred = pred1 := by
                calc
                  qtRoot.pred = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv := hpred_gc
                  _ = pred1 := by simp [hp1]
              exact
                (QTypRespectsTagMeaning_transport_etyp_pred tm (QTyp.mk t1 p1 pred1) qtRoot h1_tm
                  hetyp' hpred_root_eq_pred1) hinq hqd
          · -- t1 ≠ t2: join returns none, but hjoin' says we got some
            exfalso
            simp only [ht_eq] at hjoin'
            exact absurd hjoin'.symm (Option.some_ne_none qtRoot)

/-- EnvRespectsTagMeaning is preserved under joinMemEnvs: if both memory envs
    respect tag meaning (with the same var env), so does their join. -/
lemma EnvRespectsTagMeaning_joinMemEnvs
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ1 Γ2 : MemoryTypeEnv)
    (h1 : EnvRespectsTagMeaning tm σ Γ1)
    (h2 : EnvRespectsTagMeaning tm σ Γ2) :
    EnvRespectsTagMeaning tm σ (joinMemEnvs Γ1 Γ2) := by
  exact EnvRespectsTagMeaning.intro fun gd =>
    match gd with
    | .intro qt k d hin hm =>
      match hin with
      | .inVar _ _ x qt qtRoot hlookup hinq =>
        h1.1 (GuardDescInEnvsDeep.intro qt k d
          (QTypInEnvs.inVar σ Γ1 x qt qtRoot hlookup hinq) hm)
      | .inMem _ _ l qt qtRoot hlookup hinq =>
        by
          have hcontains : (joinMemEnvs Γ1 Γ2).contains l := by
            rw [Std.ExtTreeMap.contains_iff_mem]
            exact (Std.ExtTreeMap.mem_iff_isSome_getElem?).2
              (by rw [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] at hlookup; simp [hlookup])
          have hor := joinMemEnvs_contains_implies_or Γ1 Γ2 l hcontains
          cases hor with
          | inl hleft =>
            by_cases h2_none : Γ2[l]? = none
            · have heq := joinMemEnvs_lookup_eq_left_of_right_none Γ1 Γ2 l hleft h2_none
              rw [heq] at hlookup
              exact h1.1 (GuardDescInEnvsDeep.intro qt k d
                (QTypInEnvs.inMem σ Γ1 l qt qtRoot hlookup hinq) hm)
            · have h1_some : Γ1[l]? ≠ none := by
                intro heq
                have hnot_some : ¬Option.isSome (Γ1[l]?) := by simp [heq]
                have hmem : l ∈ Γ1 := (Std.ExtTreeMap.contains_iff_mem).mp hleft
                exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
              exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 h2
                hlookup h1_some h2_none) hinq hm
          | inr hright =>
            by_cases h1_none : Γ1[l]? = none
            · have heq := joinMemEnvs_lookup_eq_right_of_left_none Γ1 Γ2 l h1_none hright
              rw [heq] at hlookup
              exact h2.1 (GuardDescInEnvsDeep.intro qt k d
                (QTypInEnvs.inMem σ Γ2 l qt qtRoot hlookup hinq) hm)
            · have h2_some : Γ2[l]? ≠ none := by
                intro heq
                have hnot_some : ¬Option.isSome (Γ2[l]?) := by simp [heq]
                have hmem : l ∈ Γ2 := (Std.ExtTreeMap.contains_iff_mem).mp hright
                exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
              exact (QTypRespectsTagMeaning_joinMem_lookup tm σ Γ1 Γ2 l qtRoot h1 h2 hlookup
                h1_none h2_some) hinq hm

/-- Membership in a captured environment produced from `VarTypeEnv.toCaptured`
    gives the corresponding map lookup. -/
lemma VarTypeEnv_lookup_of_toCaptured_mem
    (σ : VarTypeEnv) (x : Name) (qt : QTyp) :
    (x, qt) ∈ VarTypeEnv.toCaptured σ →
    σ.lookup x = some qt := by
  intro hmem
  have hmem' : (x, qt) ∈ σ.toList := by
    simpa [VarTypeEnv.toCaptured] using hmem
  have hget : σ[x]? = some qt :=
    (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some).1 hmem'
  simpa [VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?] using hget

/-- Any deep type inside a regular function type built from `ctx.varEnv`
    is either the function type itself or rooted in `ctx.varEnv`. -/
lemma QTypInQTyp_fn_regular_root_or_self
    (ctx : TypeContext) (x : Name) (st₁ st₂ : Typ) (p : Poison) (body : Expr)
    {qt target : QTyp}
    (h : QTypInQTyp qt target)
    (htarget : target =
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩) :
    qt =
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩
    ∨ ∃ y qtRoot, ctx.varEnv.lookup y = some qtRoot ∧ QTypInQTyp qt qtRoot := by
  induction h generalizing ctx x st₁ st₂ p body with
  | self qt0 =>
      subst qt0
      left
      rfl
  | in_arrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      let tcl0 : FnTClosure := FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)
      have hEtyp : ETyp.arrow st1 st2 p0 tcls = ETyp.arrow st₁ st₂ p [tcl0] := by
        simpa [tcl0] using houterEtyp.symm
      have htcls : tcls = [tcl0] := by
        injection hEtyp with _ _ _ htcls
      have htcl0 : tcl = tcl0 := by
        have : tcl ∈ [tcl0] := by simpa [htcls] using htcl
        simpa using this
      have hcap' : (y, qtInner) ∈ VarTypeEnv.toCaptured ctx.varEnv := by
        simpa [fnCapturedEnv, tcl0, htcl0] using hcap
      have hlookup : ctx.varEnv.lookup y = some qtInner :=
        VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv y qtInner hcap'
      right
      exact ⟨y, qtInner, hlookup, QTypInQTyp.self qtInner⟩
  | in_parrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      simp at houterEtyp
  | trans qt1 qt2 qt3 h12 h23 ih12 ih23 =>
      have h23' := ih23 (ctx := ctx) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p) (body := body) htarget
      cases h23' with
      | inl hEq =>
          exact ih12 (ctx := ctx) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p) (body := body) hEq
      | inr hroot =>
          rcases hroot with ⟨y, qtRoot, hlookup, hIn⟩
          right
          exact ⟨y, qtRoot, hlookup, QTypInQTyp.trans qt1 qt2 qtRoot h12 hIn⟩

/-- Any deep type inside a regular pure-function type built from `ctx.varEnv`
    is either the function type itself or rooted in `ctx.varEnv`. -/
lemma QTypInQTyp_pfn_regular_root_or_self
    (ctx : TypeContext) (x : Name) (st₁ st₂ : Typ) (p : Poison) (body : PExpr)
    {qt target : QTyp}
    (h : QTypInQTyp qt target)
    (htarget : target =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩) :
    qt =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩
    ∨ ∃ y qtRoot, ctx.varEnv.lookup y = some qtRoot ∧ QTypInQTyp qt qtRoot := by
  induction h generalizing ctx x st₁ st₂ p body with
  | self qt0 =>
      subst qt0
      left
      rfl
  | in_arrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      simp at houterEtyp
  | in_parrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      let tcl0 : PFnTClosure := PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)
      have hEtyp : ETyp.parrow st1 st2 p0 tcls = ETyp.parrow st₁ st₂ p [tcl0] := by
        simpa [tcl0] using houterEtyp.symm
      have htcls : tcls = [tcl0] := by
        injection hEtyp with _ _ _ htcls
      have htcl0 : tcl = tcl0 := by
        have : tcl ∈ [tcl0] := by simpa [htcls] using htcl
        simpa using this
      have hcap' : (y, qtInner) ∈ VarTypeEnv.toCaptured ctx.varEnv := by
        simpa [pfnCapturedEnv, tcl0, htcl0] using hcap
      have hlookup : ctx.varEnv.lookup y = some qtInner :=
        VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv y qtInner hcap'
      right
      exact ⟨y, qtInner, hlookup, QTypInQTyp.self qtInner⟩
  | trans qt1 qt2 qt3 h12 h23 ih12 ih23 =>
      have h23' := ih23 (ctx := ctx) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p) (body := body) htarget
      cases h23' with
      | inl hEq =>
          exact ih12 (ctx := ctx) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p) (body := body) hEq
      | inr hroot =>
          rcases hroot with ⟨y, qtRoot, hlookup, hIn⟩
          right
          exact ⟨y, qtRoot, hlookup, QTypInQTyp.trans qt1 qt2 qtRoot h12 hIn⟩

/-- Regular `fn` results preserve tag-meaning respect from the captured typing
    environment. -/
lemma QTypRespectsTagMeaning_fn_regular
    (tm : TagMeaning) (ctx : TypeContext)
    (x : Name) (st₁ st₂ : Typ) (p : Poison) (body : Expr)
    (h : wfTagMeaningCtx tm ctx) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩ := by
  intro qt k d hinq hqd
  have hroot :=
    QTypInQTyp_fn_regular_root_or_self ctx x st₁ st₂ p body hinq rfl
  cases hroot with
  | inl hEq =>
      subst hEq
      simp [qtypGuardDesc?] at hqd
  | inr hIn =>
      rcases hIn with ⟨y, qtRoot, hlookup, hInRoot⟩
      exact (wfTagMeaningCtx_var_lookup_qtyp tm ctx y qtRoot h hlookup) hInRoot hqd

/-- Regular `pfn` results preserve tag-meaning respect from the captured typing
    environment. -/
lemma QTypRespectsTagMeaning_pfn_regular
    (tm : TagMeaning) (ctx : TypeContext)
    (x : Name) (st₁ st₂ : Typ) (p : Poison) (body : PExpr)
    (h : wfTagMeaningCtx tm ctx) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        p, Predicate.noPred⟩ := by
  intro qt k d hinq hqd
  have hroot :=
    QTypInQTyp_pfn_regular_root_or_self ctx x st₁ st₂ p body hinq rfl
  cases hroot with
  | inl hEq =>
      subst hEq
      simp [qtypGuardDesc?] at hqd
  | inr hIn =>
      rcases hIn with ⟨y, qtRoot, hlookup, hInRoot⟩
      exact (wfTagMeaningCtx_var_lookup_qtyp tm ctx y qtRoot h hlookup) hInRoot hqd

/-- For non-function qualified types, deep inclusion is only `self`; if the
    root has no guard descriptor, tag-meaning respect is immediate. -/
lemma QTypRespectsTagMeaning_of_nonFunction_noGuard
    (tm : TagMeaning) (qt : QTyp)
    (hnotfun : qt.etyp.isFunctionType = false)
    (hguard : qtypGuardDesc? qt = none) :
    QTypRespectsTagMeaning tm qt := by
  intro qt' k d hinq hqd
  have hEq : qt' = qt := QTypInQTyp_eq_of_nonFunctionTarget hinq hnotfun
  subst hEq
  rw [hguard] at hqd
  cases hqd

/-- If `tm` respects `(σ.update x qtNew, Γ)` and the original binding at `x`
    (when present) also respects `tm`, then `tm` respects `(σ, Γ)`. -/
lemma EnvRespectsTagMeaning_of_update
    (tm : TagMeaning) (x : Name) (σ : VarTypeEnv) (qtNew : QTyp) (Γ : MemoryTypeEnv)
    (hUpd : EnvRespectsTagMeaning tm (σ.update x qtNew) Γ)
    (hOld : ∀ {qt}, σ.lookup x = some qt → QTypRespectsTagMeaning tm qt) :
    EnvRespectsTagMeaning tm σ Γ := by
  exact EnvRespectsTagMeaning.intro fun gd =>
    match gd with
    | .intro qt k d hin hm =>
      match hin with
      | .inVar _ _ y _qt qtRoot hlookup hinq =>
        if hxy : y = x then by
          subst hxy
          exact (hOld hlookup) hinq hm
        else
          have hlookupUpd : (σ.update x qtNew).lookup y = some qtRoot := by
            simpa [VarTypeEnv_lookup_update_ne σ x y qtNew hxy] using hlookup
          hUpd.1 (GuardDescInEnvsDeep.intro _qt k d
            (QTypInEnvs.inVar (σ.update x qtNew) Γ y _qt qtRoot hlookupUpd hinq) hm)
      | .inMem _ _ l _qt qtRoot hΓ hinq =>
        hUpd.1 (GuardDescInEnvsDeep.intro _qt k d
          (QTypInEnvs.inMem (σ.update x qtNew) Γ l _qt qtRoot hΓ hinq) hm)

/-- EnvRespectsTagMeaning for extended varEnv implies it for smaller varEnv when
    σ' = σ.update x0 qt (so σ doesn't have x0) and ∀ x ≠ x0, σ.lookup x = σ'.lookup x. -/
lemma EnvRespectsTagMeaning_subbind (tm : TagMeaning) (x0 : Name) (σ σ' : VarTypeEnv) (Γ : MemoryTypeEnv)
    (hnone : σ.lookup x0 = none)
    (hext : ∀ x, x ≠ x0 → σ.lookup x = σ'.lookup x)
    (h : EnvRespectsTagMeaning tm σ' Γ) :
    EnvRespectsTagMeaning tm σ Γ :=
  EnvRespectsTagMeaning.intro fun gd =>
    match gd with
    | .intro qt k d hin hm =>
      match hin with
      | .inVar _ _ x _qt qtRoot hlookup hinq =>
        if hx : x = x0 then by
          subst hx; rw [hnone] at hlookup; cases hlookup
        else
          have hσ' : σ'.lookup x = some qtRoot := by rw [← hext x hx, hlookup]
          h.1 (GuardDescInEnvsDeep.intro _qt k d (QTypInEnvs.inVar σ' Γ x _qt qtRoot hσ' hinq) hm)
      | .inMem _ _ l _qt qtRoot hΓ hinq =>
        h.1 (GuardDescInEnvsDeep.intro _qt k d (QTypInEnvs.inMem σ' Γ l _qt qtRoot hΓ hinq) hm)

-- Laws that constrain the abstract `PredSat` relation.
structure PredSatLaws (predSat : PredSat) (tm : TagMeaning) : Prop where
  -- Bidirectional match law: if match_guard recognizes the condition as tag k,
  -- then the condition's boolean result matches predSat on the owning value.
  match_iff : ∀ (mode : LeanPoison.EvalMode) (condition : Expr) (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
                  (k : Tag) (deps : Deps)
                  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (addr : Address) (pm : Bool) (cfg : Config)
                  (v : Value) (b : Bool),
    EnvRespectsTagMeaning tm σ Γ →
    matchGuard condition Γ σ = .ok (k, deps) →
    terminatesTo mode condition { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm } cfg (Value.bool b) →
    ( (∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧
          qtypGuardTag qt = some k ∧
          ρ.lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (t : ETyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref t ls ∧
          l0 ∈ ls ∧
          Γ.lookup l0 = some memQt ∧
          qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) →
    (b = true ↔ predSat k μ v)

  mem_monotone : ∀ (k : Tag) (pred : Predicate) (μ μ' : Memory) (v : Value) (deps : Deps) (θ : RealizationMap),
    extractDepsFromPred pred = .ok deps →
    (∀ l, l ∈ deps → ∀ a, θ.lookup l = some a → μ.lookup a = μ'.lookup a) →
    (predSat k μ v ↔ predSat k μ' v)

-- Check if a QTyp-attached predicate holds using abstract satisfaction relation
inductive qtypPredHolds (predSat : PredSat) : QTyp → Memory → Value → Prop where
  | noPred_ok {qt : QTyp} {μ v}
      (h : qt.pred = Predicate.noPred) :
      qtypPredHolds predSat qt μ v
  | guardClosure_ok {qt : QTyp} {μ v k arg_name pred_body var_env}
      (h : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v
  | guardOnly_ok {qt : QTyp} {μ v k}
      (h : qt.pred = Predicate.guardOnly k)
      (hSat : predSat k μ v) :
      qtypPredHolds predSat qt μ v

-- Elementwise predicate for location regime consistency (inductive for easy inversion)
inductive locsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (θ : RealizationMap) : (Loc × QTyp) → Prop where
  | noPred_ok (entry : Loc × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      locsRegime predSat R μ θ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Loc × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      locsRegime predSat R μ θ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Loc × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
      (a : Address) (n : Int) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hreal : θ.lookup entry.fst = some a)
      (hmem : μ.lookup a = some n)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ (Value.num n)) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ (Value.num n))) :
      locsRegime predSat R μ θ entry

-- Elementwise predicate for variable regime consistency (inductive for easy inversion)
inductive varsRegime (predSat : PredSat) (R : Regime) (μ : Memory) (ρ : VarEnv) : (Name × QTyp) → Prop where
  | noPred_ok (entry : Name × QTyp)
      (hpred : qtypGuardTag entry.snd = none) :
      varsRegime predSat R μ ρ entry
  -- Guard-only predicates impose no regime consistency beyond tag presence in S
  | guardOnly_ok (entry : Name × QTyp) (k : Tag)
      (hgo : entry.snd.pred = Predicate.guardOnly k) :
      varsRegime predSat R μ ρ entry
  -- Guard-closure predicates must align with the regime: holds iff R(k)=true
  | withPred_ok (entry : Name × QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
      (v : Value) (b : Bool)
      (hclos : entry.snd.pred = Predicate.guardClosure k arg_name pred_body var_env)
      (hregime : R.lookup? k = some b)
      (hvar : ρ.lookup entry.fst = some v)
      (hconsist : (b = true → qtypPredHolds predSat entry.snd μ v) ∧
                  (b = false → ¬qtypPredHolds predSat entry.snd μ v)) :
      varsRegime predSat R μ ρ entry

-- Context-indexed runtime-regime consistency: constrains only tags the regime interprets
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l qt k, ctx.memEnv.lookup l = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     locsRegime predSat R μ θ (l, qt)) ∧
  (∀ x qt k, ctx.varEnv.lookup x = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     varsRegime predSat R μ ρ (x, qt))
