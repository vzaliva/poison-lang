-- Regime consistency definitions shared by Preservation and FaultRobustness.
-- Extracted for Issue #112 fix to avoid circular imports.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.Aux
import LeanProofs.TypeSafety
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

/-- `tm` extends to `tm'`: every binding of `tm` is preserved in `tm'`.
    Insertions at fresh keys are allowed; overwrites and removals are forbidden.

    Built on the generic `ExtTreeMap.IsSubmap` (`LeanProofs/Aux.lean`). -/
abbrev TagMeaningExtends (tm tm' : TagMeaning) : Prop :=
  ExtTreeMap.IsSubmap tm tm'

infix:50 " ⊑ " => TagMeaningExtends

theorem TagMeaningExtends.refl (tm : TagMeaning) : tm ⊑ tm :=
  ExtTreeMap.IsSubmap.refl tm

theorem TagMeaningExtends.trans {tm₁ tm₂ tm₃ : TagMeaning}
    (h₁ : tm₁ ⊑ tm₂) (h₂ : tm₂ ⊑ tm₃) : tm₁ ⊑ tm₃ :=
  ExtTreeMap.IsSubmap.trans h₁ h₂

theorem TagMeaningExtends.lookup {tm tm' : TagMeaning} (h : tm ⊑ tm') {k : Tag} {d : GuardDesc}
    (hlookup : tm.lookup k = some d) : tm'.lookup k = some d :=
  h k d hlookup

/-- `tm` contains no entries at or above `bound`. Threaded alongside
    `wfTagMeaningCtx` so allocation at fresh tag `≥ bound` produces a submap. -/
def TagMeaningBounded (tm : TagMeaning) (bound : Tag) : Prop :=
  ∀ k d, tm.lookup k = some d → k < bound

theorem TagMeaningBounded.empty {bound : Tag} :
    TagMeaningBounded (∅ : TagMeaning) bound := by
  intro k d hlookup
  simp [TagMeaning.lookup] at hlookup

/-- A bounded `tm` does not have a key at or above its bound. -/
theorem TagMeaningBounded.lookup_none_of_ge
    {tm : TagMeaning} {bound : Tag} (h : TagMeaningBounded tm bound)
    {k : Tag} (hk : bound ≤ k) : tm.lookup k = none := by
  by_contra hne
  cases h_lookup : tm.lookup k with
  | none => exact hne h_lookup
  | some d =>
      have hlt := h k d h_lookup
      exact absurd (Nat.lt_of_lt_of_le hlt hk) (Nat.lt_irrefl _)

/-- Inserting at a fresh key `≥ bound` yields a submap. -/
theorem TagMeaningExtends.of_insert_fresh
    (tm : TagMeaning) (k : Tag) (d : GuardDesc)
    (h_fresh : tm.lookup k = none) :
    tm ⊑ tm.update k d := by
  unfold TagMeaning.update
  exact ExtTreeMap.IsSubmap_of_insert_fresh tm k d h_fresh

/-- After inserting at fresh tag `bound`, the new bound is `bound + 1`. -/
theorem TagMeaningBounded.insert_succ
    {tm : TagMeaning} {bound : Tag} (h : TagMeaningBounded tm bound) (d : GuardDesc) :
    TagMeaningBounded (tm.update bound d) (bound + 1) := by
  intro k d' hlookup
  unfold TagMeaning.update TagMeaning.lookup at hlookup
  rw [ExtTreeMap.get?_eq_getElem?] at hlookup
  simp only [ExtTreeMap.getElem?_insert] at hlookup
  by_cases h_eq : compare bound k = Ordering.eq
  · have h_k_eq : bound = k := LawfulEqCmp.eq_of_compare h_eq
    subst h_k_eq
    exact Nat.lt_succ_self _
  · simp [h_eq] at hlookup
    rw [← ExtTreeMap.get?_eq_getElem?] at hlookup
    have hlt := h k d' hlookup
    exact Nat.lt_succ_of_lt hlt

/-- Boundedness is monotone in the bound (a tighter bound implies a looser one). -/
theorem TagMeaningBounded.mono {tm : TagMeaning} {b₁ b₂ : Tag}
    (h : TagMeaningBounded tm b₁) (hle : b₁ ≤ b₂) :
    TagMeaningBounded tm b₂ := by
  intro k d hlookup
  exact Nat.lt_of_lt_of_le (h k d hlookup) hle

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
  | .extern _ _ _ _ ρ _ => ρ

def pfnCapturedEnv : PFnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ _ ρ _ => ρ

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

/-- Lookup after mem-env update at the same location.
    Memory stores only poison and pred; lookup reconstructs QTyp with etyp = ETyp.int. -/
private lemma MemoryTypeEnv_lookup_update_eq (Γ : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (Γ.update l qt).lookup l = some ⟨ETyp.int, qt.poison, qt.pred⟩ := by
  simp [MemoryTypeEnv.update, MemoryTypeEnv.lookup]

/-- Lookup after mem-env update at a different location. -/
private lemma MemoryTypeEnv_lookup_update_ne (Γ : MemoryTypeEnv) (l l' : Loc) (qt : QTyp) (h_ne : l' ≠ l) :
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
    guard descriptors reachable from the inserted `qt` are covered by `tm`.
    Memory stores only poison and pred; qt must have etyp = ETyp.int. -/
lemma EnvRespectsTagMeaning_memEnv_ext
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (hqt_int : qt.etyp = ETyp.int)
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
            have hself : (Γ.update lIns qt).lookup lIns = some ⟨ETyp.int, qt.poison, qt.pred⟩ :=
              MemoryTypeEnv_lookup_update_eq Γ lIns qt
            have : some qtRoot = some ⟨ETyp.int, qt.poison, qt.pred⟩ := by
              calc
                some qtRoot = (Γ.update lIns qt).lookup lIns := by symm; simpa [lIns] using hlookup
                _ = some ⟨ETyp.int, qt.poison, qt.pred⟩ := hself
            have heq : qtRoot = ⟨ETyp.int, qt.poison, qt.pred⟩ := Option.some.inj this
            have heq2 : ⟨ETyp.int, qt.poison, qt.pred⟩ = qt := by cases qt; rw [hqt_int.symm]
            exact heq.trans heq2
          rw [hroot] at hinq
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

/-- Monotonicity of `EnvRespectsTagMeaning` along `⊑`: every required guard
    descriptor stays mapped under the extended table. -/
theorem EnvRespectsTagMeaning_mono
    {tm tm' : TagMeaning} {σ : VarTypeEnv} {Γ : MemoryTypeEnv}
    (hext : tm ⊑ tm') (h : EnvRespectsTagMeaning tm σ Γ) :
    EnvRespectsTagMeaning tm' σ Γ :=
  ⟨fun hdeep => hext.lookup (h.1 hdeep)⟩

/-- Monotonicity of `wfTagMeaningCtx` along `⊑`. -/
theorem wfTagMeaningCtx_mono
    {tm tm' : TagMeaning} {ctx : TypeContext}
    (hext : tm ⊑ tm') (h : wfTagMeaningCtx tm ctx) :
    wfTagMeaningCtx tm' ctx :=
  EnvRespectsTagMeaning_mono hext h

/-- Monotonicity of `QTypRespectsTagMeaning` along `⊑`. -/
theorem QTypRespectsTagMeaning_mono
    {tm tm' : TagMeaning} {qt : QTyp}
    (hext : tm ⊑ tm') (h : QTypRespectsTagMeaning tm qt) :
    QTypRespectsTagMeaning tm' qt := by
  intro qt' k d hinq hqd
  exact hext.lookup (h hinq hqd)

/-- Structural canonical extension predicate: `tm'` is a tag-meaning that
    extends `tm` and is consistent with the typecheck result `res` from
    context `ctx` on expression `e`.

    This is a *semantic* packaging — it records the four threaded properties
    without enumerating typecheck cases.  Per-case `StepFR` proofs construct
    witnesses for this Prop inline at each operator: leaves use `tm' = tm`,
    composites thread the canonical extension produced by subexpression IHs,
    and `app` / `externVal` construct post-allocation witnesses via
    `ExternBatchTagMeaningExtension`. -/
def IsCanonicalExtension
    (tm : TagMeaning) (ctx : TypeContext) (_e : Expr)
    (res : TypeResult) (tm' : TagMeaning) : Prop :=
  tm ⊑ tm' ∧
  TagMeaningBounded tm' res.nextTag' ∧
  wfTagMeaningCtx tm' (ctxAfter ctx res) ∧
  QTypRespectsTagMeaning tm' res.qualType

namespace IsCanonicalExtension

theorem extends_tm
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr}
    {res : TypeResult} {tm' : TagMeaning}
    (h : IsCanonicalExtension tm ctx e res tm') : tm ⊑ tm' :=
  h.1

theorem bounded
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr}
    {res : TypeResult} {tm' : TagMeaning}
    (h : IsCanonicalExtension tm ctx e res tm') :
    TagMeaningBounded tm' res.nextTag' :=
  h.2.1

theorem wfCtx
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr}
    {res : TypeResult} {tm' : TagMeaning}
    (h : IsCanonicalExtension tm ctx e res tm') :
    wfTagMeaningCtx tm' (ctxAfter ctx res) :=
  h.2.2.1

theorem respectsResult
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr}
    {res : TypeResult} {tm' : TagMeaning}
    (h : IsCanonicalExtension tm ctx e res tm') :
    QTypRespectsTagMeaning tm' res.qualType :=
  h.2.2.2

end IsCanonicalExtension

/-- Reflexive (non-allocating) canonical extension: when `tm' = tm` and the
    output already satisfies the post-typecheck consistency facts, the
    canonical-extension witness is immediate.

    Most `typecheckExpr` cases (literals, variables, ops, fn/pfn,
    sequencing, vlet, etc.) do not allocate fresh tags, so `tm' = tm`
    works.  Allocating cases (`externVal`, closure-application extern
    paths) construct `tm'` non-trivially using `ExternBatchTagMeaningExtension`. -/
theorem IsCanonicalExtension.refl
    {tm : TagMeaning} {ctx : TypeContext} {e : Expr} {res : TypeResult}
    (h_bounded : TagMeaningBounded tm res.nextTag')
    (h_wf : wfTagMeaningCtx tm (ctxAfter ctx res))
    (h_resp : QTypRespectsTagMeaning tm res.qualType) :
    IsCanonicalExtension tm ctx e res tm :=
  ⟨ExtTreeMap.IsSubmap.refl tm, h_bounded, h_wf, h_resp⟩

/-- Composition: chaining two canonical extensions through subexpressions
    transitively combines the submap relation, advances boundedness through
    the second cursor, and inherits the second extension's post-context
    well-formedness and result respectfulness. -/
theorem IsCanonicalExtension.trans
    {tm tm₁ tm₂ : TagMeaning} {ctx ctx₁ : TypeContext} {e₁ e₂ : Expr}
    {res₁ res₂ : TypeResult}
    (h₁ : IsCanonicalExtension tm ctx e₁ res₁ tm₁)
    (h₂ : IsCanonicalExtension tm₁ ctx₁ e₂ res₂ tm₂) :
    tm ⊑ tm₂ ∧
    TagMeaningBounded tm₂ res₂.nextTag' ∧
    wfTagMeaningCtx tm₂ (ctxAfter ctx₁ res₂) ∧
    QTypRespectsTagMeaning tm₂ res₂.qualType :=
  ⟨ExtTreeMap.IsSubmap.trans h₁.1 h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2⟩

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

/-- Predicate-level tag-meaning coverage for stored/update predicates.
    Only `guardClosure` carries a descriptor that must be found in `tm`;
    `noPred` and `guardOnly` are vacuous at this layer. -/
def PredRespectsTagMeaning (tm : TagMeaning) (pred : Predicate) : Prop :=
  ∀ (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
    pred = Predicate.guardClosure k arg_name pred_body var_env →
    tm.lookup k = some { argName := arg_name, body := pred_body, capEnv := var_env }

private lemma qtypGuardDesc_lookup_of_predRespects_int
    (tm : TagMeaning) (poison : Poison) (pred : Predicate)
    (hpred : PredRespectsTagMeaning tm pred) :
    ∀ (k : Tag) (d : GuardDesc),
      qtypGuardDesc? { etyp := ETyp.int, poison := poison, pred := pred } = some (k, d) →
      tm.lookup k = some d := by
  intro k d hqd
  cases pred with
  | noPred =>
      simp [qtypGuardDesc?] at hqd
  | guardOnly k0 =>
      simp [qtypGuardDesc?] at hqd
  | guardClosure k0 arg_name pred_body var_env =>
      simp [qtypGuardDesc?] at hqd
      rcases hqd with ⟨hk, hd⟩
      subst hk
      subst hd
      exact hpred k0 arg_name pred_body var_env rfl

lemma QTypRespectsTagMeaning_int_of_predRespects
    (tm : TagMeaning) (poison : Poison) (pred : Predicate)
    (hpred : PredRespectsTagMeaning tm pred) :
    QTypRespectsTagMeaning tm { etyp := ETyp.int, poison := poison, pred := pred } := by
  intro qt k d hinq hqd
  have hEq : qt = { etyp := ETyp.int, poison := poison, pred := pred } :=
    QTypInQTyp_eq_of_nonFunctionTarget hinq (by
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
  subst hEq
  exact qtypGuardDesc_lookup_of_predRespects_int tm poison pred hpred k d hqd

private lemma PredRespectsTagMeaning_joinPredicates
    (tm : TagMeaning) (p q : Predicate)
    (hp : PredRespectsTagMeaning tm p) :
    PredRespectsTagMeaning tm (joinPredicates p q) := by
  intro k arg_name pred_body var_env hjoin
  have hsplit :=
    joinPredicates_eq_guardClosure
      (p := p) (q := q) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env) hjoin
  exact hp k arg_name pred_body var_env hsplit.1

private lemma PredRespectsTagMeaning_list_fold_updateLocsetWeak
    (tm : TagMeaning) (env : MemoryTypeEnv) (xs : List Loc)
    (storedPoison : Poison) (storedPred : Predicate)
    (hinit : PredRespectsTagMeaning tm storedPred) :
    PredRespectsTagMeaning tm
      ((xs.foldl
        (fun acc l =>
          match env.get? l with
          | some qt => (joinPoison acc.1 qt.poison, joinPredicates acc.2 qt.pred)
          | none => acc)
        (storedPoison, storedPred)).2) := by
  induction xs generalizing storedPoison storedPred with
  | nil =>
      simpa using hinit
  | cons x xs ih =>
      simp [List.foldl]
      cases hget : env.get? x with
      | none =>
          have hget' : env[x]? = none := by simpa using hget
          simpa [hget'] using ih storedPoison storedPred hinit
      | some qt =>
          have hjoin : PredRespectsTagMeaning tm (joinPredicates storedPred qt.pred) :=
            PredRespectsTagMeaning_joinPredicates tm storedPred qt.pred hinit
          have hget' : env[x]? = some qt := by simpa using hget
          simpa [hget'] using ih (joinPoison storedPoison qt.poison)
            (joinPredicates storedPred qt.pred) hjoin

lemma EnvRespectsTagMeaning_updateMemEnv
    (tm : TagMeaning) (σ : VarTypeEnv) (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (hqt_int : qt.etyp = ETyp.int)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hqt : QTypRespectsTagMeaning tm qt) :
    EnvRespectsTagMeaning tm σ (updateMemEnv env l qt) := by
  simpa [updateMemEnv] using
    (EnvRespectsTagMeaning_memEnv_ext tm σ env l qt hqt_int hEnv hqt)

lemma EnvRespectsTagMeaning_list_fold_updateMemEnv
    (tm : TagMeaning) (σ : VarTypeEnv) (xs : List Loc) (env : MemoryTypeEnv) (qt : QTyp)
    (hqt_int : qt.etyp = ETyp.int)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hqt : QTypRespectsTagMeaning tm qt) :
    EnvRespectsTagMeaning tm σ
      (xs.foldl (fun acc l => updateMemEnv acc l qt) env) := by
  induction xs generalizing env with
  | nil =>
      simpa using hEnv
  | cons x xs ih =>
      have h1 : EnvRespectsTagMeaning tm σ (updateMemEnv env x qt) :=
        EnvRespectsTagMeaning_updateMemEnv tm σ env x qt hqt_int hEnv hqt
      simpa using ih (env := updateMemEnv env x qt) h1

lemma EnvRespectsTagMeaning_updateLocsetWeak
    (tm : TagMeaning) (σ : VarTypeEnv) (env : MemoryTypeEnv) (ls : LocSet)
    (storedPoison : Poison) (storedPred : Predicate)
    (hEnv : EnvRespectsTagMeaning tm σ env)
    (hpred : PredRespectsTagMeaning tm storedPred) :
    EnvRespectsTagMeaning tm σ (updateLocsetWeak env ls storedPoison storedPred) := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  have hpred_joined : PredRespectsTagMeaning tm joined.2 := by
    unfold joined
    unfold LocSet.fold
    rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
    exact
      PredRespectsTagMeaning_list_fold_updateLocsetWeak
        tm env ls.toList storedPoison storedPred hpred
  have hfinal_qtyp : QTypRespectsTagMeaning tm finalQt := by
    unfold finalQt
    exact QTypRespectsTagMeaning_int_of_predRespects tm joined.1 joined.2 hpred_joined
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  exact
    EnvRespectsTagMeaning_list_fold_updateMemEnv
      tm σ ls.toList env finalQt (by simp [finalQt]) hEnv hfinal_qtyp

/-- When both envs have something at `l`, the joined root at `l` respects tag meaning. -/
lemma QTypRespectsTagMeaning_joinMem_lookup
    (tm : TagMeaning) (σ : VarTypeEnv) (Γ1 Γ2 : MemoryTypeEnv) (l : Loc) (qtRoot : QTyp)
    (h1 : EnvRespectsTagMeaning tm σ Γ1)
    (hlookup : (joinMemEnvs Γ1 Γ2).lookup l = some qtRoot)
    (h1_some : Γ1[l]? ≠ none)
    (h2_some : Γ2[l]? ≠ none) :
    QTypRespectsTagMeaning tm qtRoot := by
  cases h1_val : Γ1[l]? with
  | none => exact (h1_some h1_val).elim
  | some e1 =>
  cases h2_val : Γ2[l]? with
  | none => exact (h2_some h2_val).elim
  | some e2 =>
  let qt1 : QTyp := ⟨ETyp.int, e1.poison, e1.pred⟩
  let qt2 : QTyp := ⟨ETyp.int, e2.poison, e2.pred⟩
  have hqt1' : Γ1.lookup l = some qt1 := by
    simp [qt1, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h1_val]
  have hqt2' : Γ2.lookup l = some qt2 := by
    simp [qt2, MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, h2_val]
  have h1_tm : QTypRespectsTagMeaning tm qt1 :=
    EnvRespectsTagMeaning_mem_lookup_qtyp tm σ Γ1 l qt1 h1 hqt1'
  have h_in : l ∈ (Γ1.keys ++ Γ2.keys).eraseDups := by
    have hmem : l ∈ Γ1 := (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 (by simp [h1_val])
    have hkeys : l ∈ Γ1.keys := (ExtTreeMap.mem_keys).2 hmem
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys)
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 => some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo := combineExtTreeMaps_go_get_mem Γ1 Γ2 f (Γ1.keys ++ Γ2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfun : f l (Γ1.get? l) (Γ2.get? l) = some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩ := by
    simp [f, Std.ExtTreeMap.get?_eq_getElem?, h1_val, h2_val]
  rw [hfun] at hgo
  have hget_join : (joinMemEnvs Γ1 Γ2).get? l = some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩ := by
    simpa [joinMemEnvs, combineExtTreeMaps] using hgo
  have heq_root : qtRoot = ⟨ETyp.int, joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩ := by
    have hto := memEnv_lookup_toQTyp (joinMemEnvs Γ1 Γ2) l qtRoot hlookup
    have hget := memEnv_get_eq_of_lookup (joinMemEnvs Γ1 Γ2) l qtRoot hlookup
    have heq_mem : MemEntry.mk qtRoot.poison qtRoot.pred = MemEntry.mk (joinPoison e1.poison e2.poison) (joinPredicates e1.pred e2.pred) :=
      Option.some.inj (hget.symm.trans hget_join)
    rw [hto]
    congr 2
    · exact (MemEntry.mk.inj heq_mem).1
    · exact (MemEntry.mk.inj heq_mem).2
  unfold QTypRespectsTagMeaning
  intro qt' k d hinq hqd
  have hetyp' : qtRoot.etyp = qt1.etyp := by rw [heq_root]
  by_cases hguard : qtypGuardDesc? qtRoot = none
  · exact (QTypRespectsTagMeaning_transport_etyp_noGuard tm qt1 qtRoot h1_tm hetyp' hguard) hinq hqd
  · obtain ⟨⟨k0, d0⟩, hqd_root⟩ := Option.ne_none_iff_exists'.1 hguard
    have hpred_gc : qtRoot.pred = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv :=
      qtypGuardDesc?_eq_some_pred_guardClosure hqd_root
    have hjoin_gc :
        joinPredicates e1.pred e2.pred = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv :=
      (congr_arg QTyp.pred heq_root.symm).trans hpred_gc
    have ⟨hp1, _hp2⟩ := joinPredicates_eq_guardClosure hjoin_gc
    have hpred_root_eq_pred1 : qtRoot.pred = e1.pred := by
      calc
        qtRoot.pred = Predicate.guardClosure k0 d0.argName d0.body d0.capEnv := hpred_gc
        _ = e1.pred := by simp [hp1]
    exact
      (QTypRespectsTagMeaning_transport_etyp_pred tm qt1 qtRoot h1_tm hetyp' hpred_root_eq_pred1) hinq hqd

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
private lemma QTypInQTyp_fn_regular_root_or_self
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
private lemma QTypInQTyp_pfn_regular_root_or_self
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

/-- Any deep type inside an extern function type built from `ctx.varEnv`
    is either the function type itself or rooted in `ctx.varEnv`. -/
lemma QTypInQTyp_fn_extern_root_or_self
    (ctx : TypeContext) (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p : Poison)
    (retSpec : ExternReturn) (effects : List Effect) {argQt : QTyp}
    {qt target : QTyp}
    (h : QTypInQTyp qt target)
    (htarget : target =
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.extern id x retSpec effects (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩) :
    qt =
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.extern id x retSpec effects (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩
    ∨ ∃ y qtRoot, ctx.varEnv.lookup y = some qtRoot ∧ QTypInQTyp qt qtRoot := by
  induction h generalizing ctx id x st₁ st₂ p retSpec effects argQt with
  | self qt0 =>
      subst qt0; left; rfl
  | in_arrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      let tcl0 : FnTClosure :=
        FnTClosure.extern id x retSpec effects (VarTypeEnv.toCaptured ctx.varEnv) argQt
      have hEtyp : ETyp.arrow st1 st2 p0 tcls = ETyp.arrow st₁ st₂ p [tcl0] := by
        simpa [tcl0] using houterEtyp.symm
      have htcls : tcls = [tcl0] := by injection hEtyp with _ _ _ htcls
      have htcl0 : tcl = tcl0 := by
        have hmem : tcl ∈ [tcl0] := by simpa [htcls] using htcl
        simpa using hmem
      have hcap' : (y, qtInner) ∈ VarTypeEnv.toCaptured ctx.varEnv := by
        simpa [fnCapturedEnv, tcl0, htcl0] using hcap
      right
      exact ⟨y, qtInner, VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv y qtInner hcap',
             QTypInQTyp.self qtInner⟩
  | in_parrow qtInner qtOuter _ _ _ _ _ _ houterEtyp _ _ =>
      subst qtOuter; simp at houterEtyp
  | trans qt1 qt2 qt3 h12 _ ih12 ih23 =>
      rcases ih23 (ctx := ctx) (id := id) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p)
               (retSpec := retSpec) (effects := effects) (argQt := argQt) htarget with
        hEq | ⟨y, qtRoot, hlookup, hIn⟩
      · exact ih12 (ctx := ctx) (id := id) (x := x) (st₁ := st₁) (st₂ := st₂) (p := p)
               (retSpec := retSpec) (effects := effects) (argQt := argQt) hEq
      · right; exact ⟨y, qtRoot, hlookup, QTypInQTyp.trans qt1 qt2 qtRoot h12 hIn⟩

/-- Extern `fn` results preserve tag-meaning respect from the captured typing environment. -/
lemma QTypRespectsTagMeaning_fn_extern
    (tm : TagMeaning) (ctx : TypeContext)
    (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p : Poison)
    (retSpec : ExternReturn) (effects : List Effect) {argQt : QTyp}
    (h : wfTagMeaningCtx tm ctx) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.arrow st₁ st₂ p [FnTClosure.extern id x retSpec effects (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩ := by
  intro qt k d hinq hqd
  rcases QTypInQTyp_fn_extern_root_or_self ctx id x st₁ st₂ p retSpec effects hinq rfl with hEq | ⟨y, qtRoot, hlookup, hInRoot⟩
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · exact (wfTagMeaningCtx_var_lookup_qtyp tm ctx y qtRoot h hlookup) hInRoot hqd

/-- Any deep type inside an extern pure-function type built from `ctx.varEnv`
    is either the function type itself or rooted in `ctx.varEnv`. -/
lemma QTypInQTyp_pfn_extern_root_or_self
    (ctx : TypeContext) (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p : Poison)
    (retSpec : ExternReturn) {argQt : QTyp}
    {qt target : QTyp}
    (h : QTypInQTyp qt target)
    (htarget : target =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩) :
    qt =
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩
    ∨ ∃ y qtRoot, ctx.varEnv.lookup y = some qtRoot ∧ QTypInQTyp qt qtRoot := by
  induction h generalizing ctx id x st₁ st₂ p retSpec argQt with
  | self qt0 =>
      subst qt0; left; rfl
  | in_arrow qtInner qtOuter _ _ _ _ _ _ houterEtyp _ _ =>
      subst qtOuter; simp at houterEtyp
  | in_parrow qtInner qtOuter st1 st2 p0 tcls tcl y houterEtyp htcl hcap =>
      subst qtOuter
      let tcl0 : PFnTClosure :=
        PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt
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

/-- Extern `pfn` results preserve tag-meaning respect from the captured typing environment. -/
lemma QTypRespectsTagMeaning_pfn_extern
    (tm : TagMeaning) (ctx : TypeContext)
    (id : ExternId) (x : Name) (st₁ st₂ : Typ) (p : Poison) (retSpec : ExternReturn)
    {argQt : QTyp}
    (h : wfTagMeaningCtx tm ctx) :
    QTypRespectsTagMeaning tm
      ⟨ETyp.parrow st₁ st₂ p [PFnTClosure.extern id x retSpec (VarTypeEnv.toCaptured ctx.varEnv) argQt],
        p, Predicate.noPred⟩ := by
  intro qt k d hinq hqd
  rcases QTypInQTyp_pfn_extern_root_or_self ctx id x st₁ st₂ p retSpec hinq rfl with hEq | ⟨y, qtRoot, hlookup, hInRoot⟩
  · subst hEq; simp [qtypGuardDesc?] at hqd
  · exact (wfTagMeaningCtx_var_lookup_qtyp tm ctx y qtRoot h hlookup) hInRoot hqd

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

-- Laws that constrain the abstract `PredSat` relation.
structure PredSatLaws (predSat : PredSat) (tm : TagMeaning) : Prop where
  -- Bidirectional match law: if match_guard recognizes the condition as tag k,
  -- then the condition's boolean result matches predSat on the owning value.
  match_iff : ∀ (condition : Expr) (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
                  (fuel : Nat)
                  (k : Tag) (deps : Deps)
                  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (addr : Address)
                  (pm : Bool) (registry : ExternRegistry) (cfg : Config)
                  (v : Value) (b : Bool),
    EnvRespectsTagMeaning tm σ Γ →
    matchGuard condition Γ σ fuel = .ok (k, deps) →
    terminatesTo condition
      { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm, registry := registry }
      cfg (Value.bool b) →
    ( (∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧
          qtypGuardTag qt = some k ∧
          ρ.lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          Γ.lookup l0 = some memQt ∧
          qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) →
    (b = true ↔ predSat k μ v)

  mem_monotone : ∀ (k : Tag) (pred : Predicate) (fuel : Nat)
      (μ μ' : Memory) (v : Value) (deps : Deps) (θ : RealizationMap),
    extractDepsFromPred pred fuel = .ok deps →
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

-- Generic combinator: recurse through closure/peClosure values, checking
-- property P on (σcap, ρcap) at each nesting level. The recursive descent
-- checks that captured variables which are themselves closures also satisfy P.
-- Mirrors the structure of valueHasETyp for recursive closure traversal.
-- Strict positivity is satisfied: the recursive occurrence appears only
-- as the conclusion of ∀ → → → → chain (universally quantified implication).
inductive deepValueQTypProperty (P : CapturedVarEnv → VarEnv → Prop) :
    QTyp → Value → Prop where
  | nonClosure {qt : QTyp} {v : Value} :
      (∀ x_param body ρcap, v ≠ Value.closure x_param body ρcap) →
      (∀ x_param body ρcap, v ≠ Value.peClosure x_param body ρcap) →
      deepValueQTypProperty P qt v
  | closure {qt : QTyp} {v : Value}
      (x_param : Name) (body : Expr) (ρcap : VarEnv)
      (σcap : CapturedVarEnv) (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure) :
      v = Value.closure x_param body ρcap →
      qt.etyp = ETyp.arrow st1 st2 p tcls →
      FnTClosure.regular x_param body σcap ∈ tcls →
      P σcap ρcap →
      (∀ (x : Name) (qt_x : QTyp) (v_x : Value),
        σcap.lookup x = some qt_x →
        ρcap.lookup x = some v_x →
        deepValueQTypProperty P qt_x v_x) →
      deepValueQTypProperty P qt v
  | closure_extern {qt : QTyp} {v : Value}
      {argPoison : Bool} {argPred : SyntaxPredicate} {argQt : QTyp}
      (id : ExternId) (x_param y : Name) (argTyp : Typ)
      (retSpec : ExternReturn) (effects : List Effect)
      (ρcap : VarEnv) (σcap : CapturedVarEnv) (p : Poison)
      (tcls : List FnTClosure) :
      v = Value.closure x_param (Expr.externFn id y argTyp argPoison argPred retSpec effects) ρcap →
      qt.etyp = ETyp.arrow argTyp (parseReturnType retSpec) p tcls →
      FnTClosure.extern id x_param retSpec effects σcap argQt ∈ tcls →
      P σcap ρcap →
      (∀ (x : Name) (qt_x : QTyp) (v_x : Value),
        σcap.lookup x = some qt_x →
        ρcap.lookup x = some v_x →
        deepValueQTypProperty P qt_x v_x) →
      deepValueQTypProperty P qt v
  | peClosure {qt : QTyp} {v : Value}
      (x_param : Name) (body : Expr) (pbody : PExpr) (ρcap : VarEnv)
      (σcap : CapturedVarEnv) (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure) :
      v = Value.peClosure x_param body ρcap →
      qt.etyp = ETyp.parrow st1 st2 p tcls →
      Expr.toPExpr? body = some pbody →
      PFnTClosure.regular x_param pbody σcap ∈ tcls →
      P σcap ρcap →
      (∀ (x : Name) (qt_x : QTyp) (v_x : Value),
        σcap.lookup x = some qt_x →
        ρcap.lookup x = some v_x →
        deepValueQTypProperty P qt_x v_x) →
      deepValueQTypProperty P qt v
  | peClosure_extern {qt : QTyp} {v : Value}
      {argPoison : Bool} {argPred : SyntaxPredicate} {argQt : QTyp}
      (id : ExternId) (x_param y : Name) (argTyp : Typ)
      (retSpec : ExternReturn)
      (ρcap : VarEnv) (σcap : CapturedVarEnv) (p : Poison)
      (tcls : List PFnTClosure) :
      v = Value.peClosure x_param (Expr.externPfn id y argTyp argPoison argPred retSpec) ρcap →
      qt.etyp = ETyp.parrow argTyp (parseReturnType retSpec) p tcls →
      PFnTClosure.extern id x_param retSpec σcap argQt ∈ tcls →
      P σcap ρcap →
      (∀ (x : Name) (qt_x : QTyp) (v_x : Value),
        σcap.lookup x = some qt_x →
        ρcap.lookup x = some v_x →
        deepValueQTypProperty P qt_x v_x) →
      deepValueQTypProperty P qt v

-- Monotonicity of deepValueQTypProperty under monotone P.
lemma deepValueQTypProperty_mono
    {P P' : CapturedVarEnv → VarEnv → Prop}
    (hPP : ∀ σcap ρcap, P σcap ρcap → P' σcap ρcap)
    {qt : QTyp} {v : Value}
    (h : deepValueQTypProperty P qt v) :
    deepValueQTypProperty P' qt v := by
  induction h with
  | nonClosure hv hpe => exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem hP _hdeep ih =>
      exact .closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem
        (hPP σcap ρcap hP) (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr)
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls
      hval hetyp hmem hP _hdeep ih =>
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls
        hval hetyp hmem (hPP σcap ρcap hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr)
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem hP _hdeep ih =>
      exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem
        (hPP σcap ρcap hP) (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr)
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem hP
      _hdeep ih =>
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls
        hval hetyp hmem (hPP σcap ρcap hP)
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr)

-- Property checked at each closure nesting level: all captured variables
-- whose type has an active guard tag satisfy varsRegime.
def capturedVarsRegimeProperty (predSat : PredSat) (R : Regime) (μ : Memory)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  ∀ (x : Name) (qt_x : QTyp) (k_x : Tag),
    σcap.lookup x = some qt_x →
    qtypGuardTag qt_x = some k_x →
    R.lookup? k_x ≠ none →
    varsRegime predSat R μ ρcap (x, qt_x)

-- Typing property for captured variables: each binding in σcap is realised in
-- ρcap with a value whose ETyp is justified by θ.  Carried alongside the
-- regime property inside closureCapturedVarsRegime so that a single σcap
-- member witnesses both regime and typing evidence (fixing the member-matching
-- problem in agreeValueUnder_same).
def capturedVarsTypingProperty (θ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap : VarEnv) : Prop :=
  List.Nodup (σcap.map Prod.fst) ∧
  (∀ y qt, σcap.lookup y = some qt → ∃ v, ρcap.lookup y = some v) ∧
  (∀ y qt v, σcap.lookup y = some qt →
    ρcap.lookup y = some v → valueHasETyp θ v qt.etyp)

-- Tracks varsRegime for captured variables inside closure values, recursively
-- across all nesting levels.  Uses qt.etyp (not qt.pred) to find the σcap,
-- so it fires for closures which always have Predicate.noPred.
--
-- Checked against the CURRENT regime R rather than the regime at capture time.
-- This is sound because Regime.monotoneStep only removes entries, so any
-- obligation that held under a larger regime still holds under the current
-- (smaller) one; memory growth is handled by PredSatLaws.mem_monotone.
--
-- The property P carried at each nesting level is the conjunction of the
-- regime property and the typing property for the SAME σcap, eliminating
-- the need to match existential witnesses from two independent sources.
inductive closureCapturedVarsRegime (predSat : PredSat) (R : Regime)
    (qt : QTyp) (μ : Memory) (θ : RealizationMap) (v : Value) : Prop where
  | intro :
      deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
        capturedVarsTypingProperty θ σcap ρcap) qt v →
      closureCapturedVarsRegime predSat R qt μ θ v

-- Context-indexed runtime-regime consistency: constrains only tags the regime
-- interprets.  The third conjunct carries closureCapturedVarsRegime for every
-- variable-value pair, enabling evidence to persist through variable storage
-- (stepFR_vlet) and retrieval (stepFR_var).
def consistentWithRegime (predSat : PredSat) (R : Regime) (ctx : TypeContext)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l qt k, ctx.memEnv.lookup l = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     locsRegime predSat R μ θ (l, qt)) ∧
  (∀ x qt k, ctx.varEnv.lookup x = some qt →
     qtypGuardTag qt = some k →
     R.lookup? k ≠ none →
     varsRegime predSat R μ ρ (x, qt)) ∧
  (∀ x qt v, ctx.varEnv.lookup x = some qt →
     ρ.lookup x = some v →
     closureCapturedVarsRegime predSat R qt μ θ v)

-- Tag-environment consistency for a regime: tags known true in the typing
-- context must be true in the regime interpretation.
def tagEnvConsistentWithRegime (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → regime.lookup? k = some true

-- Regime consistency with a typing context: tags known true in the context must be true in the
-- regime interpretation.
def regimeConsistentWithCtx (ctx : TypeContext) : Prop :=
  tagEnvConsistentWithRegime ctx.tagEnv ctx.regime

-- ------------------------
-- TagEnv/Regime consistency preservation lemmas
--
-- These are proof-only facts about the typechecker infrastructure:
--   * `tagEnvConsistentWithRegime` is stable under the TagEnv operations used by typing
--     (insertion, invalidation, joins), and
--   * typechecking preserves the invariant when starting from a consistent context.

section TagEnvConsistentWithRegimeInsert
variable (tagEnv : TagEnv) (R : Regime) (k : Tag) (deps : Deps)

lemma tagEnvConsistentWithRegime_insert_true
    (h : tagEnvConsistentWithRegime tagEnv R)
    (hk : R.lookup? k = some true) :
    tagEnvConsistentWithRegime (tagEnv.insert k ⟨true, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    -- The inserted binding is the only way to obtain `k ↦ true`.
    simpa [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self] using hk
  · -- Otherwise, defer to the old environment.
    have hcmp : compare k k' ≠ Ordering.eq := by
      -- For Nat tags, `compare k k' = .eq` iff `k = k'`.
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      -- `insert` at a different key does not affect lookups.
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

lemma tagEnvConsistentWithRegime_insert_false
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegime (tagEnv.insert k ⟨false, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    -- Impossible: the inserted value is `false`.
    simp [Std.ExtTreeMap.get?_eq_getElem?] at hget
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

end TagEnvConsistentWithRegimeInsert

def tagEnvConsistentWithRegimeMasked
    (masked : Tag → Prop) (tagEnv : TagEnv) (regime : Regime) : Prop :=
  ∀ k deps, tagEnv.get? k = some ⟨true, deps⟩ → masked k ∨ regime.lookup? k = some true

def regimeConsistentWithCtxMasked
    (masked : Tag → Prop) (ctx : TypeContext) : Prop :=
  tagEnvConsistentWithRegimeMasked masked ctx.tagEnv ctx.regime

def MaskedTagsAbsentFromTrueTagEnv (masked : Tag → Prop) (ctx : TypeContext) : Prop :=
  ∀ k deps, masked k → ctx.tagEnv.get? k = some ⟨true, deps⟩ → False

lemma tagEnvConsistentWithRegimeMasked_unmask
    {masked : Tag → Prop} {tagEnv : TagEnv} {R : Regime}
    (hreg : tagEnvConsistentWithRegimeMasked masked tagEnv R)
    (habsent : ∀ k deps, masked k → tagEnv.get? k = some ⟨true, deps⟩ → False) :
    tagEnvConsistentWithRegime tagEnv R := by
  intro k deps hget
  cases hreg k deps hget with
  | inl hmasked => exact False.elim (habsent k deps hmasked hget)
  | inr hlookup => exact hlookup

lemma regimeConsistentWithCtxMasked_unmask
    {masked : Tag → Prop} {ctx : TypeContext}
    (hreg : regimeConsistentWithCtxMasked masked ctx)
    (habsent : MaskedTagsAbsentFromTrueTagEnv masked ctx) :
    regimeConsistentWithCtx ctx := by
  exact tagEnvConsistentWithRegimeMasked_unmask hreg habsent

lemma MaskedTagsAbsentFromTrueTagEnv_false (ctx : TypeContext) :
    MaskedTagsAbsentFromTrueTagEnv (fun _ => False) ctx := by
  intro k deps hmasked _hget
  exact hmasked.elim

lemma tagEnvConsistentWithRegime_to_masked
    (tagEnv : TagEnv) (R : Regime) (masked : Tag → Prop)
    (h : tagEnvConsistentWithRegime tagEnv R) :
    tagEnvConsistentWithRegimeMasked masked tagEnv R := by
  intro k deps hget
  exact Or.inr (h k deps hget)

section TagEnvConsistentWithRegimeMasked
variable (masked : Tag → Prop) (tagEnv : TagEnv) (R : Regime)

lemma tagEnvConsistentWithRegimeMasked_insert_true
    (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegimeMasked masked tagEnv R)
    (hk : R.lookup? k = some true) :
    tagEnvConsistentWithRegimeMasked masked (tagEnv.insert k ⟨true, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    exact Or.inr hk
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

lemma MaskedTagsAbsentFromTrueTagEnv_insert_true
    {ctx : TypeContext} {k : Tag} {deps : Deps}
    (habsent : MaskedTagsAbsentFromTrueTagEnv masked ctx)
    (hnotMasked : masked k → False) :
    MaskedTagsAbsentFromTrueTagEnv masked
      { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } := by
  intro k' deps' hmasked hget
  by_cases hkk' : k' = k
  · subst hkk'
    exact hnotMasked hmasked
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : ctx.tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact habsent k' deps' hmasked hget'

lemma tagEnvConsistentWithRegimeMasked_insert_false
    (k : Tag) (deps : Deps)
    (h : tagEnvConsistentWithRegimeMasked masked tagEnv R) :
    tagEnvConsistentWithRegimeMasked masked (tagEnv.insert k ⟨false, deps⟩) R := by
  intro k' deps' hget
  by_cases hkk' : k' = k
  · subst hkk'
    simp [Std.ExtTreeMap.get?_eq_getElem?] at hget
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact h k' deps' hget'

lemma MaskedTagsAbsentFromTrueTagEnv_insert_false
    {ctx : TypeContext} {k : Tag} {deps : Deps}
    (habsent : MaskedTagsAbsentFromTrueTagEnv masked ctx) :
    MaskedTagsAbsentFromTrueTagEnv masked
      { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } := by
  intro k' deps' hmasked hget
  by_cases hkk' : k' = k
  · subst hkk'
    simp [Std.ExtTreeMap.get?_eq_getElem?] at hget
  · have hcmp : compare k k' ≠ Ordering.eq := by
      intro hce
      have : k = k' := (Nat.compare_eq_eq).1 hce
      exact hkk' this.symm
    have hget' : ctx.tagEnv.get? k' = some ⟨true, deps'⟩ := by
      simp [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hcmp] at hget
      exact hget
    exact habsent k' deps' hmasked hget'

lemma invalidateRegimeDeps_preserves_true_masked
    (ls : LocSet)
    (h : tagEnvConsistentWithRegimeMasked masked tagEnv R) :
    tagEnvConsistentWithRegimeMasked masked
      (invalidateTagDeps tagEnv ls) (invalidateRegimeDeps R tagEnv ls) := by
  intro k deps hget
  have hkR_or_masked : masked k ∨ R.lookup? k = some true := by
    have hkeep : tagEnv.get? k = some ⟨true, deps⟩ := by
      unfold invalidateTagDeps at hget
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
      cases h0 : tagEnv.get? k
      · rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
        simp at hget
      · rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
        simp at hget
        rw [hget.1]
    exact h k deps hkeep
  cases hkR_or_masked with
  | inl hmasked =>
      exact Or.inl hmasked
  | inr hkR =>
      right
      unfold invalidateRegimeDeps
      dsimp [Regime.lookup?] at hkR
      dsimp only [invalidateTagDeps]
      have hcontains : (invalidateTagDeps tagEnv ls).contains k = true := by
        simp only [Std.ExtTreeMap.contains_eq_isSome_getElem?]
        rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]
        rfl
      have hmap :
          (R.filter (fun k _ => (invalidateTagDeps tagEnv ls).contains k)).get? k = some true := by
        simp [Std.ExtTreeMap.get?_eq_getElem?, hcontains, hkR]
      simp [Regime.lookup?]
      exact ⟨hkR, hcontains⟩

lemma MaskedTagsAbsentFromTrueTagEnv_invalidateTagDeps
    {ctx : TypeContext} {ls : LocSet}
    (habsent : MaskedTagsAbsentFromTrueTagEnv masked ctx) :
    MaskedTagsAbsentFromTrueTagEnv masked
      { ctx with tagEnv := invalidateTagDeps ctx.tagEnv ls } := by
  intro k deps hmasked hget
  have hkeep : ctx.tagEnv.get? k = some ⟨true, deps⟩ := by
    unfold invalidateTagDeps at hget
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter'] at hget
    cases h0 : ctx.tagEnv.get? k
    · rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
      simp at hget
    · rw [← Std.ExtTreeMap.get?_eq_getElem?, h0] at hget
      simp at hget
      rw [hget.1]
  exact habsent k deps hmasked hkeep

end TagEnvConsistentWithRegimeMasked

-- Join of TagEnvs/Regimes preserves the invariant (meet-style join: only agreed tags remain).
lemma tagEnvConsistentWithRegime_join
    (tagEnv₁ tagEnv₂ : TagEnv) (R₁ R₂ : Regime)
    (h₁ : tagEnvConsistentWithRegime tagEnv₁ R₁)
    (h₂ : tagEnvConsistentWithRegime tagEnv₂ R₂) :
    tagEnvConsistentWithRegime (joinTagEnvs tagEnv₁ tagEnv₂) (joinRegimes R₁ R₂) := by
  intro k deps hget
  -- Use helper lemma to extract that both inputs must have compatible entries
  have hgetTag : (joinTagEnvs tagEnv₁ tagEnv₂).get? k = some ⟨true, deps⟩ := hget
  unfold joinTagEnvs at hgetTag
  -- Determine if k is in the combined keys
  let f : Tag → Option TagVal → Option TagVal → Option TagVal := fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ => if b1 == b2 then some ⟨b1, LocSet.union deps1 deps2⟩ else none
    | some _, none => none
    | none, some _ => none
    | none, none => none
  have hcombine : (combineExtTreeMaps tagEnv₁ tagEnv₂ f).get? k = some ⟨true, deps⟩ := hgetTag
  simp only [combineExtTreeMaps] at hcombine
  -- k must be in the key list for the result to be some
  have hk_mem : k ∈ (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups := by
    by_contra hnot
    have := combineExtTreeMaps_go_get_not_mem tagEnv₁ tagEnv₂ f
            (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hnot
    simp [this] at hcombine
  -- Use the mem lemma to get the join function result
  have hgo := combineExtTreeMaps_go_get_mem tagEnv₁ tagEnv₂ f
              (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hk_mem
  simp only [Std.ExtTreeMap.get?_eq_getElem?] at hcombine hgo
  rw [hcombine] at hgo
  -- Analyze what f k must return - need to simplify hgo to extract the constraint
  simp only [f] at hgo
  -- Do case analysis on both get? results
  cases h1 : tagEnv₁.get? k <;> cases h2 : tagEnv₂.get? k
  · -- both none - contradiction with hgo
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- tagEnv₁ none, tagEnv₂ some - contradiction
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- tagEnv₁ some, tagEnv₂ none - contradiction
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · -- both some - this is the only valid case
    rename_i val1 val2
    rcases val1 with ⟨b1, deps1⟩
    rcases val2 with ⟨b2, deps2⟩
    simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
    split_ifs at hgo with heq
    · -- Case: b1 == b2
      have heq' : b1 = b2 := by
        cases b1 <;> cases b2 <;> simp at heq <;> trivial
      simp at hgo
      -- hgo: b1 = true ∧ deps = deps1.union deps2
      have hb1 := hgo.1
      subst hb1 heq'
      -- Use the premises to get `R₁.lookup? k = some true` and `R₂.lookup? k = some true`.
      have hkR1 : R₁.lookup? k = some true := h₁ k deps1 h1
      have hkR2 : R₂.lookup? k = some true := h₂ k deps2 h2
      -- Now compute `joinRegimes R₁ R₂`.lookup? k.
      unfold joinRegimes
      -- Extract the underlying map lookups (lookup? is just R.get? k).
      have hkmap1 : R₁.get? k = some true := by
        dsimp [Regime.lookup?] at hkR1
        exact hkR1
      have hkmap2 : R₂.get? k = some true := by
        dsimp [Regime.lookup?] at hkR2
        exact hkR2
      -- Show the joined map contains `k ↦ true`.
      -- Use the same approach as for TagEnv
      have hkjoined : (combineExtTreeMaps R₁ R₂ (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 == b2 then some b1 else none
        | _, _ => none)).get? k = some true := by
        simp only [combineExtTreeMaps]
        have hk_mem_regime : k ∈ (R₁.keys ++ R₂.keys).eraseDups := by
          have hk_contains : R₁.contains k := by
            rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, ← Std.ExtTreeMap.get?_eq_getElem?, hkmap1]
            rfl
          have hk_in_keys : k ∈ R₁.keys := ExtTreeMap.mem_keys.2 hk_contains
          have hmem_append : k ∈ R₁.keys ++ R₂.keys := List.mem_append_left R₂.keys hk_in_keys
          exact List.mem_eraseDups_of_mem hmem_append
        have hgo_regime := combineExtTreeMaps_go_get_mem R₁ R₂
                           (fun _ ob1 ob2 => match ob1, ob2 with
                             | some b1, some b2 => if b1 == b2 then some b1 else none
                             | _, _ => none)
                           (R₁.keys ++ R₂.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hk_mem_regime
        -- hgo_regime: (combineExtTreeMaps.go ...)[k]? = match f k (R₁[k]?) (R₂[k]?) with ...
        -- We know R₁.get? k = some true and R₂.get? k = some true
        -- So f k (some true) (some true) = if (true == true) then some true else none = some true
        simp only [← Std.ExtTreeMap.get?_eq_getElem?, hkmap1, hkmap2] at hgo_regime
        -- Now the match simplifies: true == true = true, so we get some true
        simp only [beq_self_eq_true, ↓reduceIte] at hgo_regime
        -- Convert .get? to [k]? in the goal and use hgo_regime
        rw [Std.ExtTreeMap.get?_eq_getElem?]
        exact hgo_regime
      -- Finish the lookup.
      simp only [Regime.lookup?, Std.ExtTreeMap.get?_eq_getElem?]
      rw [← Std.ExtTreeMap.get?_eq_getElem?]
      exact hkjoined

private lemma joinTagEnvs_lookup_true_elim
    (tagEnv₁ tagEnv₂ : TagEnv) (k : Tag) (deps : Deps)
    (hget : (joinTagEnvs tagEnv₁ tagEnv₂).get? k = some ⟨true, deps⟩) :
    ∃ deps₁ deps₂,
      tagEnv₁.get? k = some ⟨true, deps₁⟩ ∧
      tagEnv₂.get? k = some ⟨true, deps₂⟩ := by
  unfold joinTagEnvs at hget
  let f : Tag → Option TagVal → Option TagVal → Option TagVal := fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
        if b1 == b2 then some ⟨b1, LocSet.union deps1 deps2⟩ else none
    | some _, none => none
    | none, some _ => none
    | none, none => none
  have hcombine : (combineExtTreeMaps tagEnv₁ tagEnv₂ f).get? k = some ⟨true, deps⟩ := hget
  simp only [combineExtTreeMaps] at hcombine
  have hk_mem : k ∈ (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups := by
    by_contra hnot
    have := combineExtTreeMaps_go_get_not_mem tagEnv₁ tagEnv₂ f
      (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hnot
    simp [this] at hcombine
  have hgo := combineExtTreeMaps_go_get_mem tagEnv₁ tagEnv₂ f
    (tagEnv₁.keys ++ tagEnv₂.keys).eraseDups ({} : TagEnv) k hk_mem
  simp only [Std.ExtTreeMap.get?_eq_getElem?] at hcombine hgo
  rw [hcombine] at hgo
  simp only [f] at hgo
  cases h1 : tagEnv₁.get? k <;> cases h2 : tagEnv₂.get? k
  · simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · simp [← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · rename_i val1 val2
    rcases val1 with ⟨b1, deps1⟩
    rcases val2 with ⟨b2, deps2⟩
    cases hb1 : b1 with
    | false =>
        cases hb2 : b2 with
        | false =>
            simp [hb1, hb2, ← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
        | true =>
            simp [hb1, hb2, ← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
    | true =>
        cases hb2 : b2 with
        | false =>
            simp [hb1, hb2, ← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
        | true =>
            simp [hb1, hb2, ← Std.ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
            subst hb1 hb2
            refine ⟨deps1, deps2, ?_, ?_⟩
            · rfl
            · rfl

private lemma joinRegimes_lookup_true_of_both_true
    (R₁ R₂ : Regime) (k : Tag)
    (hkR1 : R₁.lookup? k = some true)
    (hkR2 : R₂.lookup? k = some true) :
    (joinRegimes R₁ R₂).lookup? k = some true := by
  -- Extract the underlying map lookups (lookup? is just R.get? k).
  have hkmap1 : R₁.get? k = some true := by
    dsimp [Regime.lookup?] at hkR1
    exact hkR1
  have hkmap2 : R₂.get? k = some true := by
    dsimp [Regime.lookup?] at hkR2
    exact hkR2
  have hkjoined :
      (combineExtTreeMaps R₁ R₂
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 = b2 then some b1 else none
          | _, _ => none)).get? k = some true := by
    simp only [combineExtTreeMaps]
    have hk_mem_regime : k ∈ (R₁.keys ++ R₂.keys).eraseDups := by
      have hk_contains : R₁.contains k := by
        rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, ← Std.ExtTreeMap.get?_eq_getElem?, hkmap1]
        rfl
      have hk_in_keys : k ∈ R₁.keys := ExtTreeMap.mem_keys.2 hk_contains
      exact List.mem_eraseDups_of_mem (List.mem_append_left R₂.keys hk_in_keys)
    have hgo_regime := combineExtTreeMaps_go_get_mem R₁ R₂
      (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 = b2 then some b1 else none
        | _, _ => none)
      (R₁.keys ++ R₂.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hk_mem_regime
    simp only [← Std.ExtTreeMap.get?_eq_getElem?, hkmap1, hkmap2] at hgo_regime
    simp only [↓reduceIte] at hgo_regime
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hgo_regime
  simpa [Regime.lookup?, joinRegimes] using hkjoined

lemma tagEnvConsistentWithRegimeMasked_join
    (masked : Tag → Prop)
    (tagEnv₁ tagEnv₂ : TagEnv) (R₁ R₂ : Regime)
    (h₁ : tagEnvConsistentWithRegimeMasked masked tagEnv₁ R₁)
    (h₂ : tagEnvConsistentWithRegimeMasked masked tagEnv₂ R₂) :
    tagEnvConsistentWithRegimeMasked masked (joinTagEnvs tagEnv₁ tagEnv₂) (joinRegimes R₁ R₂) := by
  intro k deps hget
  rcases joinTagEnvs_lookup_true_elim tagEnv₁ tagEnv₂ k deps hget with
    ⟨deps₁, deps₂, hget₁, hget₂⟩
  have h₁_lookup := h₁ k deps₁ hget₁
  have h₂_lookup := h₂ k deps₂ hget₂
  cases h₁_lookup with
  | inl hmasked =>
      exact Or.inl hmasked
  | inr hlookup₁ =>
      cases h₂_lookup with
      | inl hmasked =>
          exact Or.inl hmasked
      | inr hlookup₂ =>
          exact Or.inr (joinRegimes_lookup_true_of_both_true R₁ R₂ k hlookup₁ hlookup₂)

lemma MaskedTagsAbsentFromTrueTagEnvs_join
    {masked : Tag → Prop} {tagEnv₁ tagEnv₂ : TagEnv}
    (h₁ : ∀ k deps, masked k → tagEnv₁.get? k = some ⟨true, deps⟩ → False)
    (_h₂ : ∀ k deps, masked k → tagEnv₂.get? k = some ⟨true, deps⟩ → False) :
    ∀ k deps, masked k →
      (joinTagEnvs tagEnv₁ tagEnv₂).get? k = some ⟨true, deps⟩ → False := by
  intro k deps hmasked hget
  rcases joinTagEnvs_lookup_true_elim tagEnv₁ tagEnv₂ k deps hget with
    ⟨deps₁, _deps₂, hget₁, _hget₂⟩
  exact h₁ k deps₁ hmasked hget₁

lemma masked_lookup_none_of_monotoneStep
    {masked : Tag → Prop} {R R' : Regime}
    (hmasked_none : ∀ k, masked k → R.lookup? k = none)
    (h_mono : Regime.monotoneStep R R') :
    ∀ k, masked k → R'.lookup? k = none := by
  intro k hk
  by_contra hnot
  exact h_mono.2 k hnot (hmasked_none k hk)

/-- Extended-regime version of `masked_lookup_none_of_monotoneStep` (doc/extern-regime.md
    §4.4, Q5): masked tags stay absent from the regime across a `monotoneStepExt` step,
    provided masked tags are never among the freshly-added `newTags`.  At every use site the
    discharge is `masked k → k < ctx.nextTag` while `newTags = fun k => ctx.nextTag ≤ k`. -/
lemma masked_lookup_none_of_monotoneStepExt
    {masked : Tag → Prop} {R R' : Regime} {newTags : Tag → Prop}
    (hmasked_none : ∀ k, masked k → R.lookup? k = none)
    (hmasked_fresh : ∀ k, masked k → ¬ newTags k)
    (h_mono : Regime.monotoneStepExt R R' newTags) :
    ∀ k, masked k → R'.lookup? k = none := by
  intro k hk
  by_contra hnot
  rcases h_mono.2 k hnot with hRne | hnew
  · exact hRne (hmasked_none k hk)
  · exact hmasked_fresh k hk hnew
