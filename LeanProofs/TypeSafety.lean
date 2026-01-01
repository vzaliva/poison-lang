-- Common type safety definitions for the Poison Language
--
-- This file contains shared definitions used by both Progress and Preservation
-- properties, including evaluation relations and runtime context instantiation.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import Std.Data.ExtTreeSet.Lemmas
import Std.Data.ExtTreeMap

open Std

-- ================================================================
-- combineExtTreeMaps helpers
-- ================================================================

theorem list_removeAll_self [BEq α] [LawfulBEq α] (l : List α) : l.removeAll l = [] := by
  simp [List.removeAll, List.filter_eq_nil_iff]

theorem list_eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
  l.eraseDups = l := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have h' : as.Nodup := (List.nodup_cons.mp h).2
      have ha_not : a ∉ as := (List.nodup_cons.mp h).1
      have hfilter : as.filter (fun b => !b == a) = as := by
        apply (List.filter_eq_self).2
        intro b hb
        have hbne : b ≠ a := by
          intro hba
          apply ha_not
          simpa [hba] using hb
        simp [hbne]
      simp [List.eraseDups_cons, hfilter, ih h']

theorem combineExtTreeMaps_go_get_not_mem
  (m1 m2 : ExtTreeMap Nat β)
  (f : Nat → Option β → Option β → Option β)
  (ks : List Nat) (acc : ExtTreeMap Nat β) (k : Nat)
  (h_not : k ∉ ks) :
  (combineExtTreeMaps.go m1 m2 f ks acc)[k]? = acc[k]? := by
  classical
  induction ks generalizing acc with
  | nil =>
      simp [combineExtTreeMaps.go]
  | cons x xs ih =>
      have hk_ne : k ≠ x := by
        intro h
        apply h_not
        simp [h]
      have h_not_xs : k ∉ xs := by
        intro hmem
        apply h_not
        simp [hmem]
      cases hfx : f x (m1.get? x) (m2.get? x) with
      | none =>
          have hfx' : f x m1[x]? m2[x]? = none := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hfx
          have ih' := ih (acc.erase x) h_not_xs
          have hcmp : compare x k ≠ Ordering.eq := by
            intro hcmp
            have : x = k := (Nat.compare_eq_eq).1 hcmp
            exact hk_ne this.symm
          have hstep :
              (combineExtTreeMaps.go m1 m2 f (x :: xs) acc)[k]? =
                (combineExtTreeMaps.go m1 m2 f xs (acc.erase x))[k]? := by
            simp [combineExtTreeMaps.go, hfx']
          rw [hstep, ih']
          simp [ExtTreeMap.getElem?_erase, hcmp]
      | some v =>
          have hfx' : f x m1[x]? m2[x]? = some v := by
            simpa [ExtTreeMap.get?_eq_getElem?] using hfx
          have ih' := ih (acc.insert x v) h_not_xs
          have hcmp : compare x k ≠ Ordering.eq := by
            intro hcmp
            have : x = k := (Nat.compare_eq_eq).1 hcmp
            exact hk_ne this.symm
          have hstep :
              (combineExtTreeMaps.go m1 m2 f (x :: xs) acc)[k]? =
                (combineExtTreeMaps.go m1 m2 f xs (acc.insert x v))[k]? := by
            simp [combineExtTreeMaps.go, hfx']
          rw [hstep, ih']
          simp [ExtTreeMap.getElem?_insert, hcmp]

theorem combineExtTreeMaps_go_get_mem
  (m1 m2 : ExtTreeMap Nat β)
  (f : Nat → Option β → Option β → Option β)
  (ks : List Nat) (acc : ExtTreeMap Nat β) (k : Nat)
  (h_in : k ∈ ks) :
  (combineExtTreeMaps.go m1 m2 f ks acc)[k]? =
    match f k (m1.get? k) (m2.get? k) with
    | some v => some v
    | none => none := by
  classical
  induction ks generalizing acc with
  | nil =>
      cases h_in
  | cons x xs ih =>
      cases h_in with
      | head =>
          cases hfx : f k (m1.get? k) (m2.get? k) with
          | none =>
              have hfx' : f k m1[k]? m2[k]? = none := by
                simpa [ExtTreeMap.get?_eq_getElem?] using hfx
              by_cases hmem : k ∈ xs
              · have ih' := ih (acc.erase k) hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.erase k))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep]
                have ih'' := ih'
                rw [hfx] at ih''
                exact ih''
              · have ih' := combineExtTreeMaps_go_get_not_mem m1 m2 f xs (acc.erase k) k hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.erase k))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep, ih']
                simp
          | some v =>
              have hfx' : f k m1[k]? m2[k]? = some v := by
                simpa [ExtTreeMap.get?_eq_getElem?] using hfx
              by_cases hmem : k ∈ xs
              · have ih' := ih (acc.insert k v) hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.insert k v))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep]
                have ih'' := ih'
                rw [hfx] at ih''
                exact ih''
              · have ih' := combineExtTreeMaps_go_get_not_mem m1 m2 f xs (acc.insert k v) k hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.insert k v))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep, ih']
                simp
      | tail =>
          rename_i hmem
          cases hfx : f x (m1.get? x) (m2.get? x) with
          | none =>
              have hfx' : f x m1[x]? m2[x]? = none := by
                simpa [ExtTreeMap.get?_eq_getElem?] using hfx
              have ih' := ih (acc.erase x) hmem
              have hstep :
                  (combineExtTreeMaps.go m1 m2 f (x :: xs) acc)[k]? =
                    (combineExtTreeMaps.go m1 m2 f xs (acc.erase x))[k]? := by
                simp [combineExtTreeMaps.go, hfx']
              rw [hstep]
              exact ih'
          | some v =>
              have hfx' : f x m1[x]? m2[x]? = some v := by
                simpa [ExtTreeMap.get?_eq_getElem?] using hfx
              have ih' := ih (acc.insert x v) hmem
              have hstep :
                  (combineExtTreeMaps.go m1 m2 f (x :: xs) acc)[k]? =
                    (combineExtTreeMaps.go m1 m2 f xs (acc.insert x v))[k]? := by
                simp [combineExtTreeMaps.go, hfx']
              rw [hstep]
              exact ih'

theorem locSet_union_idempotent (s : LocSet) : LocSet.union s s = s := by
  classical
  ext k
  simp [LocSet.union, Std.ExtTreeSet.mem_union_iff]

theorem joinTagEnvs_func_idempotent :
  ∀ (k : Tag) (otv : Option TagVal),
    (fun _ otv1 otv2 =>
      match otv1, otv2 with
      | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
        if b1 == b2 then
          some ⟨b1, LocSet.union deps1 deps2⟩
        else
          none
      | some _, none => none
      | none, some _ => none
      | none, none => none) k otv otv = otv := by
  intro k otv
  cases otv with
  | none => rfl
  | some tv =>
      cases tv with
      | mk b deps =>
          cases b <;> simp [locSet_union_idempotent]

theorem joinTagEnvs_idempotent (t : TagEnv) : joinTagEnvs t t = t := by
  classical
  let f : Tag → Option TagVal → Option TagVal → Option TagVal := fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
      if b1 == b2 then
        some ⟨b1, LocSet.union deps1 deps2⟩
      else
        none
    | some _, none => none
    | none, some _ => none
    | none, none => none
  have hcombine : combineExtTreeMaps t t f = t := by
    have hkeys_nodup : t.keys.Nodup := ExtTreeMap.nodup_keys (t := t)
    have hkeys_erase : t.keys.eraseDups = t.keys :=
      list_eraseDups_eq_self_of_nodup (h := hkeys_nodup)
    have hks : (t.keys ++ t.keys).eraseDups = t.keys := by
      simp [List.eraseDups_append, list_removeAll_self, hkeys_erase]
    apply ExtTreeMap.ext_getElem?
    intro k
    dsimp [combineExtTreeMaps]
    rw [hks]
    by_cases hmem : k ∈ t.keys
    · have hgo := combineExtTreeMaps_go_get_mem t t f t.keys ({} : TagEnv) k hmem
      have hfun : f k (t[k]?) (t[k]?) = t[k]? := by
        simpa [f] using (joinTagEnvs_func_idempotent k (t[k]?))
      have hgo' := hgo
      simp [hfun] at hgo'
      cases h : t[k]? <;> simpa [h] using hgo'
    · have hgo := combineExtTreeMaps_go_get_not_mem t t f t.keys ({} : TagEnv) k hmem
      have hnot_mem : k ∉ t := by
        intro hk
        have hk' : k ∈ t.keys := (ExtTreeMap.mem_keys).2 hk
        exact hmem hk'
      have hm_none : t[k]? = none := ExtTreeMap.getElem?_eq_none hnot_mem
      simpa [hm_none] using hgo
  simpa [joinTagEnvs, f] using hcombine

theorem Except.bind_eq_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β)
    (h : Except.bind x f = Except.ok b) :
    ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e =>
    simp [Except.bind] at h
  | ok a =>
    refine ⟨a, rfl, ?_⟩
    simpa [Except.bind] using h

-- ================================================================
-- Realisation Maps and Value Typing
-- ================================================================

-- Proof-level realisation map from logical locations to concrete runtime addresses.
-- This is a proof artefact used to relate the logical locations in types to a
-- particular execution's heap layout (Issue #76).
abbrev RealizationMap := ExtTreeMap Loc Address

namespace RealizationMap

  @[inline] def lookup (m : RealizationMap) (l : Loc) : Option Address :=
    m.get? l

  @[inline] def update (m : RealizationMap) (l : Loc) (a : Address) : RealizationMap :=
    m.insert l a

  /-- `m` contains a binding for `l`. -/
  def hasKey (m : RealizationMap) (l : Loc) : Prop :=
    m.contains l

  /-- `θ₁` extends `θ₀` if it agrees on all realised locations of `θ₀`. -/
  def extendsMap (θ₀ θ₁ : RealizationMap) : Prop :=
    ∀ l a, θ₀.lookup l = some a → θ₁.lookup l = some a

  /-- `θ` is injective: distinct logical locations map to distinct addresses. -/
  def isInjective (θ : RealizationMap) : Prop :=
    ∀ l₁ l₂ a, θ.lookup l₁ = some a → θ.lookup l₂ = some a → l₁ = l₂

  instance : BEq RealizationMap where
    beq m₁ m₂ := (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

  instance : Repr RealizationMap where
    reprPrec m _ := s!"ofList {repr (ExtTreeMap.toList m)}"

end RealizationMap

/-- A realisation map is well-formed if it is injective.
    This predicate can be extended with additional conditions as needed (Issue #76). -/
def wfRealizationMap (θ : RealizationMap) : Prop :=
  θ.isInjective

/-- θ₁ is a well-formed extension of θ₀: it agrees on existing locations
    and preserves injectivity (if θ₀ is injective, so is θ₁).
    This captures that extending a realisation map during evaluation
    preserves well-formedness (Issue #76). -/
def wfExtendsMap (θ₀ θ₁ : RealizationMap) : Prop :=
  θ₀.extendsMap θ₁ ∧ (wfRealizationMap θ₀ → wfRealizationMap θ₁)

-- Proof-level typing relation for runtime values.
--
-- For `ref` types, the concrete address must be the realisation (via `θ`) of some
-- logical location in the `LocSet` annotation (Issue #76).
inductive valueHasETyp (θ : RealizationMap) : Value → ETyp → Prop where
  | num (n): valueHasETyp θ (Value.num n) ETyp.int
  | bool (b): valueHasETyp θ (Value.bool b) ETyp.bool
  | unit : valueHasETyp θ Value.unit ETyp.unit
  | str (s): valueHasETyp θ (Value.str s) ETyp.string
  | loc {a : Address} {t : ETyp} {ls : LocSet} {l : Loc}
      (hlookup : θ.lookup l = some a)
      (hin : l ∈ ls) :
      valueHasETyp θ (Value.loc a) (ETyp.ref t ls)
  | closure (x e env st1 st2 p tcl):
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure (x pe env st1 st2 p tcl):
      valueHasETyp θ (Value.peClosure x pe env) (ETyp.parrow st1 st2 p tcl)

-- ================================================================
-- Runtime Context Instantiation
-- ================================================================

-- A predicate for runtime instantiating the context: values must exist for
-- every typed variable and memory must contain entries for each typed
-- location.
--
-- Note on memory type matching (Issue #76): The proposal requires that heap
-- cells have qualified types matching Γ(l). This is implicitly satisfied because:
-- (1) Memory only stores integers (Memory := HashMap Address Int)
-- (2) Well-typed programs only store values of type int in memory
-- (3) Therefore, for any l ∈ dom(Γ) with θ(l) = a, the value μ(a) : Int
--     matches the stored type Γ(l).etyp which must be ETyp.int.
def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l a, θ.lookup l = some a → ctx.memEnv.contains l ∧ μ.contains a) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt →
     ∃ v, ρ.lookup x = some v ∧ valueHasETyp θ v qt.etyp)

-- ================================================================
-- Helper Lemmas
-- ================================================================

-- Helper lemma: if a variable is in the typing context and runtime instantiates the context,
-- then the variable lookup returns a value with the correct enriched type
lemma var_has_correct_type (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (x : Name) (qt : QTyp) :
  wfRealizationMap θ →
  runtimeInstantiatesCtx ctx μ ρ θ →
  ctx.varEnv.lookup x = some qt →
  ∃ v, ρ.lookup x = some v ∧ valueHasETyp θ v qt.etyp := by
  intro _h_wf ⟨_, h_vars⟩ h_lookup
  obtain ⟨v, h_v, h_typ⟩ := h_vars h_lookup
  exact ⟨v, h_v, h_typ⟩

-- ================================================================
-- LocSet foldM Helper Lemmas
-- ================================================================

-- Helper lemma: LocSet.foldM preserves a property P on the accumulator
-- when the fold function preserves P and only reads from environments
-- This is useful for proving that foldM doesn't modify environments
--
-- The lemma states: if foldM succeeds and the function preserves P,
-- then the result satisfies P
-- Helper lemma: List.foldlM over Except preserves P when all list elements satisfy a side condition Q
theorem List.foldlM_Except_preserves_property_of_forall_mem
    (xs : List α) (init : β) (f : β → α → Except ε β)
    (P : β → Prop) (Q : α → Prop)
    (h_init : P init)
    (h_all : ∀ x ∈ xs, Q x)
    (h_step : ∀ (acc : β) (x : α), P acc → Q x → (∀ (acc' : β), f acc x = Except.ok acc' → P acc')) :
    ∀ (result : β), List.foldlM f init xs = Except.ok result → P result := by
  induction xs generalizing init with
  | nil =>
    intro result h_fold
    simp [List.foldlM_nil, pure, Except.pure] at h_fold
    subst h_fold
    exact h_init
  | cons x xs ih =>
    intro result h_fold
    simp [List.foldlM_cons, bind, Except.bind] at h_fold
    cases h_fx : f init x with
    | error e =>
      simp [h_fx] at h_fold
    | ok acc' =>
      simp [h_fx] at h_fold
      have hQx : Q x := h_all x (by simp)
      have hPacc' : P acc' := h_step init x h_init hQx acc' h_fx
      have h_all_tail : ∀ y ∈ xs, Q y := by
        intro y hy
        exact h_all y (by simp [hy])
      exact ih acc' hPacc' h_all_tail result h_fold

-- Helper lemma: List.foldlM over Except preserves property P
theorem List.foldlM_Except_preserves_property
    (xs : List α) (init : β) (f : β → α → Except ε β)
    (P : β → Prop)
    (h_init : P init)
    (h_preserve : ∀ (acc : β) (x : α), P acc → (∀ (acc' : β), f acc x = Except.ok acc' → P acc')) :
    ∀ (result : β), List.foldlM f init xs = Except.ok result → P result := by
  intro result h_fold
  refine List.foldlM_Except_preserves_property_of_forall_mem xs init f P (fun _ => True)
    h_init (fun x _ => trivial) (fun acc x hP _ => h_preserve acc x hP) result h_fold

theorem LocSet.foldM_Except_preserves_property
    (s : LocSet) (init : β) (f : β → Loc → Except ε β)
    (P : β → Prop)
    (h_init : P init)
    (h_preserve : ∀ (acc : β) (l : Loc), P acc → (∀ (acc' : β), f acc l = Except.ok acc' → P acc')) :
    ∀ (result : β), LocSet.foldM s init f = Except.ok result → P result := by
  intro result h_fold
  -- Convert LocSet.foldM to ExtTreeSet.foldlM
  have h_eq : LocSet.foldM s init f = ExtTreeSet.foldlM (f := fun acc l => f acc l) (init := init) s := rfl
  rw [h_eq] at h_fold
  -- Use foldlM_eq_foldlM_toList to convert to list fold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at h_fold
  -- Apply the list lemma
  exact List.foldlM_Except_preserves_property s.toList init f P h_init h_preserve result h_fold

-- Helper lemma: List.mapM preserves a property on all elements
theorem List.mapM_Except_preserves_property
    (xs : List α) (f : α → Except ε β)
    (P : β → Prop)
    (h_preserve : ∀ (x : α) (y : β), f x = Except.ok y → P y) :
    ∀ (results : List β), List.mapM f xs = Except.ok results → ∀ y ∈ results, P y := by
  induction xs with
  | nil =>
    intro results h_map
    simp [List.mapM_nil, pure, Except.pure] at h_map
    cases h_map
    intro y h_mem
    cases h_mem
  | cons x xs ih =>
    intro results h_map
    simp [List.mapM_cons, bind, Except.bind] at h_map
    cases h_fx : f x with
    | error e =>
      simp [h_fx] at h_map
    | ok y_val =>
      simp [h_fx] at h_map
      cases h_map_results : List.mapM f xs with
      | error e =>
        simp [h_map_results] at h_map
      | ok rest_results =>
        simp [h_map_results] at h_map
        -- h_map : Except.ok (y_val :: rest_results) = Except.ok results
        injection h_map with h_list_eq
        -- h_list_eq : y_val :: rest_results = results
        subst h_list_eq
        intro z h_mem
        simp [List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          -- h_eq : z = y_val
          subst h_eq
          -- Now z = y_val, so h_fx : f x = Except.ok y_val becomes f x = Except.ok z
          have h_fx_z : f x = Except.ok z := h_fx
          exact h_preserve x z h_fx_z
        | inr h_mem_rest =>
          exact ih rest_results h_map_results z h_mem_rest

-- ================================================================
-- TypeContext Well-formedness
-- ================================================================

/-- A TypeContext is well-formed if all locations in memEnv are below nextLoc.
    This captures that nextLoc is the "high-water mark" for allocated logical locations. -/
def wfTypeContext (ctx : TypeContext) : Prop :=
  ∀ l, ctx.memEnv.contains l → l < ctx.nextLoc

/-- The typing result is well-formed if all locations in memEnv' are below nextLoc'. -/
def wfTypeResult (res : TypeResult) : Prop :=
  ∀ l, res.memEnv'.contains l → l < res.nextLoc'

/-- Post-context derived from typing result. -/
def ctxAfter (ctx : TypeContext) (res : TypeResult) : TypeContext :=
  { ctx with memEnv := res.memEnv', tagEnv := res.tagEnv', nextLoc := res.nextLoc', nextTag := res.nextTag' }

/-- wfTypeResult implies wfTypeContext for the post-context. -/
lemma wfTypeContext_of_wfTypeResult (ctx : TypeContext) (res : TypeResult) :
    wfTypeResult res → wfTypeContext (ctxAfter ctx res) := by
  intro hwf l hcontains
  simp only [ctxAfter] at hcontains ⊢
  exact hwf l hcontains

/-- A location at or above ctx.nextLoc is not realized in θ if runtimeInstantiatesCtx holds. -/
lemma freshLoc_not_realized (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (l : Loc) :
    wfTypeContext ctx →
    runtimeInstantiatesCtx ctx μ ρ θ →
    l ≥ ctx.nextLoc →
    θ.lookup l = none := by
  intro hwf hric hge
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have ⟨hmem, _⟩ := hric.1 l a ha
  have hlt := hwf l hmem
  exact Nat.lt_irrefl l (Nat.lt_of_lt_of_le hlt hge)
