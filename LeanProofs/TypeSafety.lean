-- Common type safety definitions for the Poison Language
--
-- This file contains shared definitions used by both Progress and Preservation
-- properties, including evaluation relations and runtime context instantiation.

import LeanPoison.Syntax
import LeanProofs.Equality
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Properties
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
  unfold LocSet.foldM at h_fold
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


-- ================================================================
-- Typechecker structure lemmas
-- ================================================================

section typecheck_structure_lemmas

-- Structure lemma for printInt typechecking.
lemma typecheckPrintInt_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintInt ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckPrintInt at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckPrintInt at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          match h_qt : result1.qualType with
          | QTyp.mk etyp poison pred =>
              rw [h_qt] at h_typecheck
              cases h_b : (etyp != ETyp.int) with
              | true =>
                  -- Convert boolean inequality to propositional inequality
                  have h_neq : etyp ≠ ETyp.int := by
                    intro h_eq
                    subst h_eq
                    simp [bne] at h_b
                  have h_typecheck' := h_typecheck
                  simp at h_typecheck'
                  rw [if_neg h_neq] at h_typecheck'
                  simp [throwThe, throw] at h_typecheck'
              | false =>
                  -- Convert boolean equality to propositional equality
                  have h_eq : etyp = ETyp.int := by
                    have : (etyp == ETyp.int) = true := by
                      simp only [bne, Bool.not_eq_false'] at h_b
                      exact h_b
                    exact eq_of_beq this
                  have h_typecheck' := h_typecheck
                  simp only at h_typecheck'
                  rw [if_pos h_eq] at h_typecheck'
                  simp [pure, Except.pure] at h_typecheck'
                  have h_res :
                      { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                        memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                        nextTag' := result1.nextTag' } = res := by
                    cases h_typecheck'
                    rfl
                  refine ⟨result1, h_tc1, ?_⟩
                  rw [← h_res]
                  simp
      | error _msg =>
          simp [h_tc1] at h_typecheck

-- Structure lemma for printString typechecking.
lemma typecheckPrintString_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckPrintString ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.unit := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckPrintString at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckPrintString at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          match h_qt : result1.qualType with
          | QTyp.mk etyp poison pred =>
              rw [h_qt] at h_typecheck
              cases h_b : (etyp != ETyp.string) with
              | true =>
                  -- Convert boolean inequality to propositional inequality
                  have h_neq : etyp ≠ ETyp.string := by
                    intro h_eq
                    subst h_eq
                    simp [bne] at h_b
                  have h_typecheck' := h_typecheck
                  simp at h_typecheck'
                  rw [if_neg h_neq] at h_typecheck'
                  simp [throwThe, throw] at h_typecheck'
              | false =>
                  -- Convert boolean equality to propositional equality
                  have h_eq : etyp = ETyp.string := by
                    have : (etyp == ETyp.string) = true := by
                      simp only [bne, Bool.not_eq_false'] at h_b
                      exact h_b
                    exact eq_of_beq this
                  have h_typecheck' := h_typecheck
                  simp at h_typecheck'
                  rw [if_pos h_eq] at h_typecheck'
                  simp [pure, Except.pure] at h_typecheck'
                  have h_res :
                      { qualType := { etyp := ETyp.unit, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                        memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                        nextTag' := result1.nextTag' } = res := by
                    cases h_typecheck'
                    rfl
                  refine ⟨result1, h_tc1, ?_⟩
                  rw [← h_res]
                  simp
      | error _msg =>
          simp [h_tc1] at h_typecheck

-- Structure lemma for unary-op typechecking.
lemma typecheckUnaryOp_structure (ctx : TypeContext) (op : UnaryOp) (e1 : Expr) (fuel : Nat)
    (res : TypeResult) :
  typecheckUnaryOp ctx op e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    opUnaryEType? op result1.qualType.etyp = some result_etyp ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = result_etyp ∧
    res.qualType.poison = joinPoison ctx.pc result1.qualType.poison ∧
    res.qualType.pred = Predicate.noPred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckUnaryOp] at h_typecheck
  | succ fuel' =>
      unfold typecheckUnaryOp at h_typecheck
      simp at h_typecheck
      cases h_tc1_result : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck
          match h_qt1 : result1.qualType with
          | QTyp.mk etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              cases h_opEType_result : opUnaryEType? op etyp1 with
              | some result_etyp =>
                  simp [h_opEType_result] at h_typecheck
                  injection h_typecheck with h_res_eq
                  have h_opEType_final : opUnaryEType? op result1.qualType.etyp = some result_etyp := by
                    rw [h_qt1]
                    exact h_opEType_result
                  simp only [Nat.add_sub_cancel]
                  subst h_res_eq
                  refine ⟨result1, result_etyp, h_tc1_result, h_opEType_final, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
                  simp [h_qt1]
              | none =>
                  simp [h_opEType_result] at h_typecheck
      | error _msg =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck

-- Structure lemma for binary-op typechecking.
lemma typecheckOp_structure (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat)
    (res : TypeResult) :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ∃ (result1 result2 : TypeResult) (result_etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 (fuel - 1) = .ok result2 ∧
    opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.etyp = result_etyp ∧
    res.qualType.poison = joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison) ∧
    res.qualType.pred = Predicate.noPred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckOp] at h_typecheck
  | succ fuel' =>
      unfold typecheckOp at h_typecheck
      simp at h_typecheck
      cases h_tc1_result : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck
          match h_qt1 : result1.qualType with
          | QTyp.mk etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              cases h_tc2_result :
                (typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel') with
              | ok result2 =>
                  simp [h_tc2_result] at h_typecheck
                  match h_qt2 : result2.qualType with
                  | QTyp.mk etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      cases h_opEType_result : opEType? op etyp1 etyp2 with
                      | some result_etyp =>
                          simp [h_opEType_result] at h_typecheck
                          injection h_typecheck with h_res_eq
                          have h_opEType_final :
                              opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp := by
                            rw [h_qt1, h_qt2]
                            exact h_opEType_result
                          simp only [Nat.add_sub_cancel]
                          subst h_res_eq
                          refine ⟨result1, result2, result_etyp, h_tc1_result, h_tc2_result, h_opEType_final,
                                  rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
                          simp [h_qt1, h_qt2]
                      | none =>
                          simp [h_opEType_result] at h_typecheck
              | error _msg2 =>
                  simp [h_tc2_result] at h_typecheck
      | error _msg =>
          simp [h_tc1_result, bind, Except.bind] at h_typecheck

-- Structure lemma for seq typechecking.
-- Note: typecheckSeq simply returns result2 (the result of e2), no poison join is performed.
lemma typecheckSeq_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ∃ (result1 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = updateCtxFromResult ctx result1 ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok res := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckSeq] at h_typecheck
  | succ fuel' =>
      unfold typecheckSeq at h_typecheck
      simp only [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp only [h_tc1, pure, Except.pure] at h_typecheck
          cases h_tc2 : typecheckExpr (updateCtxFromResult ctx result1) e2 fuel' with
          | ok result2 =>
              simp only [h_tc2] at h_typecheck
              have hres : result2 = res := by injection h_typecheck
              refine ⟨result1, updateCtxFromResult ctx result1, h_tc1, rfl, ?_⟩
              simp only [Nat.succ_sub_one]
              rw [← hres]
              exact h_tc2
          | error _err =>
              simp only [h_tc2] at h_typecheck
              exact absurd h_typecheck (by simp)
      | error _err =>
          simp [h_tc1] at h_typecheck

-- Structure lemma for vlet typechecking.
lemma typecheckVlet_structure (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat)
    (res : TypeResult) :
  typecheckVlet ctx x e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = ({ ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }) ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.poison = joinPoison ctx.pc result2.qualType.poison ∧
    res.qualType.pred = result2.qualType.pred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckVlet] at h_typecheck
  | succ fuel' =>
      unfold typecheckVlet at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_tc2 :
            typecheckExpr
                { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                           tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                e2 fuel' with
          | ok result2 =>
              simp [h_tc2] at h_typecheck
              cases h_qt2 : result2.qualType with
              | mk _etyp2 p2 pred2 =>
                  rw [h_qt2] at h_typecheck
                  simp at h_typecheck
                  simp [pure, Except.pure] at h_typecheck
                  let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                  cases h_typecheck
                  refine ⟨result1, result2, ctx', ?_⟩
                  simp [ctx', h_tc1, h_tc2, h_qt2]
          | error _err =>
              simp [h_tc2] at h_typecheck
      | error _err =>
          simp [h_tc1] at h_typecheck

-- Helper lemma: extract structure from typecheckNewRef
lemma typecheckNewRef_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckNewRef ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (l : Loc) (etyp : ETyp),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    l = result1.nextLoc' ∧
    etyp = result1.qualType.etyp ∧
    res.qualType.etyp = ETyp.ref etyp (LocSet.singleton l) ∧
    res.qualType.poison = ctx.pc ∧
    res.qualType.pred = Predicate.noPred ∧
    res.memEnv' = updateMemEnv result1.memEnv' l ⟨etyp, joinPoison ctx.pc result1.qualType.poison, result1.qualType.pred⟩ ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' + 1 ∧
    res.nextTag' = result1.nextTag' := by
  intro h_typecheck
  cases fuel with
  | zero =>
    unfold typecheckNewRef at h_typecheck
    simp at h_typecheck
  | succ fuel' =>
    unfold typecheckNewRef at h_typecheck
    simp at h_typecheck
    simp [bind, Except.bind] at h_typecheck
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | ok result1 =>
      simp [h_tc1] at h_typecheck
      cases h_qt1 : result1.qualType with
      | mk etyp poison pred =>
        rw [h_qt1] at h_typecheck
        simp at h_typecheck
        -- Extract freshTLocRes result
        -- freshTLocRes result1 = (result1.nextLoc', { result1 with nextLoc' := result1.nextLoc' + 1 })
        have h_fresh : (result1.nextLoc', { result1 with nextLoc' := result1.nextLoc' + 1 }) = freshTLocRes result1 := rfl
        -- Simplify the do notation
        simp [pure, Except.pure] at h_typecheck
        -- Extract projections from h_fresh to rewrite freshTLocRes in h_typecheck
        have h_fresh1 : (freshTLocRes result1).1 = result1.nextLoc' := by
          simp [← h_fresh]
        have h_fresh2 : (freshTLocRes result1).2 = { result1 with nextLoc' := result1.nextLoc' + 1 } := by
          simp [← h_fresh]
        rw [h_fresh1, h_fresh2] at h_typecheck
        simp at h_typecheck
        -- Now h_typecheck is a record equality: {...} = res
        -- Extract field equalities by projecting from the record equality
        have h_qualType : res.qualType = ⟨ETyp.ref etyp (LocSet.singleton result1.nextLoc'), ctx.pc, Predicate.noPred⟩ := by
          have := congrArg TypeResult.qualType h_typecheck
          simp at this
          exact this.symm
        have h_memEnv : res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ⟨etyp, joinPoison ctx.pc poison, pred⟩ := by
          have := congrArg TypeResult.memEnv' h_typecheck
          simp at this
          exact this.symm
        have h_tagEnv : res.tagEnv' = result1.tagEnv' := by
          have := congrArg TypeResult.tagEnv' h_typecheck
          simp at this
          exact this.symm
        have h_nextLoc : res.nextLoc' = result1.nextLoc' + 1 := by
          have := congrArg TypeResult.nextLoc' h_typecheck
          simp at this
          exact this.symm
        have h_nextTag : res.nextTag' = result1.nextTag' := by
          have := congrArg TypeResult.nextTag' h_typecheck
          simp at this
          exact this.symm
        -- Extract qualType field equalities (QTyp is a structure, so we use congrArg)
        have h_etyp : res.qualType.etyp = ETyp.ref etyp (LocSet.singleton result1.nextLoc') := by
          have := congrArg QTyp.etyp h_qualType
          simp at this
          exact this
        have h_poison_eq : res.qualType.poison = ctx.pc := by
          have := congrArg QTyp.poison h_qualType
          simp at this
          exact this
        have h_pred_eq : res.qualType.pred = Predicate.noPred := by
          have := congrArg QTyp.pred h_qualType
          simp at this
          exact this
        -- Now we have all the field equalities
        -- Construct the existential
        simp only [Nat.add_sub_cancel]
        use result1, result1.nextLoc', etyp
        constructor
        · exact h_tc1
        constructor
        · rfl  -- l = result1.nextLoc'
        constructor
        · -- etyp = result1.qualType.etyp
          simp [h_qt1]
        constructor
        · -- res.qualType.etyp = ETyp.ref etyp (LocSet.singleton l)
          rw [h_etyp]
        constructor
        · -- res.qualType.poison = ctx.pc
          rw [h_poison_eq]
        constructor
        · -- res.qualType.pred = Predicate.noPred
          rw [h_pred_eq]
        constructor
        · -- res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ...
          rw [h_memEnv]
          -- The goal is: updateMemEnv ... { etyp := etyp, poison := joinPoison ctx.pc poison, pred := pred } =
          --            updateMemEnv ... { etyp := etyp, poison := joinPoison ctx.pc result1.qualType.poison, pred := result1.qualType.pred }
          -- We need to show poison = result1.qualType.poison and pred = result1.qualType.pred
          -- This follows from h_qt1
          congr 1
          congr 1
          congr 1
          simp [h_qt1]
          simp [h_qt1]
        constructor
        · -- res.tagEnv' = result1.tagEnv'
          rw [h_tagEnv]
        constructor
        · -- res.nextLoc' = result1.nextLoc' + 1
          rw [h_nextLoc]
        · -- res.nextTag' = result1.nextTag'
          rw [h_nextTag]
    | error _err =>
      simp [h_tc1] at h_typecheck

-- Structure lemma for typecheckApp.
-- Extracts the intermediate typechecking results and function type information.
-- Note: The actual result comes from joinTypeResults which joins multiple closure results,
-- but for the proof we mainly need result1, result2, and the function type with internal poison.
lemma typecheckApp_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckApp ctx e1 e2 fuel = .ok res →
  ∃ (result2 result1 : TypeResult) (st1 st2 : Typ) (p p1 : Poison) (isArrow : Bool),
    typecheckExpr ctx e2 (fuel - 1) = .ok result2 ∧
    typecheckExpr { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv',
                             nextLoc := result2.nextLoc', nextTag := result2.nextTag' } e1 (fuel - 1) = .ok result1 ∧
    ((isArrow = true ∧
      (∃ (tcls : List FnTClosure), result1.qualType.etyp = ETyp.arrow st1 st2 p tcls) ∧
      result1.qualType.poison = p1 ∧
      (¬ ctx.pureCtx) ∧
      (isSubtype st1 result2.qualType) ∧
      res.qualType.etyp.toTyp = st2 ∧
      res.qualType.pred = Predicate.noPred)
     ∨
     (isArrow = false ∧
      (∃ (tcls_p : List PFnTClosure), result1.qualType.etyp = ETyp.parrow st1 st2 p tcls_p) ∧
      result1.qualType.poison = p1 ∧
      (isSubtype st1 result2.qualType) ∧
      res.qualType.etyp.toTyp = st2 ∧
      res.qualType.pred = Predicate.noPred)) := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckApp] at h_typecheck
  | succ fuel' =>
      unfold typecheckApp at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc2_result : typecheckExpr ctx e2 fuel' with
      | ok result2 =>
          simp [h_tc2_result] at h_typecheck
          match h_qt2 : result2.qualType with
          | QTyp.mk etyp2 p2 pred2 =>
              rw [h_qt2] at h_typecheck
              simp at h_typecheck
              let ctx' := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
              have h_ctx'_eq : ctx' = { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag' } := rfl
              cases h_tc1_result : typecheckExpr ctx' e1 fuel' with
              | ok result1 =>
                  rw [h_ctx'_eq] at h_tc1_result
                  simp [h_tc1_result] at h_typecheck
                  match h_qt1 : result1.qualType with
                  | QTyp.mk etyp1 p1 pred1 =>
                      rw [h_qt1] at h_typecheck
                      simp at h_typecheck
                      cases etyp1 with
                      | arrow st1 st2 p tcls =>
                          simp at h_typecheck
                          split at h_typecheck
                          · -- pureCtx = true: error case
                            simp at h_typecheck
                          · next h_notPureCtx =>
                            split at h_typecheck
                            · -- tcls.isEmpty = true: error case
                              simp at h_typecheck
                            · next h_notEmpty =>
                              split at h_typecheck
                              · -- isSubtype check fails: error case
                                simp at h_typecheck
                              · next h_subtype =>
                                -- Extract structure from joinTypeResults
                                have h_arrow : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls := by simp [h_qt1]
                                -- Extract what we can: result2, result1, function type
                                -- The joinTypeResults analysis is complex, so we extract the essential structure
                                refine ⟨result2, result1, st1, st2, p, p1, true, ?_, ?_, ?_⟩
                                · simp only [Nat.add_sub_cancel]
                                  exact h_tc2_result
                                · simp only [Nat.add_sub_cancel]
                                  exact h_tc1_result
                                · left
                                  constructor
                                  · rfl
                                  constructor
                                  · -- Show ∃ tcls, result1.qualType.etyp = ETyp.arrow st1 st2 p tcls
                                    use tcls, h_arrow
                                  constructor
                                  · -- result1.qualType.poison = p1
                                    simp [h_qt1]
                                  constructor
                                  · exact h_notPureCtx
                                  constructor
                                  · -- Convert h_subtype: ¬isSubtype st1 { etyp := etyp2, ... } = false
                                    -- means isSubtype st1 { etyp := etyp2, ... } = true
                                    -- Use h_qt2 to rewrite result2.qualType to the QTyp constructor
                                    rw [h_qt2]
                                    simp [h_subtype]
                                  constructor
                                  · -- res.qualType.etyp.toTyp = st2
                                    -- This requires analyzing joinTypeResults which joins closure results
                                    -- All closures should return compatible types with toTyp = st2
                                    sorry -- TODO: Show res.qualType.etyp.toTyp = st2 from joinTypeResults
                                  · -- res.qualType.pred = Predicate.noPred
                                    -- Use helper lemma: joinTypeResults sets pred to noPred for function types
                                    -- Extract from h_typecheck that joinTypeResults succeeded
                                    -- The definition of joinTypeResults (Typecheck.lean:864-867) shows:
                                    --   match joinedEtyp with | arrow _ _ _ _ => noPred | parrow _ _ _ _ => noPred | _ => joinedPred
                                    -- So we need to show res.qualType.etyp is arrow or parrow, then the match sets pred = noPred
                                    -- This follows from joinETyps_arrow_structure preserving arrow structure
                                    have h_res_arrow : res.qualType.etyp.isArrow := by
                                      -- Extract from joinTypeResults that the result is arrow st1 st2
                                      -- This follows from joinETyps_arrow_structure preserving arrow structure
                                      -- and the fact that all closure results have compatible signatures
                                      sorry -- TODO: Show res.qualType.etyp.isArrow from joinTypeResults structure
                                    -- Now use the helper lemma (once we prove it)
                                    -- For now, use the fact that joinTypeResults sets pred = noPred for function types
                                    sorry -- TODO: Use joinTypeResults_pred_noPred_for_function_types with h_res_arrow
                      | parrow st1 st2 p tcls_p =>
                          simp at h_typecheck
                          split at h_typecheck
                          · -- tcls_p.isEmpty = true: error case
                            simp at h_typecheck
                          · next h_notEmpty =>
                            split at h_typecheck
                            · -- isSubtype check fails: error case
                              simp at h_typecheck
                            · next h_subtype =>
                              have h_parrow : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls_p := by simp [h_qt1]
                              refine ⟨result2, result1, st1, st2, p, p1, false, ?_, ?_, ?_⟩
                              · simp only [Nat.add_sub_cancel]
                                exact h_tc2_result
                              · simp only [Nat.add_sub_cancel]
                                exact h_tc1_result
                              · right
                                constructor
                                · rfl
                                constructor
                                · -- Show ∃ tcls_p, result1.qualType.etyp = ETyp.parrow st1 st2 p tcls_p
                                  use tcls_p, h_parrow
                                constructor
                                · -- result1.qualType.poison = p1
                                  simp [h_qt1]
                                constructor
                                · -- Convert h_subtype using h_qt2
                                  rw [h_qt2]
                                  simp [h_subtype]
                                constructor
                                · -- res.qualType.etyp.toTyp = st2
                                  sorry -- TODO: Show res.qualType.etyp.toTyp = st2 from joinTypeResults
                                · -- res.qualType.pred = Predicate.noPred
                                  -- Similar to arrow case: use joinTypeResults_pred_noPred_for_function_types
                                  have h_res_parrow : res.qualType.etyp.isParrow := by
                                    sorry -- TODO: Show res.qualType.etyp.isParrow from joinTypeResults structure
                                  sorry -- TODO: Extract structure and use joinTypeResults_pred_noPred_for_function_types
                      | _ =>
                          -- Not a function type: error case
                          simp at h_typecheck
              | error _msg =>
                  rw [h_ctx'_eq] at h_tc1_result
                  simp [h_tc1_result] at h_typecheck
      | error _msg =>
          simp [h_tc2_result] at h_typecheck

-- Extract the guard tag from a qualified type's predicate, if present.
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

/-- Structure lemma for typecheckIf with both modes explicitly exposed.
    Mode 1 (predicate-based): matchGuard succeeds, e2/e3 use original memEnv with modified tagEnv
    Mode 2 (standard): matchGuard fails, e2/e3 use ctxAfter from e1's result -/
lemma typecheckIf_structure (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    -- Case disjunction on matchGuard result
    (-- Mode 1: Predicate-based (matchGuard succeeds)
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv = .ok (k, deps) ∧
       ∃ res1 : TypeResult,
         -- e1 typechecks in pure context
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ res2 : TypeResult,
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
           -- e2 typechecks in true-tag context (original memEnv!)
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           ∃ res3 : TypeResult,
             let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
             let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
             -- e3 typechecks in false-tag context (original memEnv!)
             typecheckExpr ctxFalse' e3 (fuel - 1) = .ok res3 ∧
             -- Output structure
             res.memEnv' = joinMemEnvs res2.memEnv' res3.memEnv' ∧
             res.tagEnv' = ctx.tagEnv ∧
             res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
             res.nextTag' = max res2.nextTag' res3.nextTag')
    ∨
    (-- Mode 2: Standard (matchGuard fails)
     (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv = .error err) ∧
     ∃ res1 : TypeResult,
       -- e1 typechecks in original context
       typecheckExpr ctx e1 (fuel - 1) = .ok res1 ∧
       res1.qualType.etyp = ETyp.bool ∧
       ∃ res2 : TypeResult,
         let ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
         let pc' := joinPoison ctx.pc res1.qualType.poison
         let ctx'' := { ctx' with pc := pc' }
         -- e2 typechecks in context derived from res1
         typecheckExpr ctx'' e2 (fuel - 1) = .ok res2 ∧
         ∃ res3 : TypeResult,
           let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           -- e3 typechecks in context with advanced nextLoc/nextTag
           typecheckExpr ctxForE3 e3 (fuel - 1) = .ok res3 ∧
           -- Output structure
           res.memEnv' = joinMemEnvs res2.memEnv' res3.memEnv' ∧
           let ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                  nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
           res.tagEnv' = ctx'.tagEnv ∧
           res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
           res.nextTag' = max res2.nextTag' res3.nextTag' ∧
           -- Poison computation
           res.qualType.poison = joinPoison ctx.pc (joinPoison res1.qualType.poison
                                   (joinPoison res2.qualType.poison res3.qualType.poison))) := by
  intro htc
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    simp only [Nat.succ_sub_one]
    unfold typecheckIf at htc
    simp only [bind, Except.bind] at htc
    -- Case split on matchGuard
    cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv with
    | ok kd =>
      -- Mode 1: Predicate-based
      left
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      refine ⟨k, deps, rfl, ?_⟩
      -- Extract result1
      cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
      | error e =>
        simp only [htc1] at htc
        cases htc
      | ok result1 =>
        simp only [htc1] at htc
        refine ⟨result1, rfl, ?_⟩
        -- Destructure result1.qualType and check bool type
        match hq1 : result1.qualType with
        | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        by_cases hbool : etyp1 = ETyp.bool
        · constructor
          · exact hbool
          simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
          -- Extract result2
          cases htc2 : typecheckExpr { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } e2 fuel' with
          | error e =>
            simp only [htc2] at htc
            cases htc
          | ok result2 =>
            simp only [htc2] at htc
            refine ⟨result2, rfl, ?_⟩
            -- Destructure result2.qualType
            match hq2 : result2.qualType with
            | ⟨etyp2, p2, pred2⟩ =>
            simp only [hq2] at htc
            -- Extract result3
            let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
            let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
            cases htc3 : typecheckExpr ctxFalse' e3 fuel' with
            | error e =>
              rw [htc3] at htc
              cases htc
            | ok result3 =>
              rw [htc3] at htc
              refine ⟨result3, rfl, ?_⟩
              -- Destructure result3.qualType
              match hq3 : result3.qualType with
              | ⟨etyp3, p3, pred3⟩ =>
              simp only [hq3] at htc
              -- Check type compatibility
              by_cases hcompat : beqETypSignature etyp2 etyp3 = false
              · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc
                cases htc
              · -- hcompat : ¬ beqETypSignature etyp2 etyp3 = false, so it equals true
                have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                  cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at htc
                rw [← htc]
                simp
        · simp only [hbool, bne_iff_ne, ne_eq] at htc
          cases htc
    | error err =>
      -- Mode 2: Standard
      right
      simp only [hmatch] at htc
      constructor
      · exact ⟨err, rfl⟩
      -- Extract result1
      cases htc1 : typecheckExpr ctx e1 fuel' with
      | error e =>
        simp only [htc1] at htc
        cases htc
      | ok result1 =>
        simp only [htc1] at htc
        refine ⟨result1, rfl, ?_⟩
        -- Destructure result1.qualType and check bool type
        match hq1 : result1.qualType with
        | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        by_cases hbool : etyp1 = ETyp.bool
        · constructor
          · exact hbool
          simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
          -- Extract result2
          let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
          let pc' := joinPoison ctx.pc p1
          let ctx'' := { ctx' with pc := pc' }
          cases htc2 : typecheckExpr ctx'' e2 fuel' with
          | error e =>
            rw [htc2] at htc
            cases htc
          | ok result2 =>
            rw [htc2] at htc
            refine ⟨result2, rfl, ?_⟩
            -- Destructure result2.qualType
            match hq2 : result2.qualType with
            | ⟨etyp2, p2, pred2⟩ =>
            simp only [hq2] at htc
            -- Extract result3
            let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
            cases htc3 : typecheckExpr ctxForE3 e3 fuel' with
            | error e =>
              rw [htc3] at htc
              cases htc
            | ok result3 =>
              rw [htc3] at htc
              refine ⟨result3, rfl, ?_⟩
              -- Destructure result3.qualType
              match hq3 : result3.qualType with
              | ⟨etyp3, p3, pred3⟩ =>
              simp only [hq3] at htc
              -- Check type compatibility
              by_cases hcompat : beqETypSignature etyp2 etyp3 = false
              · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc
                cases htc
              · -- hcompat : ¬ beqETypSignature etyp2 etyp3 = false, so it equals true
                have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                  cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at htc
                rw [← htc]
                simp
        · simp only [hbool, bne_iff_ne, ne_eq] at htc
          cases htc

/-- In standard mode (when matchGuard fails), typecheckIf produces a result with noPred. -/
lemma typecheckIf_standard_pred_noPred (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv = .error err) →
    res.qualType.pred = Predicate.noPred := by
  intro htc hmatch_fail
  obtain ⟨err, hmatch_err⟩ := hmatch_fail
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind, hmatch_err] at htc
    -- Now we're in the standard mode path
    cases htc1 : typecheckExpr ctx e1 fuel' with
    | error e =>
      simp only [htc1] at htc
      cases htc
    | ok result1 =>
      simp only [htc1] at htc
      match hq1 : result1.qualType with
      | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        by_cases hbool : etyp1 = ETyp.bool
        · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
          -- Extract result2
          let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
          let pc' := joinPoison ctx.pc p1
          let ctx'' := { ctx' with pc := pc' }
          cases htc2 : typecheckExpr ctx'' e2 fuel' with
          | error e =>
            rw [htc2] at htc
            cases htc
          | ok result2 =>
            rw [htc2] at htc
            match hq2 : result2.qualType with
            | ⟨etyp2, p2, pred2⟩ =>
              simp only [hq2] at htc
              let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
              cases htc3 : typecheckExpr ctxForE3 e3 fuel' with
              | error e =>
                rw [htc3] at htc
                cases htc
              | ok result3 =>
                rw [htc3] at htc
                match hq3 : result3.qualType with
                | ⟨etyp3, p3, pred3⟩ =>
                  simp only [hq3] at htc
                  by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                  · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc
                    cases htc
                  · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                      cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                    simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                               pure, Except.pure, Except.ok.injEq] at htc
                    simp [← htc]
        · simp only [hbool, bne_iff_ne, ne_eq] at htc
          cases htc

/-- In standard mode, typecheckIf produces etyp = joinETyps res2.etyp res3.etyp. -/
lemma typecheckIf_standard_etyp (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv = .error err) →
    ∃ (res1 res2 res3 : TypeResult),
      typecheckExpr ctx e1 (fuel - 1) = .ok res1 ∧
      res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                            res2.qualType.poison res3.qualType.poison := by
  intro htc hmatch_fail
  obtain ⟨err, hmatch_err⟩ := hmatch_fail
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind, hmatch_err] at htc
    cases htc1 : typecheckExpr ctx e1 fuel' with
    | error e =>
      simp only [htc1] at htc
      cases htc
    | ok result1 =>
      simp only [htc1] at htc
      match hq1 : result1.qualType with
      | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        by_cases hbool : etyp1 = ETyp.bool
        · simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
          let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
          let pc' := joinPoison ctx.pc p1
          let ctx'' := { ctx' with pc := pc' }
          cases htc2 : typecheckExpr ctx'' e2 fuel' with
          | error e =>
            rw [htc2] at htc
            cases htc
          | ok result2 =>
            rw [htc2] at htc
            match hq2 : result2.qualType with
            | ⟨etyp2, p2, pred2⟩ =>
              simp only [hq2] at htc
              let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
              cases htc3 : typecheckExpr ctxForE3 e3 fuel' with
              | error e =>
                rw [htc3] at htc
                cases htc
              | ok result3 =>
                rw [htc3] at htc
                match hq3 : result3.qualType with
                | ⟨etyp3, p3, pred3⟩ =>
                  simp only [hq3] at htc
                  by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                  · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc
                    cases htc
                  · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                      cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                    simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                               pure, Except.pure, Except.ok.injEq] at htc
                    refine ⟨result1, result2, result3, ?_, ?_⟩
                    · exact htc1
                    · simp [← htc, hq2, hq3]
        · simp only [hbool, bne_iff_ne, ne_eq] at htc
          cases htc

/-- Variant of typecheckIf_standard_etyp that uses already-established res2, res3. -/
lemma typecheckIf_standard_etyp' (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat)
    (res res1 res2 res3 : TypeResult)
    (htc : typecheckIf ctx e1 e2 e3 fuel = .ok res)
    (hmatch_fail : ∃ err, matchGuard e1 ctx.memEnv ctx.varEnv = .error err)
    (htc1 : typecheckExpr ctx e1 (fuel - 1) = .ok res1)
    (hbool1 : res1.qualType.etyp = ETyp.bool)
    (htc2 : typecheckExpr { pc := joinPoison ctx.pc res1.qualType.poison,
                            memEnv := res1.memEnv', varEnv := ctx.varEnv,
                            tagEnv := res1.tagEnv', nextLoc := res1.nextLoc',
                            nextTag := res1.nextTag', pureCtx := ctx.pureCtx }
            e2 (fuel - 1) = .ok res2)
    (htc3 : typecheckExpr { pc := joinPoison ctx.pc res1.qualType.poison,
                            memEnv := res1.memEnv', varEnv := ctx.varEnv,
                            tagEnv := res1.tagEnv', nextLoc := res2.nextLoc',
                            nextTag := res2.nextTag', pureCtx := ctx.pureCtx }
            e3 (fuel - 1) = .ok res3) :
    res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                          res2.qualType.poison res3.qualType.poison := by
  obtain ⟨err, hmatch_err⟩ := hmatch_fail
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    unfold typecheckIf at htc
    simp only [bind, Except.bind, hmatch_err] at htc
    simp only [Nat.succ_sub_one] at htc1 htc2 htc3
    cases htc1' : typecheckExpr ctx e1 fuel' with
    | error e =>
      simp only [htc1'] at htc
      cases htc
    | ok result1 =>
      simp only [htc1'] at htc
      -- result1 = res1
      have hres1_eq : res1 = result1 := by rw [htc1] at htc1'; injection htc1'
      subst hres1_eq
      match hq1 : res1.qualType with
      | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        have hbool' : etyp1 = ETyp.bool := by simp [hq1] at hbool1; exact hbool1
        simp only [hbool', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
        let ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                               nextLoc := res1.nextLoc', nextTag := res1.nextTag' }
        let pc' := joinPoison ctx.pc p1
        let ctx'' := { ctx' with pc := pc' }
        cases htc2' : typecheckExpr ctx'' e2 fuel' with
        | error e =>
          rw [htc2'] at htc
          cases htc
        | ok result2 =>
          rw [htc2'] at htc
          -- result2 = res2
          have hp1_eq : p1 = res1.qualType.poison := by simp [hq1]
          have hpc'_eq : pc' = joinPoison ctx.pc res1.qualType.poison := by simp [pc', hp1_eq]
          have hres2_eq : res2 = result2 := by
            simp only [ctx'', ctx', hpc'_eq] at htc2'
            rw [htc2] at htc2'
            injection htc2'
          subst hres2_eq
          match hq2 : res2.qualType with
          | ⟨etyp2, p2, pred2⟩ =>
            simp only [hq2] at htc
            let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            cases htc3' : typecheckExpr ctxForE3 e3 fuel' with
            | error e =>
              rw [htc3'] at htc
              cases htc
            | ok result3 =>
              rw [htc3'] at htc
              -- result3 = res3
              have hres3_eq : res3 = result3 := by
                simp only [ctxForE3, ctx'', ctx', hpc'_eq] at htc3'
                rw [htc3] at htc3'
                injection htc3'
              subst hres3_eq
              match hq3 : res3.qualType with
              | ⟨etyp3, p3, pred3⟩ =>
                simp only [hq3] at htc
                by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc
                  cases htc
                · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                    cases h : beqETypSignature etyp2 etyp3
                    · simp [h] at hcompat
                    · rfl
                  simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                             pure, Except.pure, Except.ok.injEq] at htc
                  simp [← htc]

-- Structure lemma for rand typechecking.
lemma typecheckRand_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckRand ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.int ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' ∧
    res.qualType.etyp = ETyp.int ∧
    res.qualType.poison = joinPoison ctx.pc result1.qualType.poison ∧
    res.qualType.pred = Predicate.noPred := by
  intro htc
  cases fuel with
  | zero =>
      simp [typecheckRand] at htc
  | succ fuel' =>
      unfold typecheckRand at htc
      simp [bind, Except.bind] at htc
      cases htc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [htc1] at htc
          cases hqt : result1.qualType with
          | mk et poison pred =>
              rw [hqt] at htc
              cases hbad : (et != ETyp.int) with
              | true =>
                  -- would throw, contradiction
                  -- If `et = int`, then `et != int` cannot be true; otherwise `typecheckRand` throws.
                  cases et with
                  | int =>
                      -- `int != int` is false
                      simp at hbad
                  | bool | unit | string | ref _ _ | arrow _ _ _ _ | parrow _ _ _ _ =>
                      -- in all non-int cases `typecheckRand` throws, contradicting `.ok res`
                      simp [throw] at htc
              | false =>
                  -- success: result is `result1` with updated qualType
                  -- first, record `et = int` from the boolean check
                  have het : et = ETyp.int := by
                    cases et <;> simp at hbad
                    rfl
                  subst het
                  have htc' := htc
                  simp [pure, Except.pure] at htc'
                  have h_res :
                      { qualType := { etyp := ETyp.int, poison := joinPoison ctx.pc poison, pred := Predicate.noPred },
                        memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                        nextTag' := result1.nextTag' } = res := by
                    cases htc'
                    rfl
                  refine ⟨result1, ?_, ?_⟩
                  · -- sub typecheck
                    simpa [Nat.succ_sub_one] using htc1
                  · -- remaining field equalities
                    refine ⟨?_, ?_⟩
                    · -- result1 etyp = int
                      simp [hqt]
                    · -- rest follows by rewriting `res` using `h_res`
                      cases h_res
                      simp [hqt]
      | error msg =>
          simp [htc1] at htc

-- Structure lemma for frand typechecking.
-- We keep it coarse: expose the subresult and the key field equalities.
lemma typecheckFrand_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckFrand ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' + 1 ∧
    res.qualType.etyp = ETyp.int ∧
    res.qualType.poison = true ∧
    qtypGuardTag res.qualType = some result1.nextTag' := by
  intro htc
  cases fuel with
  | zero =>
      simp [typecheckFrand] at htc
  | succ fuel' =>
      unfold typecheckFrand at htc
      simp [bind, Except.bind] at htc
      cases htc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [htc1] at htc
          cases hqt : result1.qualType with
          | mk et poison pred =>
              rw [hqt] at htc
              cases hbad : (et != ETyp.int) with
              | true =>
                  -- If `et = int`, then `et != int` cannot be true; otherwise we throw.
                  cases et with
                  | int =>
                      simp at hbad
                  | bool | unit | string | ref _ _ | arrow _ _ _ _ | parrow _ _ _ _ =>
                      simp [throw] at htc
              | false =>
                  -- `et != int = false` forces `et = int`.
                  have het : et = ETyp.int := by
                    cases et <;> simp at hbad
                    rfl
                  subst het
                  -- Peel off the `Expr.toPExpr` bind by splitting on it.
                  cases hpb : Expr.toPExpr
                      (Expr.op (Expr.op (Expr.var (generateFreshVar ctx "limit" 0 fuel')) Op.gte (Expr.num 0)) Op.and
                        (Expr.op (Expr.var (generateFreshVar ctx "limit" 0 fuel')) Op.lte e1)) with
                  | ok predBody =>
                      have htc' := htc
                      -- After substituting `et = int`, the outer `if` reduces to the success branch.
                      simp [hpb, pure, Except.pure, generateFreshTagRes] at htc'
                      have h_res :
                          { qualType :=
                              { etyp := ETyp.int, poison := true,
                                pred := Predicate.guardClosure result1.nextTag' (generateFreshVar ctx "limit" 0 fuel') predBody
                                  (VarTypeEnv.toCaptured ctx.varEnv) },
                            memEnv' := result1.memEnv', tagEnv' := result1.tagEnv', nextLoc' := result1.nextLoc',
                            nextTag' := result1.nextTag' + 1 } = res := by
                        cases htc'
                        rfl
                      refine ⟨result1, ?_, ?_⟩
                      · simpa [Nat.succ_sub_one] using htc1
                      · -- remaining field equalities
                        cases h_res
                        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
                        simp [qtypGuardTag]
                  | error msg =>
                      -- If `Expr.toPExpr` failed, `typecheckFrand` would fail.
                      simp [hpb] at htc
      | error msg =>
          simp [htc1] at htc

-- Structure lemma for assign typechecking
lemma typecheckAssign_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (t : ETyp) (ls : LocSet),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.ref t ls ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 (fuel - 1) = .ok result2 ∧
    result2.qualType.etyp = t ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.etyp = ETyp.unit ∧
    res.qualType.poison = joinPoison ctx.pc result1.qualType.poison ∧
    res.qualType.pred = Predicate.noPred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckAssign at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckAssign at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt1 : result1.qualType with
          | mk etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              simp at h_typecheck
              cases etyp1 with
              | ref t ls =>
                  simp at h_typecheck
                  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                         nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                  cases h_tc2 : typecheckExpr ctx' e2 fuel' with
                  | ok result2 =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
                      cases h_qt2 : result2.qualType with
                      | mk etyp2 p2 pred2 =>
                          rw [h_qt2] at h_typecheck
                          simp at h_typecheck
                          -- The code checks: if t = etyp2 then ... else throw
                          split at h_typecheck
                          · rename_i h_eq  -- t = etyp2
                            simp [pure, Except.pure] at h_typecheck
                            cases h_typecheck
                            refine ⟨result1, result2, t, ls, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl⟩
                            · -- typecheckExpr ctx e1 (fuel - 1) = .ok result1
                              simp only [Nat.add_sub_cancel]
                              exact h_tc1
                            · -- result1.qualType.etyp = ETyp.ref t ls
                              rw [h_qt1]
                            · -- typecheckExpr ctx' e2 (fuel - 1) = .ok result2
                              simp only [Nat.add_sub_cancel]
                              exact h_tc2
                            · -- result2.qualType.etyp = t
                              rw [h_qt2, h_eq]
                            · -- res.qualType.poison = joinPoison ctx.pc p1
                              rw [h_qt1]
                          · -- error branch: t ≠ etyp2 would throw, contradiction
                            contradiction
                  | error _err =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
              | _ =>
                  -- Non-reference type - error case
                  simp at h_typecheck
      | error _err =>
          simp [h_tc1] at h_typecheck

-- Structure lemma for deref typechecking
-- All branches preserve nextTag' from the subexpression result
lemma typecheckDeref_structure (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref ctx e fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e (fuel - 1) = .ok result1 ∧
    res.memEnv' = result1.memEnv' ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' ∧
    res.nextTag' = result1.nextTag' := by
  intro h_typecheck
  cases fuel with
  | zero =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
  | succ fuel' =>
      unfold typecheckDeref at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          -- All return branches have the form:
          -- return { qualType := qt, memEnv' := result1.memEnv', tagEnv' := result1.tagEnv',
          --          nextLoc' := result1.nextLoc', nextTag' := result1.nextTag' }
          -- So we can conclude the result regardless of which branch was taken
          refine ⟨result1, ?_, ?_, ?_, ?_, ?_⟩
          · -- typecheckExpr ctx e (fuel - 1) = .ok result1
            simp only [Nat.add_sub_cancel]
            exact h_tc1
          · -- res.memEnv' = result1.memEnv'
            -- All return branches have: memEnv' := result1.memEnv'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                -- Only the ref case succeeds
                rename_i t ls
                split at h_typecheck
                · -- ls.isEmpty - error case
                  contradiction
                · -- ls not empty - split on foldM result
                  split at h_typecheck
                  · -- foldM error case
                    simp at h_typecheck
                  · -- foldM success case - now split on poisonRef
                    split at h_typecheck
                    · -- poisonRef = true
                      simp [pure, Except.pure] at h_typecheck
                      cases h_typecheck; rfl
                    · -- poisonRef = false - split on merged predicate
                      split at h_typecheck
                      · -- noPred case (h_1)
                        simp [pure, Except.pure] at h_typecheck
                        cases h_typecheck; rfl
                      · -- guardOnly case (h_2) - split on tag lookup
                        split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · -- guardClosure case (h_3) - split on tag lookup
                        split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
          · -- res.tagEnv' = result1.tagEnv'
            -- Same analysis as memEnv'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · simp at h_typecheck
                  · split at h_typecheck
                    · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
          · -- res.nextLoc' = result1.nextLoc'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · simp at h_typecheck
                  · split at h_typecheck
                    · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
          · -- res.nextTag' = result1.nextTag'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · simp at h_typecheck
                  · split at h_typecheck
                    · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
      | error _err =>
          simp [h_tc1] at h_typecheck

-- A stronger arrow-case structure lemma for `typecheckApp` that exposes the `mapM` call and the
-- subsequent `joinTypeResults` call. This is designed to support fault-robustness proofs for `app`.
-- Full application structure: successful `typecheckApp` must go through either the `.arrow` or `.parrow`
-- branch, exposing the `mapM` call and the final `joinTypeResults`.
lemma typecheckApp_arrow_structure_full
  (ctx : TypeContext) (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult) :
  typecheckApp ctx e1 e2 (Nat.succ fuel') = .ok res →
  ∃ (result2 result1 : TypeResult) (etyp2 : ETyp) (p2 : Poison) (pred2 : Predicate),
    result2.qualType = ⟨etyp2, p2, pred2⟩ ∧
    typecheckExpr ctx e2 fuel' = .ok result2 ∧
    typecheckExpr
        { ctx with
            memEnv := result2.memEnv',
            tagEnv := result2.tagEnv',
            nextLoc := result2.nextLoc',
            nextTag := result2.nextTag' }
        e1 fuel' = .ok result1 ∧
    (
      (∃ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
          (results : List TypeResult) (first : TypeResult) (rest : List TypeResult),
        result1.qualType.etyp = ETyp.arrow st1 st2 p tcls ∧
        result1.qualType.poison = p1 ∧
        ¬ ctx.pureCtx ∧
        tcls ≠ [] ∧
        isSubtype st1 result2.qualType = true ∧
        List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls =
          .ok results ∧
        results = first :: rest ∧
        joinTypeResults ctx first rest = .ok res)
      ∨
      (∃ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
          (results : List TypeResult) (first : TypeResult) (rest : List TypeResult),
        result1.qualType.etyp = ETyp.parrow st1 st2 p tcls ∧
        result1.qualType.poison = p1 ∧
        tcls ≠ [] ∧
        isSubtype st1 result2.qualType = true ∧
        List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls =
          .ok results ∧
        results = first :: rest ∧
        joinTypeResults ctx first rest = .ok res)
    ) := by
  intro htc
  unfold typecheckApp at htc
  simp [bind, Except.bind] at htc
  cases h_tc2 : typecheckExpr ctx e2 fuel' with
  | error _err =>
      simp [h_tc2] at htc
  | ok result2 =>
      simp [h_tc2] at htc
      rcases h_qt2 : result2.qualType with ⟨etyp2, p2, pred2⟩
      simp [h_qt2] at htc
      let ctx' : TypeContext :=
        { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
      cases h_tc1 : typecheckExpr ctx' e1 fuel' with
      | error _err =>
          rw [h_tc1] at htc
          simp at htc
      | ok result1 =>
          rw [h_tc1] at htc
          simp at htc
          rcases h_qt1 : result1.qualType with ⟨etyp1, p1, pred1⟩
          simp [h_qt1] at htc
          cases etyp1 with
          | arrow st1 st2 p tcls =>
              -- Discharge the pure-context error branch
              cases h_pure : ctx.pureCtx with
              | true =>
                  simp [h_pure] at htc
              | false =>
                  simp [h_pure, pure, Except.pure] at htc
                  by_cases h_empty : tcls = []
                  · subst h_empty
                    simp at htc
                  · cases h_sub_val : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } with
                    | false =>
                        simp [h_sub_val] at htc
                        simp [h_empty] at htc
                    | true =>
                        have h_sub0 : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                          simp [h_sub_val]
                        have h_sub : isSubtype st1 result2.qualType = true := by
                          simpa [h_qt2] using h_sub0
                        simp [h_sub_val] at htc
                        cases h_map :
                            List.mapM
                              (fun tcl =>
                                applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls with
                        | error _err =>
                            simp [h_map] at htc
                            simp [h_empty] at htc
                        | ok results =>
                            simp [h_map] at htc
                            cases results with
                            | nil =>
                                simp at htc
                                simp [h_empty] at htc
                            | cons first rest =>
                                cases h_join : joinTypeResults ctx first rest with
                                | error _err =>
                                    simp [h_join] at htc
                                    simp [h_empty] at htc
                                | ok res' =>
                                    simp [h_join] at htc
                                    -- eliminate the empty-closure guard and identify res' = res
                                    have h_empty' : tcls ≠ [] := h_empty
                                    simp [h_empty'] at htc
                                    subst res'
                                    refine ⟨result2, result1, etyp2, p2, pred2, ?_⟩
                                    refine And.intro (by simpa [h_qt2]) ?_
                                    refine And.intro rfl ?_
                                    refine And.intro (by simpa [ctx', h_pure] using h_tc1) ?_
                                    left
                                    refine ⟨st1, st2, p, p1, tcls, first :: rest, first, rest, ?_⟩
                                    refine And.intro (by simp [h_qt1]) ?_
                                    refine And.intro (by simp [h_qt1]) ?_
                                    refine And.intro (by simpa [h_pure]) ?_
                                    refine And.intro h_empty ?_
                                    refine And.intro h_sub ?_
                                    refine And.intro (by simpa using h_map) ?_
                                    refine And.intro rfl ?_
                                    simpa using h_join
          | parrow st1 st2 p tcls =>
              by_cases h_empty : tcls = []
              · subst h_empty
                simp [pure, Except.pure] at htc
              · cases h_sub_val : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } with
                | false =>
                    simp [h_empty, h_sub_val, pure, Except.pure] at htc
                | true =>
                    have h_sub0 : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                      simp [h_sub_val]
                    have h_sub : isSubtype st1 result2.qualType = true := by
                      simpa [h_qt2] using h_sub0
                    simp [h_sub_val, pure, Except.pure] at htc
                    cases h_map :
                        List.mapM
                          (fun tcl =>
                            applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls with
                    | error _err =>
                        simp [h_map] at htc
                        simp [h_empty] at htc
                    | ok results =>
                        simp [h_map] at htc
                        cases results with
                        | nil =>
                            simp at htc
                            simp [h_empty] at htc
                        | cons first rest =>
                            cases h_join : joinTypeResults ctx first rest with
                            | error _err =>
                                simp [h_join] at htc
                                simp [h_empty] at htc
                            | ok res' =>
                                simp [h_join] at htc
                                have h_empty' : tcls ≠ [] := h_empty
                                simp [h_empty'] at htc
                                subst res'
                                refine ⟨result2, result1, etyp2, p2, pred2, ?_⟩
                                refine And.intro (by simpa [h_qt2]) ?_
                                refine And.intro rfl ?_
                                refine And.intro (by simpa [ctx', h_tc1]) ?_
                                right
                                refine ⟨st1, st2, p, p1, tcls, first :: rest, first, rest, ?_⟩
                                refine And.intro (by simp [h_qt1]) ?_
                                refine And.intro (by simp [h_qt1]) ?_
                                refine And.intro h_empty ?_
                                refine And.intro h_sub ?_
                                refine And.intro (by simpa using h_map) ?_
                                refine And.intro rfl ?_
                                simpa using h_join
          | _ =>
              simp at htc

end typecheck_structure_lemmas

-- ================================================================
-- Typechecker monotonicity lemmas
-- ================================================================

section typecheck_nextTag_mono_proof

-- Helper lemmas for typecheck_nextTag_mono proof

private lemma typecheckVar_nextTag_mono (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckVar at htc
  cases h_lookup : ctx.varEnv.lookup x with
  | none =>
      simp [h_lookup] at htc
  | some qt =>
      simp [h_lookup] at htc
      cases qt with
      | mk etyp poison pred =>
          cases pred with
          | noPred =>
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact le_rfl
          | guardOnly k =>
              simp at htc
              split at htc
              · injection htc with h_eq
                subst h_eq
                exact le_rfl
              · injection htc with h_eq
                subst h_eq
                exact le_rfl
              · injection htc with h_eq
                subst h_eq
                exact le_rfl
          | guardClosure k _ _ _ =>
              simp at htc
              split at htc
              · injection htc with h_eq
                subst h_eq
                exact le_rfl
              · injection htc with h_eq
                subst h_eq
                exact le_rfl
              · injection htc with h_eq
                subst h_eq
                exact le_rfl

private lemma typecheckOp_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckOp_structure ctx e1 e2 op fuel res htc
  rcases hstruct with ⟨result1, result2, _result_etyp, htc1, htc2, _hop, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckOp at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextTag : ctx'.nextTag = result1.nextTag' := by rfl
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = ctx'.nextTag := h_ctx'_nextTag.symm
        _ ≤ result2.nextTag' := IH2
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckSeq_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckSeq_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
  cases fuel with
  | zero => unfold typecheckSeq at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok res := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' res htc2_simp
      have h_ctx'_nextTag : ctx'.nextTag = result1.nextTag' := by simp [hctx', updateCtxFromResult]
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = ctx'.nextTag := h_ctx'_nextTag.symm
        _ ≤ res.nextTag' := IH2

private lemma typecheckNewRef_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckNewRef ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckNewRef_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, _l, _etyp, htc1, _hl, _hetyp, _hqtetyp, _hqtpoison, _hqtpred, _hmem, _htag, _hloc, hnexttag⟩
  cases fuel with
  | zero => unfold typecheckNewRef at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

-- Helper lemma for typecheckAssign: preserves nextTag' from result2
lemma typecheckAssign_preserves_nextTag (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.nextTag' = result2.nextTag' := by
  intro htc
  have hstruct := typecheckAssign_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, _t, _ls, htc1, _hetyp1, htc2, _hetyp2, _hloc, hnexttag, _⟩
  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                         nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
  exact ⟨result1, result2, ctx', htc1, rfl, htc2, hnexttag⟩

private lemma typecheckAssign_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckAssign_preserves_nextTag ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, hnexttag⟩
  cases fuel with
  | zero => unfold typecheckAssign at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextTag : ctx'.nextTag = result1.nextTag' := by simp [hctx']
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = ctx'.nextTag := h_ctx'_nextTag.symm
        _ ≤ result2.nextTag' := IH2
        _ = res.nextTag' := hnexttag.symm

-- Helper lemma for typecheckDeref: all branches preserve nextTag'
lemma typecheckDeref_preserves_nextTag (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref ctx e fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e (fuel - 1) = .ok result1 ∧
    res.nextTag' = result1.nextTag' := by
  intro htc
  have hstruct := typecheckDeref_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, hnexttag⟩
  exact ⟨result1, htc1, hnexttag⟩

private lemma typecheckDeref_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckDeref ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckDeref_preserves_nextTag ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, hnexttag⟩
  cases fuel with
  | zero => unfold typecheckDeref at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckVlet_nextTag_mono (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckVlet ctx x e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckVlet_structure ctx x e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _hetyp, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckVlet at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextTag : ctx'.nextTag = result1.nextTag' := by simp [hctx']
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = ctx'.nextTag := h_ctx'_nextTag.symm
        _ ≤ result2.nextTag' := IH2
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckIf_nextTag_mono (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckIf ctx e1 e2 e3 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckIf at htc; simp at htc
  | succ fuel' =>
      unfold typecheckIf at htc
      cases hguard : matchGuard e1 ctx.memEnv ctx.varEnv with
      | ok g =>
          rcases g with ⟨k, deps⟩
          simp [hguard, bind, Except.bind] at htc
          set pureCtx : TypeContext := { ctx with pureCtx := true } with hpure
          rcases htc1 : typecheckExpr pureCtx e1 fuel' with _ | ⟨res1⟩
            <;> erw [htc1] at htc
            <;> simp at htc
          rcases hq1 : res1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          by_cases hbool : etyp1 != ETyp.bool
          · simp at hbool; simp [hbool] at htc
          · simp at hbool; simp [hbool] at htc
            set ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } with hctxTrue
            set ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ } with hctxFalse
            rcases htc2 : typecheckExpr ctxTrue e2 fuel' with _ | ⟨res2⟩
              <;> erw [htc2] at htc
              <;> simp [pure, Except.pure] at htc
            rcases hq2 : res2.qualType with ⟨etyp2, p2, pred2⟩
            simp [hq2] at htc
            set ctxFalse' : TypeContext :=
              { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } with hctxFalse'
            rcases htc3 : typecheckExpr ctxFalse' e3 fuel' with _ | ⟨res3⟩
              <;> erw [htc3] at htc
              <;> simp at htc
            rcases hq3 : res3.qualType with ⟨etyp3, p3, pred3⟩
            simp [hq3] at htc
            cases hsig : beqETypSignature etyp2 etyp3 <;> simp [hsig] at htc
            cases htc
            have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
            have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by
              simpa [typecheck] using htc2
            have IH2 := IH fuel' h_fuel e2 ctxTrue res2 htc2'
            have h_ctxTrue_nextTag : ctxTrue.nextTag = ctx.nextTag := by
              simp [hctxTrue]
            have h_ctx_nextTag_le : ctx.nextTag ≤ res2.nextTag' := by
              simpa [h_ctxTrue_nextTag] using IH2
            dsimp
            transitivity
            · exact h_ctx_nextTag_le
            · apply Nat.le_max_left
      | error err =>
          simp [hguard, bind, Except.bind] at htc
          rcases htc1 : typecheckExpr ctx e1 fuel' with _ | ⟨res1⟩
            <;> erw [htc1] at htc
            <;> simp at htc
          rcases hq1 : res1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          by_cases hbool : etyp1 != ETyp.bool
          · simp at hbool; simp [hbool] at htc
          · simp at hbool; simp [hbool] at htc
            simp [pure, Except.pure] at htc
            set ctx' : TypeContext :=
              { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag' } with hctx'
            set ctx'' : TypeContext := { ctx' with pc := joinPoison ctx.pc p1 } with hctx''
            rcases htc2 : typecheckExpr ctx'' e2 fuel' with _ | ⟨res2⟩
              <;> erw [htc2] at htc
              <;> simp at htc
            rcases hq2 : res2.qualType with ⟨etyp2, p2, pred2⟩
            simp [hq2] at htc
            set ctxForE3 : TypeContext :=
              { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' } with hctxForE3
            rcases htc3 : typecheckExpr ctxForE3 e3 fuel' with _ | ⟨res3⟩
              <;> erw [htc3] at htc
              <;> simp at htc
            rcases hq3 : res3.qualType with ⟨etyp3, p3, pred3⟩
            simp [hq3] at htc
            cases hsig : beqETypSignature etyp2 etyp3 <;> simp [hsig] at htc
            cases htc
            have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
            have htc1' : typecheck ctx e1 fuel' = .ok res1 := by
              simpa [typecheck] using htc1
            have IH1 := IH fuel' h_fuel e1 ctx res1 htc1'
            have h_ctx'_nextTag : ctx'.nextTag = res1.nextTag' := by
              simp [hctx']
            have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by
              simpa [typecheck] using htc2
            have IH2 := IH fuel' h_fuel e2 ctx'' res2 htc2'
            have h_ctx''_nextTag : ctx''.nextTag = ctx'.nextTag := by
              simp [hctx'']
            have h_ctx_nextTag_le : ctx.nextTag ≤ res2.nextTag' := by
              calc
                ctx.nextTag ≤ res1.nextTag' := IH1
                _ = ctx'.nextTag := h_ctx'_nextTag.symm
                _ = ctx''.nextTag := h_ctx''_nextTag.symm
                _ ≤ res2.nextTag' := IH2
            transitivity
            · exact h_ctx_nextTag_le
            · apply Nat.le_max_left

private lemma joinTypeResults_nextTag_eq_max
  (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult) :
    joinTypeResults ctx r rs = .ok res →
    res.nextTag' = List.max (r.nextTag' :: rs.map TypeResult.nextTag') (by intro h; cases h) := by
  intro hjoin
  -- Helper: the join fold computes the max of nextTag' across the list.
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvs acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              max acc.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2 result.nextTag')
  have h_fold_nextTag :
      ∀ (rs : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag),
        List.foldlM joinStep acc rs = Except.ok acc' →
        acc'.2.2.2.2.2.2 = List.foldl max acc.2.2.2.2.2.2 (rs.map TypeResult.nextTag') := by
    intro rs acc acc' h
    induction rs generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at h
        cases h
        simp
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at h
            -- h is now about the tail fold; apply the IH.
            have h' := ih _ h
            -- foldl on a cons updates the max with the head.
            simpa [List.foldl_cons] using h'
  -- Unfold joinTypeResults and split on the fold checks.
  cases hqt : r.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at hjoin
      cases hcheck :
          (List.foldlM
      (fun x result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
          if beqETypSignature etyp resEtyp = false then
            Except.error
              (toString "Closure alternatives produced incompatible result types: " ++ toString (repr etyp) ++
                  toString " vs " ++
                toString (repr resEtyp))
          else Except.ok ())
      () rs : Except String Unit) with
      | error err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              simp
              have h_fold := h_fold_nextTag rs _ _ hfold
              -- List.max on a non-empty list is foldl max.
              simpa [List.max] using h_fold

/-- joinTypeResults preserves arrow/parrow structure: if first result is arrow st1 st2, result is arrow st1 st2.
    TODO: this is not a good way to prove this. We need to define helper lemma on FoldM which holds a pairwise property and proves that it holds for the resut!
-/
private lemma joinTypeResults_preserves_arrow_structure
  (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult)
  (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure) :
    r.qualType.etyp = ETyp.arrow st1 st2 p tcls →
    joinTypeResults ctx r rs = .ok res →
    ∃ (p' : Poison) (tcls' : List FnTClosure),
      res.qualType.etyp = ETyp.arrow st1 st2 p' tcls' := by
  intro h_first_arrow hjoin
  -- Unfold joinTypeResults to extract the fold structure
  cases hqt : r.qualType with
  | mk etyp poison pred =>
      -- etyp = ETyp.arrow st1 st2 p tcls from h_first_arrow
      have h_etyp_eq : etyp = ETyp.arrow st1 st2 p tcls := by
        rw [hqt] at h_first_arrow
        simp at h_first_arrow
        exact h_first_arrow
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at hjoin
      -- Extract the signature compatibility check
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++ toString (repr etyp) ++
                        toString " vs " ++
                      toString (repr resEtyp))
                else Except.ok ())
            () rs : Except String Unit) with
      | error err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          -- Extract the join fold
          let joinStep :
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) →
                TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      max acc.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2 result.nextTag')
          -- Helper: the join fold preserves arrow structure
          -- Generalized to work with any p' tcls' that have signature st1 st2
          have h_fold_arrow :
              ∀ (rs : List TypeResult)
                (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag)
                (p_acc : Poison) (tcls_acc : List FnTClosure),
                acc.1 = ETyp.arrow st1 st2 p_acc tcls_acc →
                (∀ r' ∈ rs, beqETypSignature (ETyp.arrow st1 st2 p_acc tcls_acc) r'.qualType.etyp = true) →
                List.foldlM joinStep acc rs = Except.ok acc' →
                ∃ (p' : Poison) (tcls' : List FnTClosure),
                  acc'.1 = ETyp.arrow st1 st2 p' tcls' := by
            intro rs acc acc' p_acc tcls_acc h_acc_arrow h_compat h_fold
            induction rs generalizing acc with
            | nil =>
                simp [List.foldlM_nil, pure, Except.pure] at h_fold
                cases h_fold
                exact ⟨p_acc, tcls_acc, h_acc_arrow⟩
            | cons x xs ih =>
                -- x has compatible signature
                have h_x_compat : beqETypSignature (ETyp.arrow st1 st2 p_acc tcls_acc) x.qualType.etyp = true := by
                  have h_mem : x ∈ x :: xs := by simp
                  exact h_compat x h_mem
                -- x.qualType.etyp.isArrow (since compatible with arrow)
                have h_x_arrow : x.qualType.etyp.isArrow := by
                  -- beqETypSignature returns true only when both are arrows with same st1, st2
                  cases h_x_etyp : x.qualType.etyp with
                  | arrow _ _ _ _ =>
                      simp [ETyp.isArrow]
                  | parrow _ _ _ _ =>
                      -- parrow is not compatible with arrow (beqETypSignature returns false)
                      simp [beqETypSignature, h_x_etyp] at h_x_compat
                  | int | bool | unit | string =>
                      -- Non-function types are not compatible with arrow
                      simp [beqETypSignature, h_x_etyp] at h_x_compat
                  | ref _ _ =>
                      -- ref types are not compatible with arrow
                      simp [beqETypSignature, h_x_etyp] at h_x_compat
                -- Extract resEtyp from x.qualType
                cases h_x_qt : x.qualType with
                | mk resEtyp resPoison resPred =>
                    have h_resEtyp_eq : x.qualType.etyp = resEtyp := by
                      rw [h_x_qt]
                    have h_resEtyp_arrow : resEtyp.isArrow := by
                      rw [← h_resEtyp_eq]
                      exact h_x_arrow
                    have h_resEtyp_compat : beqETypSignature (ETyp.arrow st1 st2 p_acc tcls_acc) resEtyp = true := by
                      rw [← h_resEtyp_eq]
                      exact h_x_compat
                    -- resEtyp must be arrow with same st1, st2 (from compatibility)
                    have h_resEtyp_arrow_form : ∃ (st1' st2' : Typ) (p2 : Poison) (tcls2 : List FnTClosure),
                        resEtyp = ETyp.arrow st1' st2' p2 tcls2 := by
                      cases resEtyp with
                      | arrow st1' st2' p2 tcls2 =>
                          exact ⟨st1', st2', p2, tcls2, rfl⟩
                      | _ => simp [ETyp.isArrow] at h_resEtyp_arrow
                    obtain ⟨st1', st2', p2, tcls2, h_resEtyp_form⟩ := h_resEtyp_arrow_form
                    -- Compatibility means (st1 == st1' && st2 == st2') = true
                    have h_sig_eq : (st1 == st1' && st2 == st2') = true := by
                      rw [h_resEtyp_form] at h_resEtyp_compat
                      simp only [beqETypSignature] at h_resEtyp_compat
                      assumption
                    -- Now show joinETyps preserves arrow structure
                    have h_join_arrow : ∃ (p' : Poison) (tcls' : List FnTClosure),
                        joinETyps (ETyp.arrow st1 st2 p_acc tcls_acc) resEtyp acc.2.2.1 resPoison = ETyp.arrow st1 st2 p' tcls' := by
                      rw [h_resEtyp_form]
                      simp only [joinETyps]
                      simp [h_sig_eq, ↓reduceIte]
                    obtain ⟨p_joined, tcls_joined, h_join_eq⟩ := h_join_arrow
                    -- Now apply IH on the tail
                    -- h_fold shows: List.foldlM joinStep acc (x :: xs) = Except.ok acc'
                    -- Extract the new accumulator from h_fold
                    simp [List.foldlM_cons, bind, Except.bind] at h_fold
                    -- h_fold now shows: (joinStep acc x >>= fun acc_new => fold on tail) = Except.ok acc'
                    -- Extract joinStep result
                    match h_step_val : joinStep acc x with
                    | Except.error err =>
                        simp [h_step_val] at h_fold
                    | Except.ok acc_new_val =>
                        simp [h_step_val] at h_fold
                        -- h_step_val shows: joinStep acc x = Except.ok acc_new_val
                        -- Simplify joinStep to extract tuple
                        simp [joinStep, h_x_qt] at h_step_val
                        -- Now h_step_val is: Except.ok (tuple) = Except.ok acc_new_val
                        -- Extract tuple equality from Except.ok equality
                        have h_step_eq : (joinETyps acc.1 resEtyp acc.2.2.1 resPoison, joinMemEnvs acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv', max acc.2.2.2.2.2.1 x.nextLoc',
                            max acc.2.2.2.2.2.2 x.nextTag') = acc_new_val := by
                          sorry -- TODO: Extract from Except.ok equality
                        -- Extract first component
                        have h_acc_new_1 : acc_new_val.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison := by
                          sorry -- TODO: Extract from tuple equality h_step_eq
                        have h_acc_new_arrow_joined : acc_new_val.1 = ETyp.arrow st1 st2 p_joined tcls_joined := by
                          rw [h_acc_new_1, h_acc_arrow, h_join_eq]
                        -- Apply IH on tail with acc_new_val
                        have h_compat_tail : ∀ r' ∈ xs, beqETypSignature (ETyp.arrow st1 st2 p_joined tcls_joined) r'.qualType.etyp = true := by
                          intro r' h_mem
                          -- Original compatibility with arrow st1 st2 p_acc tcls_acc
                          have h_orig : beqETypSignature (ETyp.arrow st1 st2 p_acc tcls_acc) r'.qualType.etyp = true := by
                            have h_mem' : r' ∈ x :: xs := by simp [h_mem]
                            exact h_compat r' h_mem'
                          -- beqETypSignature only checks st1 == st1' && st2 == st2', so compatibility is preserved
                          sorry -- TODO: Show compatibility preserved when changing p_acc/tcls_acc to p_joined/tcls_joined
                        -- Apply generalized IH with p_joined and tcls_joined
                        -- The IH signature is: ∀ acc, acc.1 = arrow st1 st2 p_acc tcls_acc → ...
                        -- We need to use p_joined and tcls_joined as p_acc and tcls_acc
                        -- But the IH is quantified over p_acc and tcls_acc, so we can instantiate it
                        sorry -- TODO: Apply IH with p_joined and tcls_joined - need to fix IH signature
          -- Apply the helper
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              simp at hjoin
              -- Extract that res.qualType.etyp = a.1
              -- hjoin shows: { qualType := { etyp := a.1, ... }, ... } = res
              -- Extract etyp equality
              have h_res_etyp : res.qualType.etyp = a.1 := by
                sorry -- TODO: Extract etyp from record equality hjoin
              -- Use h_fold_arrow to show a.1 is arrow
              have h_compat_all : ∀ r' ∈ rs, beqETypSignature (ETyp.arrow st1 st2 p tcls) r'.qualType.etyp = true := by
                -- This follows from the signature check passing in hcheck
                -- hcheck shows that all r' in rs have beqETypSignature etyp r'.qualType.etyp = true
                -- and etyp = arrow st1 st2 p tcls, so the result follows
                intro r' h_mem
                -- Extract from hcheck that beqETypSignature etyp r'.qualType.etyp = true
                -- This requires unfolding the fold in hcheck
                sorry -- TODO: Extract from hcheck - need to show foldlM check implies compatibility
              have h_fold_arrow_result := h_fold_arrow rs (etyp, r.memEnv', poison, pred, r.tagEnv', r.nextLoc', r.nextTag') a p tcls h_etyp_eq h_compat_all hfold
              obtain ⟨p', tcls', h_a1_arrow⟩ := h_fold_arrow_result
              -- Now show res.qualType.etyp = arrow st1 st2 p' tcls'
              use p', tcls'
              rw [h_res_etyp, h_a1_arrow]


/-- joinTypeResults sets pred to noPred when the joined etyp is a function type (arrow or parrow).
    NOTE: This lemma may be difficult to prove directly because it requires extracting
    the structure from the nested match in joinTypeResults. Consider using a stronger
    lemma that extracts the full structure first. -/
private lemma joinTypeResults_pred_noPred_for_function_types
  (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult) :
    joinTypeResults ctx r rs = .ok res →
    (res.qualType.etyp.isArrow ∨ res.qualType.etyp.isParrow) →
    res.qualType.pred = Predicate.noPred := by
  intro hjoin hfun
  -- Unfold joinTypeResults just far enough to expose the `finalPred` match
  cases hqt : r.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at hjoin
      -- The signature-check fold must have succeeded (otherwise `.ok res` is impossible).
      cases hcheck :
          (List.foldlM
              (fun x result =>
                match result.qualType with
                | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                    if beqETypSignature etyp resEtyp = false then
                      Except.error
                        (toString "Closure alternatives produced incompatible result types: " ++
                          toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                    else Except.ok ())
              () rs : Except String Unit) with
      | error err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          -- The join fold must have succeeded too.
          let joinStep :
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) →
                TypeResult →
                  Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Loc × Tag)
              (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      max acc.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2 result.nextTag')
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              -- At this point `hjoin` pins down `res` (including the `finalPred` match).
              simp at hjoin
              cases hjoin
              -- Destructure the fold accumulator so we can case-split on the joined etyp directly.
              rcases a with ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, maxNextLoc, maxNextTag⟩
              -- Reduce the goal to the `finalPred` match, and eliminate non-function cases
              have hfun' : joinedEtyp.isArrow = true ∨ joinedEtyp.isParrow = true := by
                simpa using hfun
              cases joinedEtyp <;>
                (simp [ETyp.isArrow, ETyp.isParrow] at hfun' <;> simp)


private lemma applyFnTClosure_nextTag_mono
  (tcl : FnTClosure) (ctx : TypeContext)
  (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' → ctx'.nextTag ≤ res'.nextTag') :
  applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 fuel = .ok r2 →
  r1.nextTag' ≤ r2.nextTag' := by
  intro happly
  unfold applyFnTClosure at happly
  cases fuel <;> simp at happly
  cases tcl <;> simp at happly
  · simp [bind, Except.bind] at happly
    rcases htc : typecheckExpr _ _ _ with _ | ⟨r⟩
      <;> rw [htc] at happly
      <;> simp at happly
    rcases hqt : r.qualType with ⟨etyp, poison, pred⟩
    simp [hqt] at happly
    rcases hsub : isSubtype st2 _
      <;> rw [hsub] at happly
      <;> simp at happly
    · simp [Functor.map, Except.map] at happly
    · simp [pure, Except.pure] at happly
      subst r2
      specialize IH _ (lt_add_one _) _ _ _ htc
      simp at IH
      exact IH
  · simp [bind, Except.bind] at happly
    rename_i argName retSpec effects capturedEnv
    set unifiedEnv :=
      (VarTypeEnv.ofCaptured capturedEnv).update argName
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred }
    split at happly
    · cases happly
    · cases retSpec with
      | nestedFn innerArg innerArgTyp innerRet innerEffects =>
          simp [pure, Except.pure] at happly
          cases happly
          exact le_rfl
      | nestedPfn innerArg innerArgTyp innerRet =>
          simp [pure, Except.pure] at happly
          cases happly
          exact le_rfl
      | simple typ poison pred =>
          simp at happly
          split at happly
          · cases happly
          · rename_i hret retVal
            cases hret_etyp : hret.1.etyp with
            | ref t ls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                  split at happly
                  · cases happly
                  · cases happly
                    exact le_rfl
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | int =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | bool =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | unit =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | string =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | arrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
            | parrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl

private lemma typecheckApp_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckApp ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckApp at htc
  cases fuel <;> simp at htc
  rename_i fuel'
  simp [bind, Except.bind] at htc
  rcases hcte2 : typecheckExpr ctx e2 _ with _ | ⟨res2⟩
    <;> rw [hcte2] at htc
    <;> simp at htc
  rcases hq2 : res2.qualType with ⟨etyp2, poison2, pred2⟩
  simp [hq2] at htc
  set ctx' : TypeContext := {
    pc := ctx.pc,
    memEnv := res2.memEnv',
    varEnv := ctx.varEnv,
    tagEnv := res2.tagEnv',
    nextLoc := res2.nextLoc',
    nextTag := res2.nextTag',
    pureCtx := ctx.pureCtx } with hctx'
  rcases htce1 : typecheckExpr ctx' e1 _ with _ | ⟨res1⟩
    <;> rw [htce1] at htc
    <;> simp at htc
  rcases hq1 : res1.qualType with ⟨etyp1, poison1, pred1⟩
  simp [hq1] at htc
  rcases etyp1 with _ | _ | _ | _ | _ | ⟨t1, t2, p, fs⟩ | _
    <;> simp at htc
  · rcases hctx : ctx.pureCtx <;> simp [hctx] at htc
    rcases fs with _ | ⟨f, fs'⟩ <;> simp at htc
    rcases hsub1 : isSubtype t1 _
      <;> rw [hsub1] at htc
      <;> simp at htc
    simp [bind, Except.bind] at htc
    rcases happly : applyFnTClosure f t1 t2 p poison1 etyp2 poison2 pred2 ctx res2 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons : List.cons r <$> List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res2 _) fs' with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap : List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res2 _) fs' with _ | ⟨rs''⟩
      <;> rw [hmap] at hcons
      <;> simp at hcons
    rcases hcons with ⟨heq1, heq2⟩
    subst r1
    subst rs''
    -- ctx.nextTag <= res1.nextTag (by IH on htce1)
    -- res1.nextTag = ctx'.nextTag
    -- ctx'.nextTag <= res2.nextTag (by IH on hcte2)
    -- res2.nextTag <= r.nextTag (by applyFnTClosure_nextTag_mono)
    -- forall r in rs', res2.nextTag <= r.nextTag (by applyFnTClosure_nextTag_mono)
    -- res2.nextTag <= max (r.nextTag, map rs' .nextTag) (follows from above)
    -- max (res2.nextTag, map rs' .nextTag) = res.nextTag (by joinTypeResults_nextTag_eq_max)
    have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
    have hcte2' : typecheck ctx e2 fuel' = .ok res2 := by
      simpa [typecheck] using hcte2
    have IH2 := IH fuel' h_fuel e2 ctx res2 hcte2'
    have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by
      simpa [typecheck] using htce1
    have _IH1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextTag ≤ res'.nextTag' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res2.nextTag' ≤ r.nextTag' := by
      exact applyFnTClosure_nextTag_mono f ctx t1 t2 p poison1 etyp2 poison2 pred2 res2 r fuel' IH' happly
    have h_join :
        res.nextTag' =
          List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      joinTypeResults_nextTag_eq_max ctx r rs' res htc
    have h_r_le_res : r.nextTag' ≤ res.nextTag' := by
      have h_r_le_max :
          r.nextTag' ≤
            List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) := by
        apply List.le_max_of_mem
        simp
      simpa [h_join] using h_r_le_max
    calc
      ctx.nextTag ≤ res2.nextTag' := IH2
      _ = ctx'.nextTag := by simp [hctx']
      _ ≤ r.nextTag' := h_r
      _ ≤ res.nextTag' := h_r_le_res
  · rename_i st1 st2 p tcls
    rcases tcls with _ | ⟨f, fs'⟩ <;> simp at htc
    rcases hsub1 : isSubtype st1 _
      <;> rw [hsub1] at htc
      <;> simp at htc
    simp [bind, Except.bind] at htc
    rcases happly : applyPFnTClosure f st1 st2 p poison1 etyp2 poison2 pred2 ctx res2 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons :
        List.cons r <$>
          List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res2 _) fs'
        with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap :
        List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res2 _) fs'
        with _ | ⟨rs''⟩
      <;> rw [hmap] at hcons
      <;> simp at hcons
    rcases hcons with ⟨heq1, heq2⟩
    subst r1
    subst rs''
    have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
    have hcte2' : typecheck ctx e2 fuel' = .ok res2 := by
      simpa [typecheck] using hcte2
    have IH2 := IH fuel' h_fuel e2 ctx res2 hcte2'
    have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by
      simpa [typecheck] using htce1
    have _IH1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextTag ≤ res'.nextTag' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res2.nextTag' ≤ r.nextTag' := by
      unfold applyPFnTClosure at happly
      cases fuel' with
      | zero =>
          simp at happly
      | succ fuel'' =>
          cases f with
          | regular x body env =>
              simp [bind, Except.bind] at happly
              cases htc_body : typecheckExpr _ _ _ with
              | error err =>
                  rw [htc_body] at happly
                  simp at happly
              | ok r3 =>
                  rw [htc_body] at happly
                  simp at happly
                  rcases hq3 : r3.qualType with ⟨etyp3, poison3, pred3⟩
                  simp [hq3] at happly
                  cases hsub : isSubtype st2 { etyp := etyp3, poison := poison3, pred := pred3 } with
                  | false =>
                      rw [hsub] at happly
                      simp at happly
                  | true =>
                      rw [hsub] at happly
                      simp [pure, Except.pure] at happly
                      set ctx'' : TypeContext :=
                        { pc := joinPoison p (joinPoison ctx.pc poison1),
                          memEnv := res2.memEnv',
                          varEnv :=
                            (VarTypeEnv.ofCaptured env).update x
                              { etyp := etyp2, poison := joinPoison ctx.pc poison2, pred := pred2 },
                          tagEnv := res2.tagEnv',
                          nextLoc := res2.nextLoc',
                          nextTag := res2.nextTag',
                          pureCtx := true } with hctx''
                      have htc_body' : typecheck ctx'' body.toExpr fuel'' = .ok r3 := by
                        simpa [typecheck, hctx''] using htc_body
                      have IH_body := IH' fuel'' (Nat.lt_succ_self fuel'') body.toExpr ctx'' r3 htc_body'
                      cases happly
                      simpa using IH_body
          | extern x retSpec capturedEnv =>
              cases retSpec with
              | simple typ poison pred =>
                  simp [bind, Except.bind] at happly
                  cases hret : returnSpecToQTyp _ _ _ _ _ with
                  | error err =>
                      rw [hret] at happly
                      simp at happly
                  | ok ret =>
                      rw [hret] at happly
                      simp [pure, Except.pure] at happly
                      cases happly
                      exact le_rfl
              | nestedFn innerArg innerArgTyp innerRet innerEffects =>
                  simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
              | nestedPfn innerArg innerArgTyp innerRet =>
                  simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
    have h_join :
        res.nextTag' =
          List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      joinTypeResults_nextTag_eq_max ctx r rs' res htc
    have h_r_le_res : r.nextTag' ≤ res.nextTag' := by
      have h_r_le_max :
          r.nextTag' ≤
            List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) := by
        apply List.le_max_of_mem
        simp
      simpa [h_join] using h_r_le_max
    calc
      ctx.nextTag ≤ res2.nextTag' := IH2
      _ = ctx'.nextTag := by simp [hctx']
      _ ≤ r.nextTag' := h_r
      _ ≤ res.nextTag' := h_r_le_res

private lemma runWhileFixpoint_nextTag_mono
  (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (pureGuard : Bool) (guardOpt : Option (Tag × Deps))
  (pc : Poison) (mem : MemoryTypeEnv) (tag : TagEnv) (nextLoc : Loc) (nextTag : Tag)
  (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
    typecheck ctx' e m = .ok res' →
    ctx'.nextTag ≤ res'.nextTag') :
  runWhileFixpoint ctx e1 e2 fuel pureGuard guardOpt = .ok (pc, mem, tag, nextLoc, nextTag) →
  ctx.nextTag ≤ nextTag := by
  intro hfix
  induction fuel generalizing ctx pureGuard guardOpt pc mem tag nextLoc nextTag with
  | zero => simp [runWhileFixpoint] at hfix
  | succ fuel' ih =>
    simp [runWhileFixpoint, bind, Except.bind] at hfix
    set ctxForGuard : TypeContext := if pureGuard then { ctx with pureCtx := true } else ctx with hctxForGuard
    rcases hguard : typecheckExpr ctxForGuard e1 fuel' with _ | ⟨guardRes⟩
    · simp [hguard] at hfix
    · simp [hguard] at hfix
      rcases hq1 : guardRes.qualType with ⟨etyp1, p1, pred1⟩
      simp [hq1] at hfix
      by_cases hbool : etyp1 != ETyp.bool
      · simp at hbool; simp [hbool] at hfix
      · simp at hbool; simp [hbool] at hfix
        rcases hbody : typecheckExpr _ e2 fuel' with _ | ⟨bodyRes⟩
        · simp [pure, Except.pure] at hfix
          erw [hbody] at hfix
          simp at hfix
        · simp [hbody] at hfix
          rcases hq2 : bodyRes.qualType with ⟨etyp2, p2, pred2⟩
          simp [hq2] at hfix
          by_cases hunit : etyp2 != ETyp.unit
          · simp at hunit; simp [hunit] at hfix
            simp [pure, Except.pure] at hfix
          · simp at hunit; simp [hunit] at hfix
            have htc_guard : typecheck ctxForGuard e1 fuel' = .ok guardRes := by
              simpa [typecheck] using hguard
            have hguard_nextTag : ctxForGuard.nextTag ≤ guardRes.nextTag' :=
              IH fuel' (lt_add_one fuel') e1 ctxForGuard guardRes htc_guard
            have hctx_nextTag_le : ctx.nextTag ≤ guardRes.nextTag' := by
              have hctxForGuard_nextTag : ctxForGuard.nextTag = ctx.nextTag := by
                cases pureGuard <;> simp [hctxForGuard]
              simpa [hctxForGuard_nextTag] using hguard_nextTag
            set bodyPcCtx : TypeContext := { ctx with pc := joinPoison ctx.pc p1 } with hbodyPcCtx
            set bodyTagEnv : TagEnv := if pureGuard then ctx.tagEnv else guardRes.tagEnv' with hbodyTagEnv
            set bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv } with hbodyEnvCtx
            set bodyCtxBase : TypeContext := { bodyEnvCtx with nextLoc := guardRes.nextLoc', nextTag := guardRes.nextTag', pureCtx := ctx.pureCtx } with hbodyCtxBase
            set bodyCtx : TypeContext :=
              match guardOpt with
              | some (k, deps) => { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
              | none => bodyCtxBase with hbodyCtx
            have htc_body : typecheck bodyCtx e2 fuel' = .ok bodyRes := by
              simp [typecheck, bodyCtx]
              cases guardOpt <;> simp at hbody <;> simp <;> apply hbody
            have hbody_nextTag : bodyCtx.nextTag ≤ bodyRes.nextTag' :=
              IH fuel' (lt_add_one fuel') e2 bodyCtx bodyRes htc_body
            have hctx_body_nextTag : ctx.nextTag ≤ bodyRes.nextTag' := by
              have hbodyCtx_nextTag : bodyCtx.nextTag = guardRes.nextTag' := by
                cases guardOpt <;> simp [hbodyCtx, hbodyCtxBase]
              calc
                ctx.nextTag ≤ guardRes.nextTag' := hctx_nextTag_le
                _ = bodyCtx.nextTag := hbodyCtx_nextTag.symm
                _ ≤ bodyRes.nextTag' := hbody_nextTag
            set newPc : Poison := joinPoison ctx.pc p2 with hnewPc
            set restrictedBodyEnv : MemoryTypeEnv := restrictMemEnv bodyRes.memEnv' ctx.memEnv with hrestrictedBodyEnv
            set newMemEnv : MemoryTypeEnv := joinMemEnvs ctx.memEnv restrictedBodyEnv with hnewMemEnv
            set newTagEnv : TagEnv := joinTagEnvs ctx.tagEnv bodyRes.tagEnv' with hnewTagEnv
            by_cases hfixpoint : newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv
            · simp at hfixpoint
              simp [if_pos hfixpoint] at hfix
              simp [pure, Except.pure] at hfix
              rcases hfix with ⟨_, _, _, _, hfix⟩
              subst nextTag
              apply hctx_body_nextTag
            · simp [pure, Except.pure] at hfix
              rw [if_neg (by simpa using hfixpoint)] at hfix
              set nextCtx : TypeContext :=
                { ctx with pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' } with hnextCtx
              have hnextCtx_nextTag : nextCtx.nextTag = bodyRes.nextTag' := by
                simp [hnextCtx]
              have ih' : nextCtx.nextTag ≤ nextTag := by
                apply ih _ _ _ _ _ _ _ _ _ hfix
                intros fuel'' hfuel'' expr tc r htc
                apply IH fuel'' (by linarith) expr tc r htc
              calc
                ctx.nextTag ≤ bodyRes.nextTag' := hctx_body_nextTag
                _ = nextCtx.nextTag := hnextCtx_nextTag.symm
                _ ≤ nextTag := ih'

private lemma typecheckWhile_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckWhile ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckWhile at htc; simp at htc
  | succ fuel' =>
      unfold typecheckWhile at htc
      cases hguard : matchGuard e1 ctx.memEnv ctx.varEnv with
      | ok g =>
          rcases g with ⟨k, deps⟩
          simp [hguard] at htc
          cases fuel' with
          | zero => simp [typecheckWhileDepoison] at htc
          | succ fuel'' =>
              simp [typecheckWhileDepoison, bind, Except.bind] at htc
              cases hfix :
                  runWhileFixpoint ctx e1 e2 fuel'' true (some (k, deps)) with
              | error err =>
                  simp [hfix] at htc
              | ok r =>
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_nextTag_mono ctx e1 e2 fuel'' true (some (k, deps))
                        finalPc finalMemEnv finalTagEnv finalNextLoc finalNextTag _ hfix
                  intros fuel hfuel expr ctx res hctx
                  apply IH fuel (by linarith) expr ctx res hctx
      | error err =>
          simp [hguard] at htc
          cases fuel' with
          | zero => simp [typecheckWhileStd] at htc
          | succ fuel'' =>
              simp [typecheckWhileStd, bind, Except.bind] at htc
              cases hfix : runWhileFixpoint ctx e1 e2 fuel'' false none with
              | error err => simp [hfix] at htc
              | ok r =>
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_nextTag_mono ctx e1 e2 fuel'' false none
                        finalPc finalMemEnv finalTagEnv finalNextLoc finalNextTag _ hfix
                  intros fuel hfuel expr ctx r hctx
                  apply IH fuel (by linarith) expr ctx r hctx

private lemma typecheckRand_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckRand ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckRand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hetyp, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckRand at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckFrand_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckFrand ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  -- Use the structure lemma to extract the intermediate result
  have hstruct := typecheckFrand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, hnexttag, _hetyp, _hpoison, _hguard⟩
  -- Apply the IH to the subexpression
  cases fuel with
  | zero =>
      unfold typecheckFrand at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      -- htc1 says: typecheckExpr ctx e (succ fuel' - 1) = ok result1
      -- which simplifies to: typecheckExpr ctx e fuel' = ok result1
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by
        simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      -- Now we have: ctx.nextTag ≤ result1.nextTag' and res.nextTag' = result1.nextTag' + 1
      have h_lt : ctx.nextTag < res.nextTag' := by
        calc ctx.nextTag
          _ ≤ result1.nextTag' := IH1
          _ < result1.nextTag' + 1 := Nat.lt_succ_self result1.nextTag'
          _ = res.nextTag' := by rw [← hnexttag]
      exact Nat.le_of_lt h_lt

private lemma typecheckPrintInt_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckPrintInt ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckPrintInt_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckPrintInt at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckPrintString_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckPrintString ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckPrintString_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckPrintString at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

private lemma typecheckUnaryOp_nextTag_mono (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckUnaryOp ctx op e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckUnaryOp_structure ctx op e fuel res htc
  rcases hstruct with ⟨result1, _result_etyp, htc1, _hop, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckUnaryOp at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextTag
        _ ≤ result1.nextTag' := IH1
        _ = res.nextTag' := hnexttag.symm

-- Helper lemma for typecheckExternVal: always preserves nextTag
lemma typecheckExternVal_preserves_nextTag (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (res : TypeResult) :
  typecheckExternVal ctx typ poison pred = .ok res →
  res.nextTag' = ctx.nextTag := by
  intro htc
  unfold typecheckExternVal at htc
  split at htc
  · -- error case: clean types cannot have predicates
    simp at htc
  · -- error case: clean types cannot have predicates (second pattern)
    simp at htc
  · -- success case
    simp [bind, Except.bind] at htc
    cases h : surfaceSpecToQTyp typ poison pred ctx.varEnv ctx with
    | error _ => simp [h] at htc
    | ok result =>
        simp [h, pure, Except.pure] at htc
        cases htc
        rfl

-- Helper lemma for typecheckExternFn: always preserves nextTag
lemma typecheckExternFn_preserves_nextTag (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) (res : TypeResult) :
  typecheckExternFn ctx arg argTyp retSpec effects = .ok res →
  res.nextTag' = ctx.nextTag := by
  intro htc
  unfold typecheckExternFn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

-- Helper lemma for typecheckExternPfn: always preserves nextTag
lemma typecheckExternPfn_preserves_nextTag (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (res : TypeResult) :
  typecheckExternPfn ctx arg argTyp retSpec = .ok res →
  res.nextTag' = ctx.nextTag := by
  intro htc
  unfold typecheckExternPfn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

private lemma typecheck_nextTag_mono_main : ∀ (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult),
  typecheck ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro ctx e fuel res htc
  revert ctx e res htc
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res htc
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag' := by
      intro m h_lt e' ctx' res' htc'
      exact IH m h_lt ctx' e' res' htc'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc
        simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheck ctx' e m = .ok res' →
          ctx'.nextTag ≤ res'.nextTag' := by
          intro m h_lt e' ctx' res' htc'
          have h_lt' : m < fuel' + 1 := Nat.lt_of_lt_of_le h_lt (Nat.le_succ fuel')
          exact IH_converted m h_lt' e' ctx' res' htc'
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp at htc
            injection htc with h_eq
            subst h_eq
            exact le_rfl
        | bool _b =>
            unfold typecheckBool at htc
            simp at htc
            injection htc with h_eq
            subst h_eq
            exact le_rfl
        | unit =>
            unfold typecheckUnit at htc
            simp at htc
            injection htc with h_eq
            subst h_eq
            exact le_rfl
        | str _s =>
            unfold typecheckString at htc
            simp at htc
            injection htc with h_eq
            subst h_eq
            exact le_rfl
        | var x =>
            simp at htc
            exact typecheckVar_nextTag_mono ctx x res htc
        | fn x st1 body st2 =>
            unfold typecheckFn at htc
            simp at htc
            injection htc with h_eq
            subst h_eq
            exact le_rfl
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [Bind.bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ =>
                simp [h_topexpr] at htc
            | ok _ =>
                simp [h_topexpr] at htc
                injection htc with h_eq
                subst h_eq
                exact le_rfl
        | externVal typ poison pred =>
            -- typecheckExternVal returns nextTag' := ctx.nextTag
            simp at htc
            have h_preserve := typecheckExternVal_preserves_nextTag ctx typ poison pred res htc
            rw [h_preserve]
        | externFn arg argTyp retSpec effects =>
            -- typecheckExternFn returns nextTag' := ctx.nextTag
            simp at htc
            have h_preserve := typecheckExternFn_preserves_nextTag ctx arg argTyp retSpec effects res htc
            rw [h_preserve]
        | externPfn arg argTyp retSpec =>
            -- typecheckExternPfn returns nextTag' := ctx.nextTag
            simp at htc
            have h_preserve := typecheckExternPfn_preserves_nextTag ctx arg argTyp retSpec res htc
            rw [h_preserve]
        | op e1 op e2 =>
            simp at htc
            exact typecheckOp_nextTag_mono ctx e1 e2 fuel' op res IH_fuel' htc
        | unaryop op e1 =>
            simp at htc
            exact typecheckUnaryOp_nextTag_mono ctx op e1 fuel' res IH_fuel' htc
        | ite e1 e2 e3 =>
            simp at htc
            exact typecheckIf_nextTag_mono ctx e1 e2 e3 fuel' res IH_fuel' htc
        | newRef e1 =>
            simp at htc
            exact typecheckNewRef_nextTag_mono ctx e1 fuel' res IH_fuel' htc
        | assign e1 e2 =>
            simp at htc
            exact typecheckAssign_nextTag_mono ctx e1 e2 fuel' res IH_fuel' htc
        | deref e1 =>
            simp at htc
            exact typecheckDeref_nextTag_mono ctx e1 fuel' res IH_fuel' htc
        | seq e1 e2 =>
            simp at htc
            exact typecheckSeq_nextTag_mono ctx e1 e2 fuel' res IH_fuel' htc
        | vlet x e1 e2 =>
            simp at htc
            exact typecheckVlet_nextTag_mono ctx x e1 e2 fuel' res IH_fuel' htc
        | app e1 e2 =>
            simp at htc
            exact typecheckApp_nextTag_mono ctx e1 e2 fuel' res IH_fuel' htc
        | kwhile e1 e2 =>
            simp at htc
            exact typecheckWhile_nextTag_mono ctx e1 e2 fuel' res IH_fuel' htc
        | rand e1 =>
            simp at htc
            exact typecheckRand_nextTag_mono ctx e1 fuel' res IH_fuel' htc
        | frand e1 =>
            simp at htc
            exact typecheckFrand_nextTag_mono ctx e1 fuel' res IH_fuel' htc
        | printInt e1 =>
            simp at htc
            exact typecheckPrintInt_nextTag_mono ctx e1 fuel' res IH_fuel' htc
        | printString e1 =>
            simp at htc
            exact typecheckPrintString_nextTag_mono ctx e1 fuel' res IH_fuel' htc

end typecheck_nextTag_mono_proof

-- ================================================================

-- `nextTag` is monotone for successful typechecking: typing never decreases the fresh-tag supply.
--
-- This is used by FR/NI developments to show that tags freshly generated by typing (e.g. in `frand`)
-- lie at or above the current context's `nextTag`.
lemma typecheck_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  exact typecheck_nextTag_mono_main ctx e fuel res htc

-- `nextLoc` is monotone for successful typechecking: typing never decreases the fresh-location supply.
-- This is analogous to typecheck_nextTag_mono but for memory locations.
lemma typecheck_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  -- TODO: This follows the same pattern as typecheck_nextTag_mono
  -- Each typing rule either preserves or increases nextLoc
  sorry

-- Typecheck produces well-formed results if input context is well-formed.
-- This is a key property: typing never introduces locations beyond nextLoc.
-- The proof requires induction over typecheck, showing each rule either:
-- (1) preserves locations from the input context (which are < ctx.nextLoc ≤ res.nextLoc')
-- (2) allocates new locations using nextLoc values (which are < res.nextLoc' by construction)
lemma typecheck_wfTypeResult (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  wfTypeContext ctx → typecheck ctx e fuel = .ok res → wfTypeResult res := by
  -- TODO: Prove by induction on typecheck, similar pattern to typecheck_nextLoc_mono
  sorry

-- ================================================================
-- joinPoison Properties
-- ================================================================

/-- If joinPoison returns false, both inputs must be false. -/
lemma joinPoison_eq_false {p1 p2 : Poison} :
  joinPoison p1 p2 = false → p1 = false ∧ p2 = false := by
  intro h
  cases p1 <;> cases p2
  all_goals simp [joinPoison] at h ⊢

/-- If the left input is true, joinPoison returns true. -/
lemma joinPoison_true_left {p1 p2 : Poison} :
  p1 = true → joinPoison p1 p2 = true := by
  intro h; cases p1 <;> cases p2 <;> simp [joinPoison] at h ⊢

/-- If the right input is true, joinPoison returns true. -/
lemma joinPoison_true_right {p1 p2 : Poison} :
  p2 = true → joinPoison p1 p2 = true := by
  intro h; cases p1 <;> cases p2 <;> simp [joinPoison] at h ⊢

-- ================================================================
-- joinETyps Properties
-- ================================================================

/-- joinETyps preserves non-function property from first argument
    when first argument is not an arrow or ref type. -/
lemma joinETyps_isFunctionType_false_of_left {t1 t2 : ETyp} {p1 p2 : Poison} :
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    (joinETyps t1 t2 p1 p2).isFunctionType = false := by
  intro hnotfun hnotref
  unfold joinETyps
  cases t1 with
  | bool | int | unit | string => simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  | ref inner ls =>
      -- Contradiction: t1 is ref
      exfalso
      exact hnotref ⟨inner, ls, rfl⟩
  | arrow _ _ _ _ | parrow _ _ _ _ =>
      -- Contradiction: t1 is function type
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun

/-- joinETyps preserves non-ref property from first argument
    when first argument is not an arrow or ref type. -/
lemma joinETyps_notRef_of_left_simple {t1 t2 : ETyp} {p1 p2 : Poison} :
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    ¬ (∃ inner ls, (joinETyps t1 t2 p1 p2) = ETyp.ref inner ls) := by
  intro hnotfun hnotref
  unfold joinETyps
  cases t1 with
  | bool => simp
  | int => simp
  | unit => simp
  | string => simp
  | ref inner ls =>
      exfalso
      exact hnotref ⟨inner, ls, rfl⟩
  | arrow _ _ _ _ | parrow _ _ _ _ =>
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hnotfun

/-- joinETyps preserves non-function property when BOTH args are non-function/non-ref. -/
lemma joinETyps_isFunctionType_false_of_both {t1 t2 : ETyp} {p1 p2 : Poison} :
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    t2.isFunctionType = false → ¬ (∃ inner ls, t2 = ETyp.ref inner ls) →
    (joinETyps t1 t2 p1 p2).isFunctionType = false := by
  intro hnotfun1 hnotref1 _ _
  -- Uses the left version since joinETyps returns left for simple types
  exact joinETyps_isFunctionType_false_of_left hnotfun1 hnotref1

/-- joinETyps preserves non-ref property when BOTH args are non-function/non-ref. -/
lemma joinETyps_notRef_of_both_simple {t1 t2 : ETyp} {p1 p2 : Poison} :
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    t2.isFunctionType = false → ¬ (∃ inner ls, t2 = ETyp.ref inner ls) →
    ¬ (∃ inner ls, (joinETyps t1 t2 p1 p2) = ETyp.ref inner ls) := by
  intro hnotfun1 hnotref1 _ _
  exact joinETyps_notRef_of_left_simple hnotfun1 hnotref1

/-- When t2 is non-function/non-ref and joinETyps result is non-function/non-ref,
    it follows from t1 also being non-function/non-ref. -/
lemma joinETyps_isFunctionType_false_of_right {t1 t2 : ETyp} {p1 p2 : Poison} :
    t2.isFunctionType = false → ¬ (∃ inner ls, t2 = ETyp.ref inner ls) →
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    (joinETyps t1 t2 p1 p2).isFunctionType = false := by
  intro _ _ hnotfun1 hnotref1
  exact joinETyps_isFunctionType_false_of_left hnotfun1 hnotref1

/-- When t2 is non-function/non-ref and joinETyps result is non-ref,
    it follows from t1 also being non-function/non-ref. -/
lemma joinETyps_notRef_of_right_simple {t1 t2 : ETyp} {p1 p2 : Poison} :
    t2.isFunctionType = false → ¬ (∃ inner ls, t2 = ETyp.ref inner ls) →
    t1.isFunctionType = false → ¬ (∃ inner ls, t1 = ETyp.ref inner ls) →
    ¬ (∃ inner ls, (joinETyps t1 t2 p1 p2) = ETyp.ref inner ls) := by
  intro _ _ hnotfun1 hnotref1
  exact joinETyps_notRef_of_left_simple hnotfun1 hnotref1

/-- Helper: adding unique elements preserves membership from accumulator. -/
private lemma foldl_addUnique_mem_of_acc {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (acc : List α) (x : α) :
    x ∈ acc → x ∈ xs.foldl (fun acc' y => if acc'.contains y then acc' else acc' ++ [y]) acc := by
  intro hmem
  induction xs generalizing acc with
  | nil => exact hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases hc : acc.contains hd
    · simp only [hc, ↓reduceIte]
      exact ih acc hmem
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ih (acc ++ [hd]) (List.mem_append_left [hd] hmem)

/-- Helper: adding unique elements from a list preserves membership from input. -/
private lemma foldl_addUnique_mem_of_input {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (acc : List α) (x : α) :
    x ∈ xs → x ∈ xs.foldl (fun acc' y => if acc'.contains y then acc' else acc' ++ [y]) acc := by
  intro hmem
  induction xs generalizing acc with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      by_cases hc : acc.contains x
      · simp only [hc, ↓reduceIte]
        exact foldl_addUnique_mem_of_acc tl acc x (List.mem_of_elem_eq_true hc)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        have hmem_append : x ∈ acc ++ [x] := List.mem_append_right acc (List.mem_singleton_self x)
        exact foldl_addUnique_mem_of_acc tl (acc ++ [x]) x hmem_append
    | inr hmem_tl =>
      by_cases hc : acc.contains hd
      · simp only [hc, ↓reduceIte]
        exact ih acc hmem_tl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ih (acc ++ [hd]) hmem_tl

/-- mergeFnTClosures preserves membership from the left list. -/
lemma mem_mergeFnTClosures_left (tcls1 tcls2 : List FnTClosure) (tcl : FnTClosure) :
    tcl ∈ tcls1 → tcl ∈ mergeFnTClosures tcls1 tcls2 := by
  intro hmem
  simp only [mergeFnTClosures]
  -- First show tcl is in the result of processing tcls1
  have h1 : tcl ∈ tcls1.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [] :=
    foldl_addUnique_mem_of_input tcls1 [] tcl hmem
  -- Then show it's preserved when processing tcls2
  exact foldl_addUnique_mem_of_acc tcls2 _ tcl h1

/-- mergeFnTClosures preserves membership from the right list. -/
lemma mem_mergeFnTClosures_right (tcls1 tcls2 : List FnTClosure) (tcl : FnTClosure) :
    tcl ∈ tcls2 → tcl ∈ mergeFnTClosures tcls1 tcls2 := by
  intro hmem
  simp only [mergeFnTClosures]
  -- tcl is in tcls2, and the outer foldl processes tcls2
  exact foldl_addUnique_mem_of_input tcls2 _ tcl hmem

/-- mergePFnTClosures preserves membership from the left list. -/
lemma mem_mergePFnTClosures_left (tcls1 tcls2 : List PFnTClosure) (tcl : PFnTClosure) :
    tcl ∈ tcls1 → tcl ∈ mergePFnTClosures tcls1 tcls2 := by
  intro hmem
  simp only [mergePFnTClosures]
  have h1 : tcl ∈ tcls1.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) [] :=
    foldl_addUnique_mem_of_input tcls1 [] tcl hmem
  exact foldl_addUnique_mem_of_acc tcls2 _ tcl h1

/-- mergePFnTClosures preserves membership from the right list. -/
lemma mem_mergePFnTClosures_right (tcls1 tcls2 : List PFnTClosure) (tcl : PFnTClosure) :
    tcl ∈ tcls2 → tcl ∈ mergePFnTClosures tcls1 tcls2 := by
  intro hmem
  simp only [mergePFnTClosures]
  exact foldl_addUnique_mem_of_input tcls2 _ tcl hmem

/-- joinETyps for arrow types with compatible signatures produces an arrow type
    with merged closures. -/
lemma joinETyps_arrow_structure {st1 st2 : Typ} {p1 : Poison} {tcls1 : List FnTClosure}
    {t2 : ETyp} {p1' p2' : Poison} :
    t2.isArrow →
    beqETypSignature (ETyp.arrow st1 st2 p1 tcls1) t2 →
    ∃ (p' : Poison) (tcls' : List FnTClosure),
      joinETyps (ETyp.arrow st1 st2 p1 tcls1) t2 p1' p2' = ETyp.arrow st1 st2 p' tcls' ∧
      (∀ tcl, tcl ∈ tcls1 → tcl ∈ tcls') := by
  intro hisArrow hcompat
  cases t2 with
  | arrow st1' st2' p2 tcls2 =>
    simp only [joinETyps]
    by_cases heq : st1 == st1' && st2 == st2'
    · simp only [heq, ↓reduceIte]
      refine ⟨joinPoison p1 p2, mergeFnTClosures tcls1 tcls2, rfl, ?_⟩
      intro tcl hmem
      exact mem_mergeFnTClosures_left tcls1 tcls2 tcl hmem
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      refine ⟨p1, tcls1, rfl, ?_⟩
      intro _ h; exact h
  | _ => simp [ETyp.isArrow] at hisArrow

/-- joinETyps for parrow types with compatible signatures produces a parrow type
    with merged closures. -/
lemma joinETyps_parrow_structure {st1 st2 : Typ} {p1 : Poison} {tcls1 : List PFnTClosure}
    {t2 : ETyp} {p1' p2' : Poison} :
    t2.isParrow →
    beqETypSignature (ETyp.parrow st1 st2 p1 tcls1) t2 →
    ∃ (p' : Poison) (tcls' : List PFnTClosure),
      joinETyps (ETyp.parrow st1 st2 p1 tcls1) t2 p1' p2' = ETyp.parrow st1 st2 p' tcls' ∧
      (∀ tcl, tcl ∈ tcls1 → tcl ∈ tcls') := by
  intro hisParrow hcompat
  cases t2 with
  | parrow st1' st2' p2 tcls2 =>
    simp only [joinETyps]
    by_cases heq : st1 == st1' && st2 == st2'
    · simp only [heq, ↓reduceIte]
      refine ⟨joinPoison p1 p2, mergePFnTClosures tcls1 tcls2, rfl, ?_⟩
      intro tcl hmem
      exact mem_mergePFnTClosures_left tcls1 tcls2 tcl hmem
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      refine ⟨p1, tcls1, rfl, ?_⟩
      intro _ h; exact h
  | _ => simp [ETyp.isParrow] at hisParrow

/-- joinETyps for ref types with compatible signatures produces a ref type. -/
lemma joinETyps_ref_structure {inner : ETyp} {ls1 : LocSet} {t2 : ETyp} {p1' p2' : Poison} :
    (∃ inner2 ls2, t2 = ETyp.ref inner2 ls2) →
    beqETypSignature (ETyp.ref inner ls1) t2 →
    ∃ ls', joinETyps (ETyp.ref inner ls1) t2 p1' p2' = ETyp.ref inner ls' := by
  intro ⟨inner2, ls2, ht2⟩ hcompat
  subst ht2
  simp only [joinETyps]
  by_cases heq : beqETypSignature inner inner2
  · simp [heq]
  · simp [heq]

-- ================================================================
-- joinMemEnvs Properties
-- ================================================================

/-- joinMemEnvs contains all locations from the left input. -/
lemma joinMemEnvs_contains_left (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1.contains l → (joinMemEnvs env1 env2).contains l := by
  -- joinMemEnvs combines env1 and env2, keeping all locations from both
  -- When l is in env1:
  -- - If l is also in env2, the join uses the merge function which produces some value
  -- - If l is only in env1, the join keeps env1's value
  -- In both cases, l is in the result
  -- The proof requires going through combineExtTreeMaps machinery
  sorry

/-- joinMemEnvs contains all locations from the right input. -/
lemma joinMemEnvs_contains_right (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env2.contains l → (joinMemEnvs env1 env2).contains l := by
  sorry

/-- If a location is in joinMemEnvs, it was in at least one of the inputs. -/
lemma joinMemEnvs_contains_implies_or (env1 env2 : MemoryTypeEnv) (l : Loc) :
  (joinMemEnvs env1 env2).contains l → env1.contains l ∨ env2.contains l := by
  intro hcontains
  have hmem : l ∈ (joinMemEnvs env1 env2) := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
  simp only [joinMemEnvs, Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
  by_cases h1 : env1.contains l
  · left; exact h1
  · by_cases h2 : env2.contains l
    · right; exact h2
    · exfalso
      have h1' : env1[l]? = none := Std.ExtTreeMap.getElem?_eq_none ((Std.ExtTreeMap.contains_iff_mem).not.1 h1)
      have h2' : env2[l]? = none := Std.ExtTreeMap.getElem?_eq_none ((Std.ExtTreeMap.contains_iff_mem).not.1 h2)
      simp only [joinMemEnvs] at hcontains
      -- The combining function produces none when both inputs are none
      sorry

/-- If a clean type is in joinMemEnvs and the left input has something at that location,
    then the left input's type is also clean (since joinPoison false = requires both false). -/
lemma joinMemEnvs_lookup_clean_left (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (joinMemEnvs env1 env2).lookup l = some qt →
  qt.poison = false →
  env1.lookup l ≠ none →
  ∃ qt1, env1.lookup l = some qt1 ∧ qt1.etyp = qt.etyp ∧ qt1.poison = false := by
  -- From joinMemEnvs definition: if result has qt with poison=false,
  -- and env1 has something at l, the input from env1 must also have poison=false
  -- (since joinPoison p1 p2 = false implies p1 = false)
  sorry

/-- wfTypeContext property is preserved under joinMemEnvs with max nextLoc. -/
lemma wfTypeContext_joinMemEnvs_max
  (env1 env2 : MemoryTypeEnv) (nl1 nl2 : Nat)
  (hwf1 : ∀ l, env1.contains l → l < nl1)
  (hwf2 : ∀ l, env2.contains l → l < nl2) :
  ∀ l, (joinMemEnvs env1 env2).contains l → l < max nl1 nl2 := by
  intro l hcontains
  have hor := joinMemEnvs_contains_implies_or env1 env2 l hcontains
  cases hor with
  | inl h1 =>
    have hlt1 : l < nl1 := hwf1 l h1
    exact Nat.lt_of_lt_of_le hlt1 (Nat.le_max_left nl1 nl2)
  | inr h2 =>
    have hlt2 : l < nl2 := hwf2 l h2
    exact Nat.lt_of_lt_of_le hlt2 (Nat.le_max_right nl1 nl2)
