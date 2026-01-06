-- Common type safety definitions for the Poison Language
--
-- This file contains shared definitions used by both Progress and Preservation
-- properties, including evaluation relations and runtime context instantiation.

import LeanPoison.Syntax
import LeanProofs.Equality
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
lemma typecheckSeq_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.qualType.poison = joinPoison result1.qualType.poison result2.qualType.poison ∧
    res.qualType.pred = result2.qualType.pred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckSeq] at h_typecheck
  | succ fuel' =>
      unfold typecheckSeq at h_typecheck
      simp at h_typecheck
      simp [bind, Except.bind] at h_typecheck
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | ok result1 =>
          simp [h_tc1] at h_typecheck
          cases h_qt1 : result1.qualType with
          | mk _etyp1 p1 pred1 =>
              rw [h_qt1] at h_typecheck
              simp at h_typecheck
              cases h_tc2 :
                (typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                             nextLoc := result1.nextLoc', nextTag := result1.nextTag' } e2 fuel') with
              | ok result2 =>
                  simp (config := { failIfUnchanged := false }) [h_tc2] at h_typecheck
                  cases h_qt2 : result2.qualType with
                  | mk _etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      simp [pure, Except.pure] at h_typecheck
                      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                              nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
                      cases h_typecheck
                      refine ⟨result1, result2, ctx', ?_⟩
                      simp [ctx', h_tc1, h_tc2, h_qt1, h_qt2]
              | error _err =>
                  simp (config := { failIfUnchanged := false }) [h_tc2] at h_typecheck
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


-- Extract the guard tag from a qualified type's predicate, if present.
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

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
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _hetyp, _hmem, _htag, _hloc, hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckSeq at htc; simp at htc
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

-- Helper lemma for typecheckIf: preserves nextTag' from max of result2 and result3
lemma typecheckIf_preserves_nextTag (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckIf ctx e1 e2 e3 fuel = .ok res →
  ∃ (result1 result2 result3 : TypeResult),
    res.nextTag' = max result2.nextTag' result3.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckIf at htc; simp at htc
  | succ fuel' => sorry  -- Detailed proof requires case analysis of both if_depoison and if_std branches

private lemma typecheckIf_nextTag_mono (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckIf ctx e1 e2 e3 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckIf at htc; simp at htc
  | succ fuel' => sorry  -- Complex proof due to two branches and matchGuard

-- Helper lemma for typecheckApp: preserves nextTag' from result2
lemma typecheckApp_preserves_nextTag (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckApp ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.nextTag' = result2.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckApp at htc; simp at htc
  | succ fuel' => sorry  -- Detailed proof requires case analysis

private lemma typecheckApp_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckApp ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  have hstruct := typecheckApp_preserves_nextTag ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, hnexttag⟩
  cases fuel with
  | zero => unfold typecheckApp at htc; simp at htc
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

private lemma typecheckWhile_nextTag_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckWhile ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckWhile at htc; simp at htc
  | succ fuel' => sorry  -- Complex proof involving runWhileFixpoint

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
