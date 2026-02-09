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
import Init.Data.List.Lemmas
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
-- particular execution's heap layout.
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
    This predicate can be extended with additional conditions as needed. -/
def wfRealizationMap (θ : RealizationMap) : Prop :=
  θ.isInjective

/-- θ₁ is a well-formed extension of θ₀: it agrees on existing locations
    and preserves injectivity (if θ₀ is injective, so is θ₁).
    This captures that extending a realisation map during evaluation
    preserves well-formedness. -/
def wfExtendsMap (θ₀ θ₁ : RealizationMap) : Prop :=
  θ₀.extendsMap θ₁ ∧ (wfRealizationMap θ₀ → wfRealizationMap θ₁)

-- Proof-level typing relation for runtime values.
--
-- For `ref` types, the concrete address must be the realisation (via `θ`) of some
-- logical location in the `LocSet` annotation.
inductive valueHasETyp (θ : RealizationMap) : Value → ETyp → Prop where
  | num (n): valueHasETyp θ (Value.num n) ETyp.int
  | bool (b): valueHasETyp θ (Value.bool b) ETyp.bool
  | unit : valueHasETyp θ Value.unit ETyp.unit
  | str (s): valueHasETyp θ (Value.str s) ETyp.string
  | loc {a : Address} {t : ETyp} {ls : LocSet} {l : Loc}
      (hlookup : θ.lookup l = some a)
      (hin : l ∈ ls) :
      valueHasETyp θ (Value.loc a) (ETyp.ref t ls)
  | closure {x e env st1 st2 p tcl} {tenv : CapturedVarEnv}
      (htcl : FnTClosure.regular x e tenv ∈ tcl)
      (henv : ∀ y qt v, tenv.lookup y = some qt →
        env.lookup y = some v → valueHasETyp θ v qt.etyp) :
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure {x body env st1 st2 p tcl} {pbody : PExpr} {tenv : CapturedVarEnv}
      (hpure : Expr.toPExpr? body = some pbody)
      (htcl : PFnTClosure.regular x pbody tenv ∈ tcl)
      (henv : ∀ y qt v, tenv.lookup y = some qt →
        env.lookup y = some v → valueHasETyp θ v qt.etyp) :
      valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcl)

-- ================================================================
-- Runtime Context Instantiation
-- ================================================================

-- A predicate for runtime instantiating the context: values must exist for
-- every typed variable and memory must contain entries for each typed
-- location.
--
-- Note on memory type matching: We want heap
-- cells have qualified types matching Γ(l). This is implicitly satisfied because:
-- (1) Memory only stores integers (Memory := HashMap Address Int)
-- (2) Well-typed programs only store values of type int in memory
-- (3) Therefore, for any l ∈ dom(Γ) with θ(l) = a, the value μ(a) : Int
--     matches the stored type Γ(l).etyp which must be ETyp.int.
def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l a, θ.lookup l = some a → ctx.memEnv.contains l ∧ μ.contains a) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt →
     ∃ v, ρ.lookup x = some v ∧ valueHasETyp θ v qt.etyp)

/-- Future-use lemma for preservation proofs:
    when typing joins function closure sets (e.g. branch joins / merged alternatives),
    transport a concrete closure-typing witness to the larger closure list. -/
lemma valueHasETyp_closure_weaken_tcl
    {θ : RealizationMap} {x : Name} {e : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p₁ p₂ : Poison} {tcls₁ tcls₂ : List FnTClosure}
    (h : valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p₁ tcls₁))
    (hsub : ∀ tc, tc ∈ tcls₁ → tc ∈ tcls₂) :
    valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p₂ tcls₂) := by
  cases h with
  | closure htcl henv =>
      exact valueHasETyp.closure (htcl := hsub _ htcl) (henv := henv)

/-- Future-use lemma for preservation proofs:
    pure analogue of `valueHasETyp_closure_weaken_tcl` for joined parrow closure sets. -/
lemma valueHasETyp_peClosure_weaken_tcl
    {θ : RealizationMap} {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p₁ p₂ : Poison} {tcls₁ tcls₂ : List PFnTClosure}
    (h : valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₁ tcls₁))
    (hsub : ∀ tc, tc ∈ tcls₁ → tc ∈ tcls₂) :
    valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₂ tcls₂) := by
  cases h with
  | peClosure hpure htcl henv =>
      exact valueHasETyp.peClosure (hpure := hpure) (htcl := hsub _ htcl) (henv := henv)

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
  { ctx with memEnv := res.memEnv', tagEnv := res.tagEnv', nextLoc := res.nextLoc', nextTag := res.nextTag', regime := res.regime' }

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
    res.regime' = result1.regime' ∧
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
                        nextTag' := result1.nextTag', regime' := result1.regime' } = res := by
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
    res.regime' = result1.regime' ∧
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
                        nextTag' := result1.nextTag', regime' := result1.regime' } = res := by
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
    res.regime' = result1.regime' ∧
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
                  refine ⟨result1, result_etyp, h_tc1_result, h_opEType_final, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
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
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag',
                             regime := result1.regime' } e2 (fuel - 1) = .ok result2 ∧
    opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.regime' = result2.regime' ∧
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
                                          nextLoc := result1.nextLoc', nextTag := result1.nextTag',
                                          regime := result1.regime' } e2 fuel') with
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
                                  rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
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
    ctx' = ({ ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }) ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.qualType.etyp = result2.qualType.etyp ∧
    res.memEnv' = result2.memEnv' ∧
    res.tagEnv' = result2.tagEnv' ∧
    res.nextLoc' = result2.nextLoc' ∧
    res.nextTag' = result2.nextTag' ∧
    res.regime' = result2.regime' ∧
    res.qualType.poison = joinPoison ctx.pc result2.qualType.poison ∧
    res.qualType.pred = result2.qualType.pred := by
  intro h_typecheck
  cases fuel with
  | zero =>
      simp [typecheckVlet] at h_typecheck
  | succ fuel' =>
      unfold typecheckVlet at h_typecheck
      -- Handle the shadowing check match expression
      cases h_shadow : ctx.varEnv.lookup x with
      | none =>
          simp [h_shadow] at h_typecheck
          simp [bind, Except.bind] at h_typecheck
          cases h_tc1 : typecheckExpr ctx e1 fuel' with
          | ok result1 =>
              simp [h_tc1] at h_typecheck
              cases h_tc2 :
                typecheckExpr
                    { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                               tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                    e2 fuel' with
              | ok result2 =>
                  simp [h_tc2] at h_typecheck
                  cases h_qt2 : result2.qualType with
                  | mk _etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      simp [pure, Except.pure] at h_typecheck
                      let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                      cases h_typecheck
                      refine ⟨result1, result2, ctx', ?_⟩
                      simp [ctx', h_tc1, h_tc2, h_qt2]
              | error _err =>
                  simp [h_tc2] at h_typecheck
          | error _err =>
              simp [h_tc1] at h_typecheck
      | some qt_outer =>
          simp [h_shadow] at h_typecheck
          -- Handle the predicate match
          cases h_pred : qt_outer.pred with
          | guardClosure k _ _ _ =>
              simp [h_pred] at h_typecheck
              -- Handle the regime lookup check
              cases h_regime : (ctx.regime.lookup? k).isSome with
              | true =>
                  -- If regime interprets k, shadowing check would have failed, contradiction
                  simp [h_regime] at h_typecheck
                  contradiction
              | false =>
                  simp [h_regime] at h_typecheck
                  simp [bind, Except.bind] at h_typecheck
                  cases h_tc1 : typecheckExpr ctx e1 fuel' with
                  | ok result1 =>
                      simp [h_tc1] at h_typecheck
                      cases h_tc2 :
                        typecheckExpr
                            { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                                       tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                            e2 fuel' with
                      | ok result2 =>
                          simp [h_tc2] at h_typecheck
                          cases h_qt2 : result2.qualType with
                          | mk _etyp2 p2 pred2 =>
                              rw [h_qt2] at h_typecheck
                              simp at h_typecheck
                              simp [pure, Except.pure] at h_typecheck
                              let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                              cases h_typecheck
                              refine ⟨result1, result2, ctx', ?_⟩
                              simp [ctx', h_tc1, h_tc2, h_qt2]
                      | error _err =>
                          simp [h_tc2] at h_typecheck
                  | error _err =>
                      simp [h_tc1] at h_typecheck
          | guardOnly _ =>
              simp [h_pred] at h_typecheck
              simp [bind, Except.bind] at h_typecheck
              cases h_tc1 : typecheckExpr ctx e1 fuel' with
              | ok result1 =>
                  simp [h_tc1] at h_typecheck
                  cases h_tc2 :
                    typecheckExpr
                        { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                                   tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                        e2 fuel' with
                  | ok result2 =>
                      simp [h_tc2] at h_typecheck
                      cases h_qt2 : result2.qualType with
                      | mk _etyp2 p2 pred2 =>
                          rw [h_qt2] at h_typecheck
                          simp at h_typecheck
                          simp [pure, Except.pure] at h_typecheck
                          let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                          cases h_typecheck
                          refine ⟨result1, result2, ctx', ?_⟩
                          simp [ctx', h_tc1, h_tc2, h_qt2]
                  | error _err =>
                      simp [h_tc2] at h_typecheck
              | error _err =>
                  simp [h_tc1] at h_typecheck
          | noPred =>
              simp [h_pred] at h_typecheck
              simp [bind, Except.bind] at h_typecheck
              cases h_tc1 : typecheckExpr ctx e1 fuel' with
              | ok result1 =>
                  simp [h_tc1] at h_typecheck
                  cases h_tc2 :
                    typecheckExpr
                        { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                                   tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                        e2 fuel' with
                  | ok result2 =>
                      simp [h_tc2] at h_typecheck
                      cases h_qt2 : result2.qualType with
                      | mk _etyp2 p2 pred2 =>
                          rw [h_qt2] at h_typecheck
                          simp at h_typecheck
                          simp [pure, Except.pure] at h_typecheck
                          let ctx' := { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType, tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                          cases h_typecheck
                          refine ⟨result1, result2, ctx', ?_⟩
                          simp [ctx', h_tc1, h_tc2, h_qt2]
                  | error _err =>
                      simp [h_tc2] at h_typecheck
              | error _err =>
                  simp [h_tc1] at h_typecheck

-- Helper lemma: extract structure from typecheckNewRef
-- NOTE: Now requires etyp = ETyp.int (heap stores only integers)
lemma typecheckNewRef_structure (ctx : TypeContext) (e1 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckNewRef ctx e1 fuel = .ok res →
  ∃ (result1 : TypeResult) (l : Loc),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    l = result1.nextLoc' ∧
    result1.qualType.etyp = ETyp.int ∧
    res.qualType.etyp = ETyp.ref ETyp.int (LocSet.singleton l) ∧
    res.qualType.poison = ctx.pc ∧
    res.qualType.pred = Predicate.noPred ∧
    res.memEnv' = updateMemEnv result1.memEnv' l ⟨ETyp.int, joinPoison ctx.pc result1.qualType.poison, result1.qualType.pred⟩ ∧
    res.tagEnv' = result1.tagEnv' ∧
    res.nextLoc' = result1.nextLoc' + 1 ∧
    res.nextTag' = result1.nextTag' ∧
    res.regime' = result1.regime' := by
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
        -- The new code checks if etyp = ETyp.int
        split at h_typecheck
        · -- Case: etyp = ETyp.int (the only successful case)
          rename_i h_int
          -- Extract freshTLocRes result
          have h_fresh : (result1.nextLoc', { result1 with nextLoc' := result1.nextLoc' + 1 }) = freshTLocRes result1 := rfl
          -- Simplify the do notation
          simp [pure, Except.pure] at h_typecheck
          -- Extract projections from h_fresh
          have h_fresh1 : (freshTLocRes result1).1 = result1.nextLoc' := by simp [← h_fresh]
          have h_fresh2 : (freshTLocRes result1).2 = { result1 with nextLoc' := result1.nextLoc' + 1 } := by simp [← h_fresh]
          rw [h_fresh1, h_fresh2] at h_typecheck
          simp at h_typecheck
          -- Extract field equalities
          have h_qualType : res.qualType = ⟨ETyp.ref ETyp.int (LocSet.singleton result1.nextLoc'), ctx.pc, Predicate.noPred⟩ := by
            have := congrArg TypeResult.qualType h_typecheck
            simp at this
            exact this.symm
          have h_memEnv : res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ⟨ETyp.int, joinPoison ctx.pc poison, pred⟩ := by
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
          have h_regime : res.regime' = result1.regime' := by
            have := congrArg TypeResult.regime' h_typecheck
            simp at this
            exact this.symm
          have h_etyp : res.qualType.etyp = ETyp.ref ETyp.int (LocSet.singleton result1.nextLoc') := by
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
          -- Construct the existential with the new signature (no etyp, it's always ETyp.int)
          simp only [Nat.add_sub_cancel]
          use result1, result1.nextLoc'
          refine ⟨h_tc1, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- result1.qualType.etyp = ETyp.int
            rw [h_qt1]
            simp
            exact h_int
          · -- res.qualType.etyp = ETyp.ref ETyp.int (LocSet.singleton l)
            exact h_etyp
          · -- res.qualType.poison = ctx.pc
            exact h_poison_eq
          · -- res.qualType.pred = Predicate.noPred
            exact h_pred_eq
          · -- res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc' ...
            rw [h_memEnv, h_qt1]
          · -- res.tagEnv' = result1.tagEnv'
            exact h_tagEnv
          · -- res.nextLoc' = result1.nextLoc' + 1
            exact h_nextLoc
          · -- res.nextTag' = result1.nextTag'
            exact h_nextTag
          · -- res.regime' = result1.regime'
            exact h_regime
        · -- Case: etyp ≠ ETyp.int (error case - contradiction)
          -- Contradiction: mapping over `throw` cannot yield `Except.ok`.
          have h_typecheck' := h_typecheck
          simp [Functor.map, Except.map] at h_typecheck'
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
    typecheckExpr { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' } e1 (fuel - 1) = .ok result1 ∧
    ((isArrow = true ∧
      (∃ (tcls : List FnTClosure), result1.qualType.etyp = ETyp.arrow st1 st2 p tcls) ∧
      result1.qualType.poison = p1 ∧
      (¬ ctx.pureCtx) ∧
      (isSubtype st1 result2.qualType))
     ∨
     (isArrow = false ∧
      (∃ (tcls_p : List PFnTClosure), result1.qualType.etyp = ETyp.parrow st1 st2 p tcls_p) ∧
      result1.qualType.poison = p1 ∧
      (isSubtype st1 result2.qualType))) := by
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
              let ctx' := { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' }
              have h_ctx'_eq : ctx' = { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' } := rfl
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
                          · simp at h_typecheck
                          · next h_notPureCtx =>
                            split at h_typecheck
                            · simp at h_typecheck
                            · next h_notEmpty =>
                              split at h_typecheck
                              · simp at h_typecheck
                              · next h_subtype =>
                                have h_arrow : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls := by
                                  simp [h_qt1]
                                refine ⟨result2, result1, st1, st2, p, p1, true, ?_, ?_, ?_⟩
                                · simpa [Nat.succ_sub_one] using h_tc2_result
                                · simpa [Nat.succ_sub_one] using h_tc1_result
                                · left
                                  constructor
                                  · rfl
                                  constructor
                                  · exact ⟨tcls, h_arrow⟩
                                  constructor
                                  · simp [h_qt1]
                                  constructor
                                  · exact h_notPureCtx
                                  · rw [h_qt2]
                                    simp [h_subtype]
                      | parrow st1 st2 p tcls_p =>
                          simp at h_typecheck
                          split at h_typecheck
                          · simp at h_typecheck
                          · next h_notEmpty =>
                            split at h_typecheck
                            · simp at h_typecheck
                            · next h_subtype =>
                              have h_parrow : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls_p := by
                                simp [h_qt1]
                              refine ⟨result2, result1, st1, st2, p, p1, false, ?_, ?_, ?_⟩
                              · simpa [Nat.succ_sub_one] using h_tc2_result
                              · simpa [Nat.succ_sub_one] using h_tc1_result
                              · right
                                constructor
                                · rfl
                                constructor
                                · exact ⟨tcls_p, h_parrow⟩
                                constructor
                                · simp [h_qt1]
                                · rw [h_qt2]
                                  simp [h_subtype]
                      | _ =>
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
    -- Case disjunction on matchGuard result and regime lookup
    (-- Mode 1: Predicate-based with R(k) = some true (then-branch effective)
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv = .ok (k, deps) ∧
       ctx.regime.lookup? k = some true ∧
       ∃ res1 : TypeResult,
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ res2 : TypeResult,
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           ∃ res3 : TypeResult,
             let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
             let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
             typecheckExpr ctxFalse' e3 (fuel - 1) = .ok res3 ∧
            res.memEnv' = res2.memEnv' ∧
            res.tagEnv' = res2.tagEnv' ∧
            res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
            res.nextTag' = max res2.nextTag' res3.nextTag' ∧
            res.regime' = res2.regime' ∧
            res.qualType.poison = joinPoison ctx.pc res2.qualType.poison ∧
            res.qualType.etyp = res2.qualType.etyp)
    ∨
    (-- Mode 2: Predicate-based with R(k) = some false (else-branch effective)
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv = .ok (k, deps) ∧
       ctx.regime.lookup? k = some false ∧
       ∃ res1 : TypeResult,
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ res2 : TypeResult,
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           ∃ res3 : TypeResult,
             let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
             let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
             typecheckExpr ctxFalse' e3 (fuel - 1) = .ok res3 ∧
            res.memEnv' = res3.memEnv' ∧
            res.tagEnv' = res3.tagEnv' ∧
            res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
            res.nextTag' = max res2.nextTag' res3.nextTag' ∧
            res.regime' = res3.regime' ∧
            res.qualType.poison = joinPoison ctx.pc res3.qualType.poison ∧
            res.qualType.etyp = res3.qualType.etyp)
    ∨
    (-- Mode 3: Predicate-based with R(k) = none (conservative)
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv = .ok (k, deps) ∧
       ctx.regime.lookup? k = none ∧
       ∃ res1 : TypeResult,
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ res2 : TypeResult,
           let branchPc := joinPoison ctx.pc res1.qualType.poison
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           ∃ res3 : TypeResult,
             let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
             let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
             typecheckExpr ctxFalse' e3 (fuel - 1) = .ok res3 ∧
            res.memEnv' = joinMemEnvs res2.memEnv' res3.memEnv' ∧
            res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv' ∧
            res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
            res.nextTag' = max res2.nextTag' res3.nextTag' ∧
            res.regime' = joinRegimes res2.regime' res3.regime' ∧
            res.qualType.poison = joinPoison ctx.pc (joinPoison res1.qualType.poison
                                    (joinPoison res2.qualType.poison res3.qualType.poison)))
   ∨
   (-- Mode 4: Standard (matchGuard fails)
     (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv = .error err) ∧
     ∃ res1 : TypeResult,
       typecheckExpr ctx e1 (fuel - 1) = .ok res1 ∧
       res1.qualType.etyp = ETyp.bool ∧
       ∃ res2 : TypeResult,
         let ctx' := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                                nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
         let pc' := joinPoison ctx.pc res1.qualType.poison
         let ctx'' := { ctx' with pc := pc' }
         typecheckExpr ctx'' e2 (fuel - 1) = .ok res2 ∧
         ∃ res3 : TypeResult,
           let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           typecheckExpr ctxForE3 e3 (fuel - 1) = .ok res3 ∧
          res.memEnv' = joinMemEnvs res2.memEnv' res3.memEnv' ∧
          res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv' ∧
          res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
          res.nextTag' = max res2.nextTag' res3.nextTag' ∧
          res.regime' = joinRegimes res2.regime' res3.regime' ∧
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
      -- Predicate-based: case split on regime.lookup? k
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      cases hregime : ctx.regime.lookup? k with
      | some b =>
        cases b with
        | true =>
          -- Mode 1: R(k) = some true (then-branch effective)
          left
          refine ⟨k, deps, rfl, hregime, ?_⟩
          simp only [hregime] at htc
          cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            refine ⟨result1, rfl, ?_⟩
            match hq1 : result1.qualType with
            | ⟨etyp1, p1, pred1⟩ =>
            simp only [hq1] at htc
            by_cases hbool : etyp1 = ETyp.bool
            · constructor; exact hbool
              simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
              let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
              cases htc2 : typecheckExpr ctxTrue e2 fuel' with
              | error e => rw [htc2] at htc; simp at htc
              | ok result2 =>
                rw [htc2] at htc; simp at htc
                refine ⟨result2, rfl, ?_⟩
                match hq2 : result2.qualType with
                | ⟨etyp2, p2, pred2⟩ =>
                simp only [hq2] at htc
                let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
                cases htc3 : typecheckExpr ctxFalse' e3 fuel' with
                | error e => rw [htc3] at htc; cases htc
                | ok result3 =>
                  rw [htc3] at htc
                  refine ⟨result3, rfl, ?_⟩
                  match hq3 : result3.qualType with
                  | ⟨etyp3, p3, pred3⟩ =>
                  simp only [hq3] at htc
                  by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                  · simp only [hcompat, ↓reduceIte] at htc; cases htc
                  · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                      cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                    simp only [hcompat'] at htc
                    cases htc; simp [*]
            · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
        | false =>
          -- Mode 2: R(k) = some false (else-branch effective)
          right; left
          refine ⟨k, deps, rfl, hregime, ?_⟩
          simp only [hregime] at htc
          cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
          | error e => simp only [htc1] at htc; cases htc
          | ok result1 =>
            simp only [htc1] at htc
            refine ⟨result1, rfl, ?_⟩
            match hq1 : result1.qualType with
            | ⟨etyp1, p1, pred1⟩ =>
            simp only [hq1] at htc
            by_cases hbool : etyp1 = ETyp.bool
            · constructor; exact hbool
              simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
              let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
              cases htc2 : typecheckExpr ctxTrue e2 fuel' with
              | error e => rw [htc2] at htc; simp at htc
              | ok result2 =>
                rw [htc2] at htc; simp at htc
                refine ⟨result2, rfl, ?_⟩
                match hq2 : result2.qualType with
                | ⟨etyp2, p2, pred2⟩ =>
                simp only [hq2] at htc
                let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
                cases htc3 : typecheckExpr ctxFalse' e3 fuel' with
                | error e => rw [htc3] at htc; cases htc
                | ok result3 =>
                  rw [htc3] at htc
                  refine ⟨result3, rfl, ?_⟩
                  match hq3 : result3.qualType with
                  | ⟨etyp3, p3, pred3⟩ =>
                  simp only [hq3] at htc
                  by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                  · simp only [hcompat, ↓reduceIte] at htc; cases htc
                  · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                      cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                    simp only [hcompat'] at htc
                    cases htc; simp [*]
            · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
      | none =>
        -- Mode 3: R(k) = none (conservative)
        right; right; left
        refine ⟨k, deps, rfl, hregime, ?_⟩
        simp only [hregime] at htc
        cases htc1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
        | error e => simp only [htc1] at htc; cases htc
        | ok result1 =>
          simp only [htc1] at htc
          refine ⟨result1, rfl, ?_⟩
          match hq1 : result1.qualType with
          | ⟨etyp1, p1, pred1⟩ =>
          simp only [hq1] at htc
          by_cases hbool : etyp1 = ETyp.bool
          · constructor; exact hbool
            simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
            let branchPc := joinPoison ctx.pc p1
            let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
            cases htc2 : typecheckExpr ctxTrue e2 fuel' with
            | error e => rw [htc2] at htc; simp at htc
            | ok result2 =>
              rw [htc2] at htc; simp at htc
              refine ⟨result2, rfl, ?_⟩
              match hq2 : result2.qualType with
              | ⟨etyp2, p2, pred2⟩ =>
              simp only [hq2] at htc
              let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
              let ctxFalse' := { ctxFalse with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
              cases htc3 : typecheckExpr ctxFalse' e3 fuel' with
              | error e => rw [htc3] at htc; cases htc
              | ok result3 =>
                rw [htc3] at htc
                refine ⟨result3, rfl, ?_⟩
                match hq3 : result3.qualType with
                | ⟨etyp3, p3, pred3⟩ =>
                simp only [hq3] at htc
                by_cases hcompat : beqETypSignature etyp2 etyp3 = false
                · simp only [hcompat, ↓reduceIte] at htc; cases htc
                · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                    cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                  simp only [hcompat'] at htc
                  cases htc; simp [*]
          · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
    | error err =>
      -- Mode 4: Standard (matchGuard fails)
      right; right; right
      simp only [hmatch] at htc
      constructor
      · exact ⟨err, rfl⟩
      cases htc1 : typecheckExpr ctx e1 fuel' with
      | error e => simp only [htc1] at htc; cases htc
      | ok result1 =>
        simp only [htc1] at htc
        refine ⟨result1, rfl, ?_⟩
        match hq1 : result1.qualType with
        | ⟨etyp1, p1, pred1⟩ =>
        simp only [hq1] at htc
        by_cases hbool : etyp1 = ETyp.bool
        · constructor; exact hbool
          simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
          let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
          let pc' := joinPoison ctx.pc p1
          let ctx'' := { ctx' with pc := pc' }
          cases htc2 : typecheckExpr ctx'' e2 fuel' with
          | error e => rw [htc2] at htc; cases htc
          | ok result2 =>
            rw [htc2] at htc
            refine ⟨result2, rfl, ?_⟩
            match hq2 : result2.qualType with
            | ⟨etyp2, p2, pred2⟩ =>
            simp only [hq2] at htc
            let ctxForE3 := { ctx'' with nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
            cases htc3 : typecheckExpr ctxForE3 e3 fuel' with
            | error e => rw [htc3] at htc; cases htc
            | ok result3 =>
              rw [htc3] at htc
              refine ⟨result3, rfl, ?_⟩
              match hq3 : result3.qualType with
              | ⟨etyp3, p3, pred3⟩ =>
              simp only [hq3] at htc
              by_cases hcompat : beqETypSignature etyp2 etyp3 = false
              · simp only [hcompat, Bool.not_eq_true', ↓reduceIte] at htc; cases htc
              · have hcompat' : beqETypSignature etyp2 etyp3 = true := by
                  cases h : beqETypSignature etyp2 etyp3 <;> simp_all
                simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at htc
                rw [← htc]; simp
        · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc

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
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
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
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
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
                            regime := res1.regime', memEnv := res1.memEnv', varEnv := ctx.varEnv,
                            tagEnv := res1.tagEnv', nextLoc := res1.nextLoc',
                            nextTag := res1.nextTag', pureCtx := ctx.pureCtx }
            e2 (fuel - 1) = .ok res2)
    (htc3 : typecheckExpr { pc := joinPoison ctx.pc res1.qualType.poison,
                            regime := res1.regime', memEnv := res1.memEnv', varEnv := ctx.varEnv,
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
                               nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
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
    res.regime' = result1.regime' ∧
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
                        nextTag' := result1.nextTag', regime' := result1.regime' } = res := by
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
    res.regime' = result1.regime' ∧
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
                            nextTag' := result1.nextTag' + 1, regime' := result1.regime' } = res := by
                        cases htc'
                        rfl
                      refine ⟨result1, ?_, ?_⟩
                      · simpa [Nat.succ_sub_one] using htc1
                      · -- remaining field equalities
                        cases h_res
                        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
                        simp [qtypGuardTag]
                  | error msg =>
                      -- If `Expr.toPExpr` failed, `typecheckFrand` would fail.
                      simp [hpb] at htc
      | error msg =>
          simp [htc1] at htc

-- Structure lemma for assign typechecking
-- NOTE: Now requires both reference and RHS to be int type (heap stores only integers)
lemma typecheckAssign_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ls : LocSet),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.ref ETyp.int ls ∧
    typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                             nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' } e2 (fuel - 1) = .ok result2 ∧
    result2.qualType.etyp = ETyp.int ∧
    res.nextLoc' = LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1)) ∧
    res.nextTag' = result2.nextTag' ∧
    res.regime' = invalidateRegimeDeps ctx.regime result2.tagEnv' ls ∧
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
                  -- The code first checks: if t != ETyp.int then throw
                  split at h_typecheck
                  · -- Case: t = ETyp.int (the only successful case)
                    rename_i h_t_int
                    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                           nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                    cases h_tc2 : typecheckExpr ctx' e2 fuel' with
                    | ok result2 =>
                        rw [h_tc2] at h_typecheck
                        simp at h_typecheck
                        cases h_qt2 : result2.qualType with
                        | mk etyp2 p2 pred2 =>
                            rw [h_qt2] at h_typecheck
                            simp at h_typecheck
                            -- The code checks: if etyp2 != ETyp.int then throw
                            split at h_typecheck
                            · -- Case: etyp2 = ETyp.int (the only successful case)
                              rename_i h_etyp2_int
                              simp [pure, Except.pure] at h_typecheck
                              cases h_typecheck
                              simp only [Nat.add_sub_cancel]
                              use result1, result2, ls
                              constructor
                              · exact h_tc1
                              constructor
                              · -- result1.qualType.etyp = ETyp.ref ETyp.int ls
                                rw [h_qt1, h_t_int]
                              constructor
                              · exact h_tc2
                              constructor
                              · -- result2.qualType.etyp = ETyp.int
                                rw [h_qt2]
                                exact h_etyp2_int
                              constructor
                              · rfl  -- res.nextLoc' = LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1)) (proven by cases h_typecheck)
                              constructor
                              · trivial  -- res.nextTag' = result2.nextTag' (proven by cases h_typecheck)
                              constructor
                              · trivial  -- res.regime' = invalidateRegimeDeps ctx.regime result2.tagEnv' ls (proven by cases h_typecheck)
                              constructor
                              · trivial  -- res.qualType.etyp = ETyp.unit (proven by cases h_typecheck)
                              constructor
                              · -- res.qualType.poison = joinPoison ctx.pc p1
                                rw [h_qt1]
                              · trivial  -- res.qualType.pred = Predicate.noPred (proven by cases h_typecheck)
                            · -- Case: etyp2 ≠ ETyp.int (error - contradiction)
                              cases h_typecheck
                    | error _err =>
                        rw [h_tc2] at h_typecheck
                        simp at h_typecheck
                  · -- Case: t ≠ ETyp.int (error - contradiction)
                    cases h_typecheck
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
    res.nextTag' = result1.nextTag' ∧
    res.regime' = result1.regime' := by
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
          --          nextLoc' := result1.nextLoc', nextTag' := result1.nextTag', regime' := result1.regime' }
          -- So we can conclude the result regardless of which branch was taken
          refine ⟨result1, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                -- if t != ETyp.int then throw
                split at h_typecheck
                · -- Case: t = ETyp.int (the only successful case)
                  split at h_typecheck
                  · -- ls.isEmpty - error case
                    contradiction
                  · -- ls not empty - split on foldM result
                    split at h_typecheck
                    · -- foldM error case - contradiction
                      contradiction
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
                · -- Case: t ≠ ETyp.int (error - contradiction)
                  cases h_typecheck
          · -- res.tagEnv' = result1.tagEnv'
            -- Same analysis as memEnv'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                -- if t != ETyp.int then throw
                split at h_typecheck
                · -- Case: t = ETyp.int
                  split at h_typecheck
                  · contradiction
                  · split at h_typecheck
                    · -- foldM error case - contradiction
                      contradiction
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck
                        · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                · -- Case: t ≠ ETyp.int (error - contradiction)
                  cases h_typecheck
          · -- res.nextLoc' = result1.nextLoc'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                -- if t != ETyp.int then throw
                split at h_typecheck
                · -- Case: t = ETyp.int
                  split at h_typecheck
                  · contradiction
                  · split at h_typecheck
                    · -- foldM error case - contradiction
                      contradiction
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck
                        · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                · -- Case: t ≠ ETyp.int (error - contradiction)
                  cases h_typecheck
          · -- res.nextTag' = result1.nextTag'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                -- if t != ETyp.int then throw
                split at h_typecheck
                · -- Case: t = ETyp.int
                  split at h_typecheck
                  · contradiction
                  · split at h_typecheck
                    · -- foldM error case - contradiction
                      contradiction
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck
                        · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                · -- Case: t ≠ ETyp.int (error - contradiction)
                  cases h_typecheck
          · -- res.regime' = result1.regime'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i t ls
                -- if t != ETyp.int then throw
                split at h_typecheck
                · -- Case: t = ETyp.int
                  split at h_typecheck
                  · contradiction
                  · split at h_typecheck
                    · -- foldM error case - contradiction
                      contradiction
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck
                        · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                        · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                · -- Case: t ≠ ETyp.int (error - contradiction)
                  cases h_typecheck
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
            nextTag := result2.nextTag',
            regime := result2.regime' }
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
        { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' }
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
                                    refine And.intro (by simp [h_qt2]) ?_
                                    refine And.intro rfl ?_
                                    refine And.intro (by simpa [ctx', h_pure] using h_tc1) ?_
                                    left
                                    refine ⟨st1, st2, p, p1, tcls, first :: rest, first, rest, ?_⟩
                                    refine And.intro (by simp [h_qt1]) ?_
                                    refine And.intro (by simp [h_qt1]) ?_
                                    refine And.intro (by simp) ?_
                                    refine And.intro h_empty ?_
                                    refine And.intro h_sub ?_
                                    refine And.intro (by simpa using h_map) ?_
                                    refine And.intro rfl ?_
                                    simpa using h_join
          | parrow st1 st2 p tcls =>
              by_cases h_empty : tcls = []
              · subst h_empty
                simp at htc
              · cases h_sub_val : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } with
                | false =>
                    simp [h_empty, h_sub_val] at htc
                    cases htc
                | true =>
                    have h_sub0 : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                      simp [h_sub_val]
                    have h_sub : isSubtype st1 result2.qualType = true := by
                      simpa [h_qt2] using h_sub0
                    simp [h_sub_val] at htc
                    cases h_map :
                        List.mapM
                          (fun tcl =>
                            applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result2 fuel') tcls with
                    | error _err =>
                        simp [h_map] at htc
                        simp [h_empty] at htc
                        cases htc
                    | ok results =>
                        simp [h_map] at htc
                        cases results with
                        | nil =>
                            simp at htc
                            simp [h_empty] at htc
                            cases htc
                        | cons first rest =>
                            cases h_join : joinTypeResults ctx first rest with
                            | error _err =>
                                simp [h_join] at htc
                                simp [h_empty] at htc
                                cases htc
                            | ok res' =>
                                simp [h_join] at htc
                                have h_empty' : tcls ≠ [] := h_empty
                                simp [h_empty'] at htc
                                cases htc
                                refine ⟨result2, result1, etyp2, p2, pred2, ?_⟩
                                refine And.intro (by simp [h_qt2]) ?_
                                refine And.intro rfl ?_
                                refine And.intro (by simp [ctx', h_tc1]) ?_
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

section regime_monotone_proof

private lemma regimeMonotone_refl (R : Regime) :
    Regime.monotoneStep R R := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k b hk
    exact Or.inl hk
  · intro k hk
    exact hk

private lemma regimeMonotone_trans {R R' R'' : Regime}
    (h₁ : Regime.monotoneStep R R')
    (h₂ : Regime.monotoneStep R' R'') :
    Regime.monotoneStep R R'' := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      R''.bound = R'.bound := h₂.1
      _ = R.bound := h₁.1
  · intro k b hkR
    have hR' : R'.lookup? k = some b ∨ R'.lookup? k = none := h₁.2.1 k b hkR
    cases hR' with
    | inl hkR' =>
        exact h₂.2.1 k b hkR'
    | inr hkR'_none =>
        exact Or.inr (by
          by_contra hkR''_not_none
          exact hkR''_not_none (by
            have hkR'_not_none : R'.lookup? k ≠ none := h₂.2.2 k hkR''_not_none
            exact False.elim (hkR'_not_none hkR'_none)))
  · intro k hkR''_not_none
    have hkR'_not_none : R'.lookup? k ≠ none := h₂.2.2 k hkR''_not_none
    exact h₁.2.2 k hkR'_not_none

private lemma list_mem_eraseDups_of_mem {α : Type} [BEq α] [LawfulBEq α]
    {x : α} {l : List α} (h : x ∈ l) : x ∈ l.eraseDups := by
  let P : Nat → Prop := fun n =>
    ∀ l : List α, l.length = n → ∀ x : α, x ∈ l → x ∈ l.eraseDups
  have hP : P l.length := by
    induction l.length using Nat.strong_induction_on with
    | _ n ih =>
        intro l hlen x hmem
        cases l with
        | nil =>
            cases hmem
        | cons a as =>
            have hlen_as : as.length < n := by
              have hlen' : as.length + 1 = n := by simpa using hlen
              have : as.length < as.length + 1 := Nat.lt_succ_self as.length
              simpa [hlen'] using this
            cases hmem with
            | head =>
                simp [List.eraseDups_cons]
            | tail _ hmem_as =>
                by_cases hxa : x = a
                · subst hxa
                  simp [List.eraseDups_cons]
                · have h_not_mem_filter : x ∈ as.filter (fun y => !y == a) := by
                    apply List.mem_filter.mpr
                    refine ⟨hmem_as, ?_⟩
                    simp [hxa]
                  have hlen_filter_le : (as.filter (fun y => !y == a)).length ≤ as.length := by
                    exact List.length_filter_le _ _
                  have hlen_filter_lt : (as.filter (fun y => !y == a)).length < n := by
                    exact Nat.lt_of_le_of_lt hlen_filter_le hlen_as
                  have hrec := ih (as.filter (fun y => !y == a)).length hlen_filter_lt
                  have hrec' := hrec (as.filter (fun y => !y == a)) rfl x h_not_mem_filter
                  simp [List.eraseDups_cons, hxa, hrec']
  exact hP l rfl x h

private lemma combineExtTreeMaps_getElem?_of_none_none
    (m1 m2 : ExtTreeMap Nat β)
    (f : Nat → Option β → Option β → Option β)
    (k : Nat)
    (hnone : f k none none = none) :
    (combineExtTreeMaps m1 m2 f)[k]? =
      match f k m1[k]? m2[k]? with
      | some v => some v
      | none => none := by
  classical
  let ks := (m1.keys ++ m2.keys).eraseDups
  by_cases hmem : k ∈ ks
  · have hgo := combineExtTreeMaps_go_get_mem m1 m2 f ks ({} : ExtTreeMap Nat β) k hmem
    simpa [combineExtTreeMaps, ks] using hgo
  · have hk_not_m1 : k ∉ m1 := by
      intro hk
      have hk_keys : k ∈ m1.keys := (ExtTreeMap.mem_keys).2 hk
      have hk_in_append : k ∈ m1.keys ++ m2.keys := List.mem_append_left _ hk_keys
      exact hmem (list_mem_eraseDups_of_mem hk_in_append)
    have hk_not_m2 : k ∉ m2 := by
      intro hk
      have hk_keys : k ∈ m2.keys := (ExtTreeMap.mem_keys).2 hk
      have hk_in_append : k ∈ m1.keys ++ m2.keys := List.mem_append_right _ hk_keys
      exact hmem (list_mem_eraseDups_of_mem hk_in_append)
    have hm1_none : m1[k]? = none := ExtTreeMap.getElem?_eq_none hk_not_m1
    have hm2_none : m2[k]? = none := ExtTreeMap.getElem?_eq_none hk_not_m2
    have hgo := combineExtTreeMaps_go_get_not_mem m1 m2 f ks ({} : ExtTreeMap Nat β) k hmem
    have hgo' : (combineExtTreeMaps m1 m2 f)[k]? = none := by
      simpa [combineExtTreeMaps, ks] using hgo
    rw [hgo']
    simp [hm1_none, hm2_none, hnone]

private lemma combineExtTreeMaps_get?_of_none_none
    (m1 m2 : ExtTreeMap Nat β)
    (f : Nat → Option β → Option β → Option β)
    (k : Nat)
    (hnone : f k none none = none) :
    (combineExtTreeMaps m1 m2 f).get? k =
      match f k (m1.get? k) (m2.get? k) with
      | some v => some v
      | none => none := by
  simpa [Std.ExtTreeMap.get?_eq_getElem?] using
    (combineExtTreeMaps_getElem?_of_none_none m1 m2 f k hnone)

private lemma joinRegimes_combine_fun_eq :
    (fun (_ : Tag) (ob1 ob2 : Option Bool) =>
      match ob1, ob2 with
      | some b1, some b2 => if b1 == b2 then some b1 else none
      | _, _ => none) =
    (fun (_ : Tag) (ob1 ob2 : Option Bool) =>
      match ob1, ob2 with
      | some b1, some b2 => if b1 = b2 then some b1 else none
      | _, _ => none) := by
  funext k ob1 ob2
  cases ob1 <;> cases ob2 <;> simp

private lemma joinRegimes_lookup_of_some_some
    (R1 R2 : Regime) (k : Tag) (b : Bool)
    (h1 : R1.lookup? k = some b)
    (h2 : R2.lookup? k = some b) :
    (joinRegimes R1 R2).lookup? k = some b := by
  have hk1 : k < R1.bound := by
    by_cases hk : k < R1.bound
    · exact hk
    · unfold Regime.lookup? at h1
      simp [hk] at h1
  have hk2 : k < R2.bound := by
    by_cases hk : k < R2.bound
    · exact hk
    · unfold Regime.lookup? at h2
      simp [hk] at h2
  have hkmin : k < min R1.bound R2.bound := Nat.lt_min.2 ⟨hk1, hk2⟩
  have hmap1 : R1.map.get? k = some b := by
    unfold Regime.lookup? at h1
    simp [hk1] at h1
    exact h1
  have hmap2 : R2.map.get? k = some b := by
    unfold Regime.lookup? at h2
    simp [hk2] at h2
    exact h2
  have hkjoin : k < (joinRegimes R1 R2).bound := by
    simpa [joinRegimes] using hkmin
  have hmap1' : R1.map[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap1
  have hmap2' : R2.map[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap2
  have hcombine :
      (combineExtTreeMaps R1.map R2.map
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 == b2 then some b1 else none
          | _, _ => none)).get? k = some b := by
    have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1.map R2.map
      (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 = b2 then some b1 else none
        | _, _ => none) k rfl
    have hcombine0s :
        (combineExtTreeMaps R1.map R2.map
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 = b2 then some b1 else none
            | _, _ => none))[k]? = some b := by
      simpa [hmap1', hmap2'] using hcombine0
    have hcombine0' :
        (combineExtTreeMaps R1.map R2.map
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none))[k]? = some b := by
      simpa [joinRegimes_combine_fun_eq] using hcombine0s
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
  unfold Regime.lookup?
  rw [if_pos hkjoin]
  simpa [joinRegimes] using hcombine

private lemma joinRegimes_lookup_of_left_none
    (R1 R2 : Regime) (k : Tag)
    (h1 : R1.lookup? k = none) :
    (joinRegimes R1 R2).lookup? k = none := by
  by_cases hkmin : k < min R1.bound R2.bound
  · have hk1 : k < R1.bound := Nat.lt_of_lt_of_le hkmin (Nat.min_le_left _ _)
    have hmap1 : R1.map.get? k = none := by
      unfold Regime.lookup? at h1
      rw [if_pos hk1] at h1
      exact h1
    have hkjoin : k < (joinRegimes R1 R2).bound := by
      simpa [joinRegimes] using hkmin
    have hmap1' : R1.map[k]? = none := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap1
    have hcombine :
        (combineExtTreeMaps R1.map R2.map
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none)).get? k = none := by
      have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1.map R2.map
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 = b2 then some b1 else none
          | _, _ => none) k rfl
      have hcombine0s :
          (combineExtTreeMaps R1.map R2.map
            (fun _ ob1 ob2 =>
              match ob1, ob2 with
              | some b1, some b2 => if b1 = b2 then some b1 else none
              | _, _ => none))[k]? = none := by
        simpa [hmap1'] using hcombine0
      have hcombine0' :
          (combineExtTreeMaps R1.map R2.map
            (fun _ ob1 ob2 =>
              match ob1, ob2 with
              | some b1, some b2 => if b1 == b2 then some b1 else none
              | _, _ => none))[k]? = none := by
        simpa [joinRegimes_combine_fun_eq] using hcombine0s
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
    unfold Regime.lookup?
    rw [if_pos hkjoin]
    simpa [joinRegimes] using hcombine
  · have hk_join : ¬ k < (joinRegimes R1 R2).bound := by
      simpa [joinRegimes] using hkmin
    unfold Regime.lookup?
    simp [hk_join]

private lemma joinRegimes_lookup_of_right_none
    (R1 R2 : Regime) (k : Tag)
    (h2 : R2.lookup? k = none) :
    (joinRegimes R1 R2).lookup? k = none := by
  by_cases hkmin : k < min R1.bound R2.bound
  · have hk2 : k < R2.bound := Nat.lt_of_lt_of_le hkmin (Nat.min_le_right _ _)
    have hmap2 : R2.map.get? k = none := by
      unfold Regime.lookup? at h2
      rw [if_pos hk2] at h2
      exact h2
    have hkjoin : k < (joinRegimes R1 R2).bound := by
      simpa [joinRegimes] using hkmin
    have hmap2' : R2.map[k]? = none := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap2
    have hcombine :
        (combineExtTreeMaps R1.map R2.map
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none)).get? k = none := by
      have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1.map R2.map
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 = b2 then some b1 else none
          | _, _ => none) k rfl
      have hcombine0s :
          (combineExtTreeMaps R1.map R2.map
            (fun _ ob1 ob2 =>
              match ob1, ob2 with
              | some b1, some b2 => if b1 = b2 then some b1 else none
              | _, _ => none))[k]? = none := by
        simpa [hmap2'] using hcombine0
      have hcombine0' :
          (combineExtTreeMaps R1.map R2.map
            (fun _ ob1 ob2 =>
              match ob1, ob2 with
              | some b1, some b2 => if b1 == b2 then some b1 else none
              | _, _ => none))[k]? = none := by
        simpa [joinRegimes_combine_fun_eq] using hcombine0s
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
    unfold Regime.lookup?
    rw [if_pos hkjoin]
    simpa [joinRegimes] using hcombine
  · have hk_join : ¬ k < (joinRegimes R1 R2).bound := by
      simpa [joinRegimes] using hkmin
    unfold Regime.lookup?
    simp [hk_join]

private lemma joinRegimes_no_new_left
    (R1 R2 : Regime) (k : Tag)
    (hjoin : (joinRegimes R1 R2).lookup? k ≠ none) :
    R1.lookup? k ≠ none := by
  intro h1none
  have hnone : (joinRegimes R1 R2).lookup? k = none :=
    joinRegimes_lookup_of_left_none R1 R2 k h1none
  exact hjoin hnone

private lemma joinRegimes_monotone_of_monotone
    (R R1 R2 : Regime)
    (h1 : Regime.monotoneStep R R1)
    (h2 : Regime.monotoneStep R R2) :
    Regime.monotoneStep R (joinRegimes R1 R2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [joinRegimes, h1.1, h2.1, Nat.min_self]
  · intro k b hkR
    have hk1 := h1.2.1 k b hkR
    have hk2 := h2.2.1 k b hkR
    cases hk1 with
    | inl hk1some =>
        cases hk2 with
        | inl hk2some =>
            exact Or.inl (joinRegimes_lookup_of_some_some R1 R2 k b hk1some hk2some)
        | inr hk2none =>
            exact Or.inr (joinRegimes_lookup_of_right_none R1 R2 k hk2none)
    | inr hk1none =>
        exact Or.inr (joinRegimes_lookup_of_left_none R1 R2 k hk1none)
  · intro k hkjoin
    have hk1 : R1.lookup? k ≠ none := joinRegimes_no_new_left R1 R2 k hkjoin
    exact h1.2.2 k hk1

private lemma invalidateRegimeDeps_monotone
    (R : Regime) (env : TagEnv) (ls : LocSet) :
    Regime.monotoneStep R (invalidateRegimeDeps R env ls) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k b hkR
    have hklt : k < R.bound := by
      by_cases hk : k < R.bound
      · exact hk
      · unfold Regime.lookup? at hkR
        simp [hk] at hkR
    have hkmap : R.map[k]? = some b := by
      unfold Regime.lookup? at hkR
      simp [hklt] at hkR
      exact hkR
    have hmapFiltered :
        (R.map.filter (fun k _ =>
          (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k))[k]? =
        Option.filter
          (fun _ =>
            (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k)
          (some b) := by
      rw [Std.ExtTreeMap.getElem?_filter']
      simp [hkmap]
    unfold invalidateRegimeDeps Regime.lookup?
    simp [hklt, hmapFiltered]
    exact em (k ∈ ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env)
  · intro k hkInv
    by_contra hkRnone
    have hnone : (invalidateRegimeDeps R env ls).lookup? k = none := by
      by_cases hklt : k < R.bound
      · have hkmapNone : R.map[k]? = none := by
          unfold Regime.lookup? at hkRnone
          simp [hklt] at hkRnone
          exact ExtTreeMap.getElem?_eq_none hkRnone
        have hmapFilteredNone :
            (R.map.filter (fun k _ =>
              (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k))[k]? =
            Option.filter
              (fun _ =>
                (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k)
              (none : Option Bool) := by
          rw [Std.ExtTreeMap.getElem?_filter']
          simp [hkmapNone]
        unfold invalidateRegimeDeps Regime.lookup?
        simp [hklt, hmapFilteredNone]
      · unfold invalidateRegimeDeps Regime.lookup?
        simp [hklt]
    exact hkInv hnone

private lemma joinTypeResults_regime_monotone
    (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult) (R : Regime)
    (h_r : Regime.monotoneStep R r.regime')
    (h_rs : ∀ x ∈ rs, Regime.monotoneStep R x.regime') :
    joinTypeResults ctx r rs = .ok res →
    Regime.monotoneStep R res.regime' := by
  intro hjoin
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvs acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_regime :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        Regime.monotoneStep R acc.2.2.2.2.2.1 →
        (∀ x ∈ rs', Regime.monotoneStep R x.regime') →
        Regime.monotoneStep R acc'.2.2.2.2.2.1 := by
    intro rs' acc acc' hfold hacc hmono
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        simpa using hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hxmono : Regime.monotoneStep R x.regime' := hmono x (by simp)
            have hacc1 : Regime.monotoneStep R (joinRegimes acc.2.2.2.2.2.1 x.regime') :=
              joinRegimes_monotone_of_monotone R acc.2.2.2.2.2.1 x.regime' hacc hxmono
            have hmono_tail : ∀ y ∈ xs, Regime.monotoneStep R y.regime' := by
              intro y hy
              exact hmono y (by simp [hy])
            exact ih _ hfold hacc1 hmono_tail
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
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              simpa using h_fold_regime rs
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') a
                hfold h_r h_rs

private lemma applyFnTClosure_regime_mono
    (tcl : FnTClosure) (ctx : TypeContext)
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (r1 r2 : TypeResult) (fuel : Nat)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheck ctx' e m = .ok res' →
          Regime.monotoneStep ctx'.regime res'.regime') :
    applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 fuel = .ok r2 →
    Regime.monotoneStep r1.regime' r2.regime' := by
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
          exact regimeMonotone_refl r1.regime'
      | nestedPfn innerArg innerArgTyp innerRet =>
          simp [pure, Except.pure] at happly
          cases happly
          exact regimeMonotone_refl r1.regime'
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
                    exact regimeMonotone_refl r1.regime'
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | int =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | bool =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | unit =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | string =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | arrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'
            | parrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact regimeMonotone_refl r1.regime'

private lemma applyPFnTClosure_regime_mono
    (tcl : PFnTClosure) (ctx : TypeContext)
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (r1 r2 : TypeResult) (fuel : Nat)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheck ctx' e m = .ok res' →
          Regime.monotoneStep ctx'.regime res'.regime') :
    applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 fuel = .ok r2 →
    Regime.monotoneStep r1.regime' r2.regime' := by
  intro happly
  unfold applyPFnTClosure at happly
  cases fuel <;> simp at happly
  cases tcl with
  | regular x body env =>
      simp [bind, Except.bind] at happly
      rcases htc_body : typecheckExpr _ _ _ with _ | ⟨r3⟩
      · rw [htc_body] at happly
        simp at happly
      · rw [htc_body] at happly
        simp at happly
        rcases hq3 : r3.qualType with ⟨etyp3, poison3, pred3⟩
        simp [hq3] at happly
        rcases hsub : isSubtype st2 { etyp := etyp3, poison := poison3, pred := pred3 }
        · rw [hsub] at happly
          simp [Functor.map, Except.map] at happly
        · rw [hsub] at happly
          simp [pure, Except.pure] at happly
          subst r2
          specialize IH _ (lt_add_one _) _ _ _ htc_body
          simp at IH
          exact IH
  | extern x retSpec capturedEnv =>
      cases retSpec with
      | simple typ poison pred =>
          simp at happly
          cases hret : returnSpecToQTyp _ _ _ _ _ with
          | error err =>
              rw [hret] at happly
              simp at happly
          | ok ret =>
              rw [hret] at happly
              simp at happly
              cases happly
              exact regimeMonotone_refl r1.regime'
      | nestedFn innerArg innerArgTyp innerRet innerEffects =>
          simp [pure, Except.pure] at happly
          cases happly
          exact regimeMonotone_refl r1.regime'
      | nestedPfn innerArg innerArgTyp innerRet =>
          simp [pure, Except.pure] at happly
          cases happly
          exact regimeMonotone_refl r1.regime'

private lemma typecheckVar_regime_mono (ctx : TypeContext) (x : Name) (res : TypeResult) :
    typecheckVar ctx x = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
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
              simp [pure, Except.pure] at htc
              cases htc
              exact regimeMonotone_refl ctx.regime
          | guardOnly k =>
              simp at htc
              cases hft : etyp.isFunctionType with
              | true =>
                  simp [hft, throw] at htc
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact regimeMonotone_refl ctx.regime
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact regimeMonotone_refl ctx.regime
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact regimeMonotone_refl ctx.regime
          | guardClosure k _ _ _ =>
              simp at htc
              cases hft : etyp.isFunctionType with
              | true =>
                  simp [hft, throw] at htc
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact regimeMonotone_refl ctx.regime
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact regimeMonotone_refl ctx.regime
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact regimeMonotone_refl ctx.regime

private lemma typecheckApp_regime_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
  typecheckApp ctx e1 e2 fuel = .ok res →
  Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  cases fuel with
  | zero =>
      unfold typecheckApp at htc
      simp at htc
  | succ fuel' =>
      have hstruct := typecheckApp_arrow_structure_full ctx e1 e2 fuel' res htc
      rcases hstruct with ⟨res2, res1, etyp2, p2, pred2, hq2, hte2, hte1, hcases⟩
      have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
      have hte2' : typecheck ctx e2 fuel' = .ok res2 := by
        simpa [typecheck] using hte2
      have hmono2 : Regime.monotoneStep ctx.regime res2.regime' := IH fuel' h_fuel e2 ctx res2 hte2'
      have IH' :
          ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
            typecheck ctx'' e m = .ok res' →
            Regime.monotoneStep ctx''.regime res'.regime' := by
        intro m hm e ctx'' res' htc'
        exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
      cases hcases with
      | inl harr =>
          rcases harr with
            ⟨st1, st2, p, p1, tcls, results, first, rest,
              hetyp1, hpoison1, _hnotPure, _hnonempty, _hsub, hmap, hresults, hjoin⟩
          subst results
          have hmap_prop :
              ∀ x ∈ (first :: rest), Regime.monotoneStep res2.regime' x.regime' := by
            apply List.mapM_Except_preserves_property
              (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx res2 fuel')
              (P := fun x => Regime.monotoneStep res2.regime' x.regime')
            · intro tcl result htcl
              exact applyFnTClosure_regime_mono tcl ctx st1 st2 p p1 etyp2 p2 pred2 res2 result fuel' IH' htcl
            · simpa using hmap
          have hfirst : Regime.monotoneStep res2.regime' first.regime' := by
            exact hmap_prop first (by simp)
          have hrest : ∀ x ∈ rest, Regime.monotoneStep res2.regime' x.regime' := by
            intro x hx
            exact hmap_prop x (by simp [hx])
          have hjoin_mono : Regime.monotoneStep res2.regime' res.regime' :=
            joinTypeResults_regime_monotone ctx first rest res res2.regime' hfirst hrest hjoin
          exact regimeMonotone_trans hmono2 hjoin_mono
      | inr hparr =>
          rcases hparr with
            ⟨st1, st2, p, p1, tcls, results, first, rest,
              hetyp1, hpoison1, _hnonempty, _hsub, hmap, hresults, hjoin⟩
          subst results
          have hmap_prop :
              ∀ x ∈ (first :: rest), Regime.monotoneStep res2.regime' x.regime' := by
            apply List.mapM_Except_preserves_property
              (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx res2 fuel')
              (P := fun x => Regime.monotoneStep res2.regime' x.regime')
            · intro tcl result htcl
              exact applyPFnTClosure_regime_mono tcl ctx st1 st2 p p1 etyp2 p2 pred2 res2 result fuel' IH' htcl
            · simpa using hmap
          have hfirst : Regime.monotoneStep res2.regime' first.regime' := by
            exact hmap_prop first (by simp)
          have hrest : ∀ x ∈ rest, Regime.monotoneStep res2.regime' x.regime' := by
            intro x hx
            exact hmap_prop x (by simp [hx])
          have hjoin_mono : Regime.monotoneStep res2.regime' res.regime' :=
            joinTypeResults_regime_monotone ctx first rest res res2.regime' hfirst hrest hjoin
          exact regimeMonotone_trans hmono2 hjoin_mono

private lemma runWhileFixpoint_regime_mono
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (pureGuard : Bool) (guardOpt : Option (Tag × Deps))
    (pc : Poison) (mem : MemoryTypeEnv) (tag : TagEnv) (regime : Regime) (nextLoc : Loc) (nextTag : Tag)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    runWhileFixpoint ctx e1 e2 fuel pureGuard guardOpt = .ok (pc, mem, tag, regime, nextLoc, nextTag) →
    Regime.monotoneStep ctx.regime regime := by
  intro hfix
  induction fuel generalizing ctx pureGuard guardOpt pc mem tag regime nextLoc nextTag with
  | zero =>
      simp [runWhileFixpoint] at hfix
  | succ fuel' ih =>
      simp [runWhileFixpoint, bind, Except.bind] at hfix
      set ctxForGuard : TypeContext := if pureGuard then { ctx with pureCtx := true } else ctx with hctxForGuard
      rcases hguard : typecheckExpr ctxForGuard e1 fuel' with _ | ⟨guardRes⟩
      · simp [hguard] at hfix
      · simp [hguard] at hfix
        rcases hq1 : guardRes.qualType with ⟨etyp1, p1, pred1⟩
        simp [hq1] at hfix
        by_cases hbool : etyp1 != ETyp.bool
        · simp at hbool
          simp [hbool] at hfix
        · simp at hbool
          simp [hbool] at hfix
          rcases hbody : typecheckExpr _ e2 fuel' with _ | ⟨bodyRes⟩
          · simp [pure, Except.pure] at hfix
            erw [hbody] at hfix
            simp at hfix
          · simp [hbody] at hfix
            rcases hq2 : bodyRes.qualType with ⟨etyp2, p2, pred2⟩
            simp [hq2] at hfix
            by_cases hunit : etyp2 != ETyp.unit
            · simp at hunit
              simp [hunit] at hfix
              simp [pure, Except.pure] at hfix
            · simp at hunit
              simp [hunit] at hfix
              have htc_guard : typecheck ctxForGuard e1 fuel' = .ok guardRes := by
                simpa [typecheck] using hguard
              have hguard_mono : Regime.monotoneStep ctxForGuard.regime guardRes.regime' :=
                IH fuel' (lt_add_one fuel') e1 ctxForGuard guardRes htc_guard
              have hctx_guard_mono : Regime.monotoneStep ctx.regime guardRes.regime' := by
                have hctxForGuard_regime : ctxForGuard.regime = ctx.regime := by
                  cases pureGuard <;> simp [hctxForGuard]
                simpa [hctxForGuard_regime] using hguard_mono
              set bodyPcCtx : TypeContext := { ctx with pc := joinPoison ctx.pc p1 } with hbodyPcCtx
              set bodyTagEnv : TagEnv := if pureGuard then ctx.tagEnv else guardRes.tagEnv' with hbodyTagEnv
              set bodyRegime : Regime := if pureGuard then ctx.regime else guardRes.regime' with hbodyRegime
              set bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv, regime := bodyRegime } with hbodyEnvCtx
              set bodyCtxBase : TypeContext := { bodyEnvCtx with nextLoc := guardRes.nextLoc', nextTag := guardRes.nextTag', pureCtx := ctx.pureCtx } with hbodyCtxBase
              set bodyCtx : TypeContext :=
                match guardOpt with
                | some (k, deps) => { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
                | none => bodyCtxBase with hbodyCtx
              have htc_body : typecheck bodyCtx e2 fuel' = .ok bodyRes := by
                simp [typecheck, bodyCtx]
                cases guardOpt <;> simp at hbody <;> simp <;> apply hbody
              have hbody_mono_local : Regime.monotoneStep bodyCtx.regime bodyRes.regime' :=
                IH fuel' (lt_add_one fuel') e2 bodyCtx bodyRes htc_body
              have hctx_body_mono : Regime.monotoneStep ctx.regime bodyRes.regime' := by
                have hbodyCtx_regime :
                    bodyCtx.regime = (if pureGuard then ctx.regime else guardRes.regime') := by
                  cases guardOpt <;> simp [hbodyCtx, hbodyCtxBase, hbodyEnvCtx, hbodyRegime]
                cases hpg : pureGuard with
                | false =>
                    have hbody_from_guard : Regime.monotoneStep guardRes.regime' bodyRes.regime' := by
                      simpa [hpg, hbodyCtx_regime] using hbody_mono_local
                    exact regimeMonotone_trans hctx_guard_mono hbody_from_guard
                | true =>
                    simpa [hpg, hbodyCtx_regime] using hbody_mono_local
              set newPc : Poison := joinPoison ctx.pc p2 with hnewPc
              set restrictedBodyEnv : MemoryTypeEnv := restrictMemEnv bodyRes.memEnv' ctx.memEnv with hrestrictedBodyEnv
              set newMemEnv : MemoryTypeEnv := joinMemEnvs ctx.memEnv restrictedBodyEnv with hnewMemEnv
              set newTagEnv : TagEnv := joinTagEnvs ctx.tagEnv bodyRes.tagEnv' with hnewTagEnv
              set newRegime : Regime := joinRegimes ctx.regime bodyRes.regime' with hnewRegime
              have hnewRegime_mono : Regime.monotoneStep ctx.regime newRegime := by
                apply joinRegimes_monotone_of_monotone ctx.regime ctx.regime bodyRes.regime'
                · exact regimeMonotone_refl ctx.regime
                · exact hctx_body_mono
              by_cases hfixpoint :
                  newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv && newRegime.bound == ctx.regime.bound
              · simp at hfixpoint
                simp [if_pos hfixpoint] at hfix
                simp [pure, Except.pure] at hfix
                rcases hfix with ⟨_, _, _, hfixRegime, _, _⟩
                subst regime
                exact hnewRegime_mono
              · simp [pure, Except.pure] at hfix
                rw [if_neg (by simpa using hfixpoint)] at hfix
                set nextCtx : TypeContext :=
                  { ctx with
                    pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, regime := newRegime,
                    nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' } with hnextCtx
                have ih' : Regime.monotoneStep nextCtx.regime regime := by
                  apply ih _ _ _ _ _ _ _ _ _ _ hfix
                  intro fuel'' hfuel'' expr tc r htc
                  exact IH fuel'' (by linarith) expr tc r htc
                have hnextCtx_regime : nextCtx.regime = newRegime := by simp [hnextCtx]
                have hnew_to_final : Regime.monotoneStep newRegime regime := by
                  simpa [hnextCtx_regime] using ih'
                exact regimeMonotone_trans hnewRegime_mono hnew_to_final

private lemma typecheckWhile_regime_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckWhile ctx e1 e2 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  cases fuel with
  | zero =>
      unfold typecheckWhile at htc
      simp at htc
  | succ fuel' =>
      unfold typecheckWhile at htc
      cases hguard : matchGuard e1 ctx.memEnv ctx.varEnv with
      | ok g =>
          rcases g with ⟨k, deps⟩
          simp [hguard] at htc
          cases fuel' with
          | zero =>
              simp [typecheckWhileDepoison] at htc
          | succ fuel'' =>
              simp [typecheckWhileDepoison, bind, Except.bind] at htc
              cases hfix :
                  runWhileFixpoint ctx e1 e2 fuel'' true (some (k, deps)) with
              | error err =>
                  simp [hfix] at htc
              | ok r =>
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_regime_mono ctx e1 e2 fuel'' true (some (k, deps))
                        finalPc finalMemEnv finalTagEnv finalRegime finalNextLoc finalNextTag _ hfix
                  intro fuel hfuel expr ctx' r hctx
                  exact IH fuel (by linarith) expr ctx' r hctx
      | error err =>
          simp [hguard] at htc
          cases fuel' with
          | zero =>
              simp [typecheckWhileStd] at htc
          | succ fuel'' =>
              simp [typecheckWhileStd, bind, Except.bind] at htc
              cases hfix : runWhileFixpoint ctx e1 e2 fuel'' false none with
              | error err =>
                  simp [hfix] at htc
              | ok r =>
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_regime_mono ctx e1 e2 fuel'' false none
                        finalPc finalMemEnv finalTagEnv finalRegime finalNextLoc finalNextTag _ hfix
                  intro fuel hfuel expr ctx' r hctx
                  exact IH fuel (by linarith) expr ctx' r hctx

private lemma typecheckExternVal_preserves_regime
    (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (res : TypeResult) :
    typecheckExternVal ctx typ poison pred = .ok res →
    res.regime' = ctx.regime := by
  intro htc
  unfold typecheckExternVal at htc
  split at htc
  · simp at htc
  · simp at htc
  · simp [bind, Except.bind] at htc
    cases h : surfaceSpecToQTyp typ poison pred ctx.varEnv ctx with
    | error _ =>
        simp [h] at htc
    | ok result =>
        simp [h, pure, Except.pure] at htc
        cases htc
        rfl

private lemma typecheckExternFn_preserves_regime
    (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) (res : TypeResult) :
    typecheckExternFn ctx arg argTyp retSpec effects = .ok res →
    res.regime' = ctx.regime := by
  intro htc
  unfold typecheckExternFn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

private lemma typecheckExternPfn_preserves_regime
    (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (res : TypeResult) :
    typecheckExternPfn ctx arg argTyp retSpec = .ok res →
    res.regime' = ctx.regime := by
  intro htc
  unfold typecheckExternPfn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

private lemma typecheckOp_regime_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckOp ctx e1 e2 fuel op = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckOp_structure ctx e1 e2 op fuel res htc
  rcases hstruct with ⟨result1, result2, _result_etyp, htc1, htc2, _hop, _hmem, _htag, _hloc, _hnexttag, hregime, _hetyp, _hpoison, _hpred⟩
  cases fuel with
  | zero =>
      unfold typecheckOp at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have hm2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have hm2' : Regime.monotoneStep result1.regime' result2.regime' := by
        simpa [ctx'] using hm2
      have hm : Regime.monotoneStep ctx.regime result2.regime' := regimeMonotone_trans hm1 hm2'
      simpa [hregime] using hm

private lemma typecheckSeq_regime_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckSeq ctx e1 e2 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckSeq_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
  cases fuel with
  | zero =>
      unfold typecheckSeq at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok res := by simpa using htc2
      have hm2 := IH fuel' h_fuel e2 ctx' res htc2_simp
      have hm2' : Regime.monotoneStep result1.regime' res.regime' := by
        simpa [hctx', updateCtxFromResult] using hm2
      exact regimeMonotone_trans hm1 hm2'

private lemma typecheckNewRef_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckNewRef ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckNewRef_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, _l, htc1, _hl, _hetyp, _hqtetyp, _hqtpoison, _hqtpred, _hmem, _htag, _hloc, _hnexttag, hregime⟩
  cases fuel with
  | zero =>
      unfold typecheckNewRef at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckAssign_regime_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (_IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckAssign ctx e1 e2 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckAssign_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨_result1, result2, ls, _htc1, _hetyp1, _htc2, _hetyp2, _hloc, _hnexttag, hregime, _hqtetyp, _hqtpoison, _hqtpred⟩
  simpa [hregime] using invalidateRegimeDeps_monotone ctx.regime result2.tagEnv' ls

private lemma typecheckDeref_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckDeref ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckDeref_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, _hnexttag, hregime⟩
  cases fuel with
  | zero =>
      unfold typecheckDeref at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckVlet_regime_mono (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckVlet ctx x e1 e2 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckVlet_structure ctx x e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _hetyp, _hmem, _htag, _hloc, _hnexttag, hregime, _hqtpred⟩
  cases fuel with
  | zero =>
      unfold typecheckVlet at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have hm2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have hm2' : Regime.monotoneStep result1.regime' result2.regime' := by
        simpa [hctx'] using hm2
      have hm : Regime.monotoneStep ctx.regime result2.regime' := regimeMonotone_trans hm1 hm2'
      simpa [hregime] using hm

private lemma typecheckIf_regime_mono (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  cases fuel with
  | zero =>
      unfold typecheckIf at htc
      simp at htc
  | succ fuel' =>
      have hstruct := typecheckIf_structure ctx e1 e2 e3 (fuel' + 1) res htc
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      cases hstruct with
      | inl h1 =>
          obtain ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, res3, _htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison, _hetyp⟩ := h1
          have hm2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
          simpa [hregime] using hm2
      | inr h_rest =>
          cases h_rest with
          | inl h2 =>
              obtain ⟨k, deps, _, _, res1, _htc1, _hbool, res2, _htc2, res3, htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison, _hetyp⟩ := h2
              let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
              let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
              have htc3' : typecheck ctxFalse' e3 fuel' = .ok res3 := by
                simpa [typecheck, ctxFalse, ctxFalse'] using htc3
              have hm3 := IH fuel' h_fuel e3 ctxFalse' res3 htc3'
              simpa [hregime, ctxFalse, ctxFalse'] using hm3
          | inr h_rest2 =>
              cases h_rest2 with
              | inl h3 =>
                  obtain ⟨k, deps, _, _, res1, _htc1, _hbool, res2, htc2, res3, htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison⟩ := h3
                  let branchPc := joinPoison ctx.pc res1.qualType.poison
                  let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩, pc := branchPc }
                  let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩, pc := branchPc }
                  let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                  have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by
                    simpa [typecheck, ctxTrue, branchPc] using htc2
                  have htc3' : typecheck ctxFalse' e3 fuel' = .ok res3 := by
                    simpa [typecheck, ctxFalse', ctxFalse, branchPc] using htc3
                  have hm2 := IH fuel' h_fuel e2 ctxTrue res2 htc2'
                  have hm3 := IH fuel' h_fuel e3 ctxFalse' res3 htc3'
                  have hjoin : Regime.monotoneStep ctx.regime (joinRegimes res2.regime' res3.regime') :=
                    joinRegimes_monotone_of_monotone ctx.regime res2.regime' res3.regime' hm2 hm3
                  simpa [hregime] using hjoin
              | inr h4 =>
                  obtain ⟨⟨err, _hmatch_fail⟩, res1, htc1, _hbool, res2, htc2, res3, htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison⟩ := h4
                  let ctx1 : TypeContext := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
                  let pc' := joinPoison ctx.pc res1.qualType.poison
                  let ctx'' := { ctx1 with pc := pc' }
                  let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
                  have htc1' : typecheck ctx e1 fuel' = .ok res1 := by
                    simpa [typecheck] using htc1
                  have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by
                    simpa [typecheck, ctx'', ctx1, pc'] using htc2
                  have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by
                    simpa [typecheck, ctxForE3, ctx'', ctx1, pc'] using htc3
                  have hm1 := IH fuel' h_fuel e1 ctx res1 htc1'
                  have hm2_local := IH fuel' h_fuel e2 ctx'' res2 htc2'
                  have hm3_local := IH fuel' h_fuel e3 ctxForE3 res3 htc3'
                  have hm2' : Regime.monotoneStep res1.regime' res2.regime' := by
                    simpa [ctx'', ctx1] using hm2_local
                  have hm3' : Regime.monotoneStep res1.regime' res3.regime' := by
                    simpa [ctxForE3, ctx'', ctx1] using hm3_local
                  have hm2 : Regime.monotoneStep ctx.regime res2.regime' := regimeMonotone_trans hm1 hm2'
                  have hm3 : Regime.monotoneStep ctx.regime res3.regime' := regimeMonotone_trans hm1 hm3'
                  have hjoin : Regime.monotoneStep ctx.regime (joinRegimes res2.regime' res3.regime') :=
                    joinRegimes_monotone_of_monotone ctx.regime res2.regime' res3.regime' hm2 hm3
                  simpa [hregime] using hjoin

private lemma typecheckRand_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckRand ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckRand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hetyp, _hmem, _htag, _hloc, _hnexttag, hregime, _hqtetyp, _hqtpoison, _hqtpred⟩
  cases fuel with
  | zero =>
      unfold typecheckRand at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckFrand_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckFrand ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckFrand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, _hnexttag, hregime, _hetyp, _hpoison, _hguard⟩
  cases fuel with
  | zero =>
      unfold typecheckFrand at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckPrintInt_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckPrintInt ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckPrintInt_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, _hnexttag, hregime, _hetyp⟩
  cases fuel with
  | zero =>
      unfold typecheckPrintInt at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckPrintString_regime_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckPrintString ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckPrintString_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, _hnexttag, hregime, _hetyp⟩
  cases fuel with
  | zero =>
      unfold typecheckPrintString at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

private lemma typecheckUnaryOp_regime_mono (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckUnaryOp ctx op e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckUnaryOp_structure ctx op e fuel res htc
  rcases hstruct with ⟨result1, _result_etyp, htc1, _hop, _hmem, _htag, _hloc, _hnexttag, hregime, _hetyp, _hpoison, _hpred⟩
  cases fuel with
  | zero =>
      unfold typecheckUnaryOp at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have hm1 := IH fuel' h_fuel e ctx result1 htc1_simp
      simpa [hregime] using hm1

-- Regime monotonicity: Typechecking can only drop regime entries (never change values or add new entries)
-- Replaces regime_immutability which becomes false once typing invalidates R
private lemma typecheck_regime_mono_main : ∀ (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult),
    typecheck ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro ctx e fuel res htc
  revert ctx e res htc
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro ctx e res htc
      have IH_converted : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheck ctx' e m = .ok res' →
          Regime.monotoneStep ctx'.regime res'.regime' := by
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
              Regime.monotoneStep ctx'.regime res'.regime' := by
            intro m h_lt e' ctx' res' htc'
            have h_lt' : m < fuel' + 1 := Nat.lt_of_lt_of_le h_lt (Nat.le_succ fuel')
            exact IH_converted m h_lt' e' ctx' res' htc'
          cases e with
          | num _n =>
              unfold typecheckInt at htc
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact regimeMonotone_refl ctx.regime
          | bool _b =>
              unfold typecheckBool at htc
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact regimeMonotone_refl ctx.regime
          | unit =>
              unfold typecheckUnit at htc
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact regimeMonotone_refl ctx.regime
          | str _s =>
              unfold typecheckString at htc
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact regimeMonotone_refl ctx.regime
          | var x =>
              simp at htc
              exact typecheckVar_regime_mono ctx x res htc
          | fn x st1 body st2 =>
              unfold typecheckFn at htc
              simp at htc
              injection htc with h_eq
              subst h_eq
              exact regimeMonotone_refl ctx.regime
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
                  exact regimeMonotone_refl ctx.regime
          | externVal typ poison pred =>
              simp at htc
              have h_preserve := typecheckExternVal_preserves_regime ctx typ poison pred res htc
              rw [h_preserve]
              exact regimeMonotone_refl ctx.regime
          | externFn arg argTyp retSpec effects =>
              simp at htc
              have h_preserve := typecheckExternFn_preserves_regime ctx arg argTyp retSpec effects res htc
              rw [h_preserve]
              exact regimeMonotone_refl ctx.regime
          | externPfn arg argTyp retSpec =>
              simp at htc
              have h_preserve := typecheckExternPfn_preserves_regime ctx arg argTyp retSpec res htc
              rw [h_preserve]
              exact regimeMonotone_refl ctx.regime
          | op e1 op e2 =>
              simp at htc
              exact typecheckOp_regime_mono ctx e1 e2 fuel' op res IH_fuel' htc
          | unaryop op e1 =>
              simp at htc
              exact typecheckUnaryOp_regime_mono ctx op e1 fuel' res IH_fuel' htc
          | ite e1 e2 e3 =>
              simp at htc
              exact typecheckIf_regime_mono ctx e1 e2 e3 fuel' res IH_fuel' htc
          | newRef e1 =>
              simp at htc
              exact typecheckNewRef_regime_mono ctx e1 fuel' res IH_fuel' htc
          | assign e1 e2 =>
              simp at htc
              exact typecheckAssign_regime_mono ctx e1 e2 fuel' res IH_fuel' htc
          | deref e1 =>
              simp at htc
              exact typecheckDeref_regime_mono ctx e1 fuel' res IH_fuel' htc
          | seq e1 e2 =>
              simp at htc
              exact typecheckSeq_regime_mono ctx e1 e2 fuel' res IH_fuel' htc
          | vlet x e1 e2 =>
              simp at htc
              exact typecheckVlet_regime_mono ctx x e1 e2 fuel' res IH_fuel' htc
          | app e1 e2 =>
              simp at htc
              exact typecheckApp_regime_mono ctx e1 e2 fuel' res IH_fuel' htc
          | kwhile e1 e2 =>
              simp at htc
              exact typecheckWhile_regime_mono ctx e1 e2 fuel' res IH_fuel' htc
          | rand e1 =>
              simp at htc
              exact typecheckRand_regime_mono ctx e1 fuel' res IH_fuel' htc
          | frand e1 =>
              simp at htc
              exact typecheckFrand_regime_mono ctx e1 fuel' res IH_fuel' htc
          | printInt e1 =>
              simp at htc
              exact typecheckPrintInt_regime_mono ctx e1 fuel' res IH_fuel' htc
          | printString e1 =>
              simp at htc
              exact typecheckPrintString_regime_mono ctx e1 fuel' res IH_fuel' htc

lemma regime_monotone (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
    typecheck ctx e fuel = .ok res →
    Regime.monotoneStep ctx.regime (ctxAfter ctx res).regime := by
  intro htc
  simpa [ctxAfter] using typecheck_regime_mono_main ctx e fuel res htc

end regime_monotone_proof

section advanceNextTag_monotone_proof

-- Helper lemmas for advanceNextTag functions monotonicity

lemma advanceNextTagForPred_ge (pred : Predicate) (t : Tag) :
  t ≤ advanceNextTagForPred pred t := by
  cases pred with
  | guardClosure k _ _ _ => simp [advanceNextTagForPred]
  | guardOnly k => simp [advanceNextTagForPred]
  | noPred => simp [advanceNextTagForPred]

lemma advanceNextTagForSyntaxPred_ge (pred : SyntaxPredicate) (t : Tag) :
  t ≤ advanceNextTagForSyntaxPred pred t := by
  cases pred with
  | guardClosure k _ _ => simp [advanceNextTagForSyntaxPred]
  | guardOnly k => simp [advanceNextTagForSyntaxPred]
  | noPred => simp [advanceNextTagForSyntaxPred]

lemma advanceNextTagForEffects_ge (effects : List Effect) (t : Tag) :
  t ≤ advanceNextTagForEffects effects t := by
  induction effects generalizing t with
  | nil => simp [advanceNextTagForEffects, List.foldl]
  | cons hd tl ih => exact Nat.le_trans (advanceNextTagForSyntaxPred_ge hd.pred t) (ih _)

end advanceNextTag_monotone_proof

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
              cases hft : etyp.isFunctionType with
              | true =>
                  -- Function types throw error, contradicts htc : throw ... = Except.ok res
                  simp [hft, throw] at htc
                  -- htc is now: Except.error ... = Except.ok res, which is a contradiction
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact le_rfl
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
          | guardClosure k _ _ _ =>
              simp at htc
              cases hft : etyp.isFunctionType with
              | true =>
                  -- Function types throw error, contradicts htc : throw ... = Except.ok res
                  simp [hft, throw] at htc
                  -- htc is now: Except.error ... = Except.ok res, which is a contradiction
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact le_rfl
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
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
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
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
  rcases hstruct with ⟨result1, _l, htc1, _hl, _hetyp, _hqtetyp, _hqtpoison, _hqtpred, _hmem, _htag, _hloc, hnexttag, _hregime⟩
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
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    res.nextTag' = result2.nextTag' := by
  intro htc
  have hstruct := typecheckAssign_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, _ls, htc1, _hetyp1, htc2, _hetyp2, _hloc, hnexttag, _⟩
  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
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
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, _hloc, hnexttag, _hregime⟩
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
      have hstruct := typecheckIf_structure ctx e1 e2 e3 (fuel' + 1) res htc
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      -- Extract nextTag equality from all four cases and prove monotonicity
      cases hstruct with
      | inl h1 =>
        -- R(k) = some true
        obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, _, hnexttag, _, _⟩ := h1
        have IH2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
        simp at IH2
        calc ctx.nextTag
          _ ≤ res2.nextTag' := IH2
          _ ≤ max res2.nextTag' res3.nextTag' := Nat.le_max_left _ _
          _ = res.nextTag' := hnexttag.symm
      | inr h_rest =>
        cases h_rest with
        | inl h2 =>
          -- R(k) = some false
          obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, _, hnexttag, _, _⟩ := h2
          have IH2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
          have IH3 := IH fuel' h_fuel e3 _ res3 htc3
          simp at IH2
          -- ctx.nextTag ≤ res2.nextTag' ≤ res3.nextTag' (from ctxFalse' advancing)
          calc ctx.nextTag
            _ ≤ res2.nextTag' := IH2
            _ ≤ res3.nextTag' := by omega
            _ ≤ max res2.nextTag' res3.nextTag' := Nat.le_max_right _ _
            _ = res.nextTag' := hnexttag.symm
        | inr h_rest2 =>
          cases h_rest2 with
          | inl h3 =>
            -- R(k) = none
            obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, _, hnexttag, _⟩ := h3
            have IH2 := IH fuel' h_fuel e2 _ res2 htc2
            calc ctx.nextTag
              _ ≤ res2.nextTag' := by omega
              _ ≤ max res2.nextTag' res3.nextTag' := Nat.le_max_left _ _
              _ = res.nextTag' := hnexttag.symm
          | inr h4 =>
            -- Standard (matchGuard fails)
            obtain ⟨⟨err, _hmatch_fail⟩, res1, htc1, _, res2, htc2, res3, htc3, _, _, _, hnexttag, _⟩ := h4
            have IH1 := IH fuel' h_fuel e1 ctx res1 htc1
            have IH2 := IH fuel' h_fuel e2 _ res2 htc2
            calc ctx.nextTag
              _ ≤ res1.nextTag' := IH1
              _ ≤ res2.nextTag' := IH2
              _ ≤ max res2.nextTag' res3.nextTag' := Nat.le_max_left _ _
              _ = res.nextTag' := hnexttag.symm

private lemma joinTypeResults_nextTag_eq_max
  (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult) :
    joinTypeResults ctx r rs = .ok res →
    res.nextTag' = List.max (r.nextTag' :: rs.map TypeResult.nextTag') (by intro h; cases h) := by
  intro hjoin
  -- Helper: the join fold computes the max of nextTag' across the list.
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvs acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_nextTag :
      ∀ (rs : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs = Except.ok acc' →
        acc'.2.2.2.2.2.2.2 = List.foldl max acc.2.2.2.2.2.2.2 (rs.map TypeResult.nextTag') := by
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
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
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
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
                TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      joinRegimes acc.2.2.2.2.2.1 result.regime',
                      max acc.2.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2.2 result.nextTag')
          -- Helper: the join fold preserves arrow structure
          -- Generalized to work with any p' tcls' that have signature st1 st2
          have h_fold_arrow :
              ∀ (rs : List TypeResult)
                (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                (p_acc : Poison) (tcls_acc : List FnTClosure),
                acc.1 = ETyp.arrow st1 st2 p_acc tcls_acc →
                List.foldlM joinStep acc rs = Except.ok acc' →
                ∃ (p' : Poison) (tcls' : List FnTClosure),
                  acc'.1 = ETyp.arrow st1 st2 p' tcls' := by
            intro rs acc acc' p_acc tcls_acc h_acc_arrow h_fold
            induction rs generalizing acc p_acc tcls_acc with
            | nil =>
                simp [List.foldlM_nil, pure, Except.pure] at h_fold
                cases h_fold
                exact ⟨p_acc, tcls_acc, h_acc_arrow⟩
            | cons x xs ih =>
                cases h_x_qt : x.qualType with
                | mk resEtyp resPoison resPred =>
                    have h_fold' := h_fold
                    simp [List.foldlM_cons, joinStep, h_x_qt, bind, Except.bind] at h_fold'
                    set acc_new :
                        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
                      (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                        joinMemEnvs acc.2.1 x.memEnv',
                        joinPoison acc.2.2.1 resPoison,
                        joinPredicates acc.2.2.2.1 resPred,
                        joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                        joinRegimes acc.2.2.2.2.2.1 x.regime',
                        max acc.2.2.2.2.2.2.1 x.nextLoc',
                        max acc.2.2.2.2.2.2.2 x.nextTag') with h_acc_new_def
                    have h_fold_tail : List.foldlM joinStep acc_new xs = Except.ok acc' := by
                      simpa [h_acc_new_def] using h_fold'
                    have h_acc_new_arrow :
                        ∃ (p' : Poison) (tcls' : List FnTClosure),
                          acc_new.1 = ETyp.arrow st1 st2 p' tcls' := by
                      cases h_resEtyp : resEtyp with
                      | arrow st1' st2' p2 tcls2 =>
                          by_cases hsig : (st1 == st1' && st2 == st2')
                          · refine ⟨joinPoison p_acc p2, mergeFnTClosures tcls_acc tcls2, ?_⟩
                            simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps, hsig]
                          · refine ⟨p_acc, tcls_acc, ?_⟩
                            simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps, hsig]
                      | _ =>
                          refine ⟨p_acc, tcls_acc, ?_⟩
                          simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps]
                    obtain ⟨p_new, tcls_new, h_acc_new_arrow_eq⟩ := h_acc_new_arrow
                    exact ih acc_new p_new tcls_new h_acc_new_arrow_eq h_fold_tail
          -- Apply the helper
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
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
                cases hjoin
                rfl
              -- Use h_fold_arrow to show a.1 is arrow
              have h_fold_arrow_result :=
                h_fold_arrow rs (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') a p tcls h_etyp_eq hfold
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
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
                TypeResult →
                  Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
              (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      joinRegimes acc.2.2.2.2.2.1 result.regime',
                      max acc.2.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2.2 result.nextTag')
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
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
          exact advanceNextTagForEffects_ge effects r1.nextTag'
      | nestedPfn innerArg innerArgTyp innerRet =>
          simp [pure, Except.pure] at happly
          cases happly
          exact advanceNextTagForEffects_ge effects r1.nextTag'
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
                    exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | int =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | bool =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | unit =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | string =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | arrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))
            | parrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  exact Nat.le_trans (advanceNextTagForEffects_ge effects r1.nextTag') (advanceNextTagForSyntaxPred_ge pred (advanceNextTagForEffects effects r1.nextTag'))

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
    regime := res2.regime',
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
                          regime := res2.regime',
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
                      exact advanceNextTagForSyntaxPred_ge pred res2.nextTag'
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
  runWhileFixpoint ctx e1 e2 fuel pureGuard guardOpt = .ok (pc, mem, tag, regime, nextLoc, nextTag) →
  ctx.nextTag ≤ nextTag := by
  intro hfix
  induction fuel generalizing ctx pureGuard guardOpt pc mem tag regime nextLoc nextTag with
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
            set bodyRegime : Regime := if pureGuard then ctx.regime else guardRes.regime' with hbodyRegime
            set bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv, regime := bodyRegime } with hbodyEnvCtx
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
            set newRegime : Regime := joinRegimes ctx.regime bodyRes.regime' with hnewRegime
            by_cases hfixpoint : newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv && newRegime.bound == ctx.regime.bound
            · simp at hfixpoint
              simp [if_pos hfixpoint] at hfix
              simp [pure, Except.pure] at hfix
              rcases hfix with ⟨_, _, _, _, _, hfix⟩
              subst nextTag
              apply hctx_body_nextTag
            · simp [pure, Except.pure] at hfix
              rw [if_neg (by simpa using hfixpoint)] at hfix
              set nextCtx : TypeContext :=
                { ctx with pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, regime := newRegime, nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' } with hnextCtx
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
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
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
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
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

-- Helper lemma for typecheckExternVal: nextTag monotonicity
lemma typecheckExternVal_nextTag_mono (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (res : TypeResult) :
  typecheckExternVal ctx typ poison pred = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
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
        exact advanceNextTagForPred_ge result.1.pred ctx.nextTag

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
            -- typecheckExternVal advances nextTag past predicate tag
            simp at htc
            exact typecheckExternVal_nextTag_mono ctx typ poison pred res htc
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

section typecheck_nextLoc_mono_proof

-- Helper lemmas for typecheck_nextLoc_mono proof

private lemma typecheckVar_nextLoc_mono (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
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
              cases hft : etyp.isFunctionType with
              | true =>
                  -- Function types throw error, contradicts htc : throw ... = Except.ok res
                  simp [hft, throw] at htc
                  -- htc is now: Except.error ... = Except.ok res, which is a contradiction
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact le_rfl
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
          | guardClosure k _ _ _ =>
              simp at htc
              cases hft : etyp.isFunctionType with
              | true =>
                  -- Function types throw error, contradicts htc : throw ... = Except.ok res
                  simp [hft, throw] at htc
                  -- htc is now: Except.error ... = Except.ok res, which is a contradiction
                  cases htc
              | false =>
                  simp [hft] at htc
                  cases htagopt : ctx.tagEnv.get? k with
                  | none =>
                      have htagopt' : ctx.tagEnv[k]? = none := by
                        simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      cases htc
                      exact le_rfl
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ := by
                            simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b with
                          | true =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              exact le_rfl

private lemma typecheckOp_nextLoc_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckOp_structure ctx e1 e2 op fuel res htc
  rcases hstruct with ⟨result1, result2, _result_etyp, htc1, htc2, _hop, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckOp at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextLoc : ctx'.nextLoc = result1.nextLoc' := by rfl
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = ctx'.nextLoc := h_ctx'_nextLoc.symm
        _ ≤ result2.nextLoc' := IH2
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckSeq_nextLoc_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
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
      have h_ctx'_nextLoc : ctx'.nextLoc = result1.nextLoc' := by simp [hctx', updateCtxFromResult]
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = ctx'.nextLoc := h_ctx'_nextLoc.symm
        _ ≤ res.nextLoc' := IH2

private lemma typecheckNewRef_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckNewRef ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckNewRef_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, _l, htc1, _hl, _hetyp, _hqtetyp, _hqtpoison, _hqtpred, _hmem, _htag, hnextloc, _hnexttag, _hregime⟩
  cases fuel with
  | zero => unfold typecheckNewRef at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ ≤ result1.nextLoc' + 1 := Nat.le_succ result1.nextLoc'
        _ = res.nextLoc' := hnextloc.symm

-- Helper lemma: List.foldl preserves initial value as lower bound when step function is monotone
private lemma List.foldl_ge_init_of_step_ge {α β : Type*} [Preorder α] {f : α → β → α}
    (h : ∀ acc x, acc ≤ f acc x) (init : α) (l : List β) :
    init ≤ List.foldl f init l := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      calc init
        _ ≤ f init x := h init x
        _ ≤ List.foldl f (f init x) xs := ih (f init x)

-- Helper lemma for typecheckAssign: nextLoc' is at least result2.nextLoc'
lemma typecheckAssign_preserves_nextLoc (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ctx' : TypeContext),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    ctx' = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' } ∧
    typecheckExpr ctx' e2 (fuel - 1) = .ok result2 ∧
    result2.nextLoc' ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckAssign_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ls, htc1, _hetyp1, htc2, _hetyp2, hnextloc, _hnexttag, _⟩
  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
  have h_ineq : result2.nextLoc' ≤ LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1)) := by
    have h_mono : ∀ acc l, acc ≤ max acc (l + 1) := by
      intro acc l
      exact Nat.le_max_left acc (l + 1)
    unfold LocSet.fold
    rw [ExtTreeSet.foldl_eq_foldl_toList]
    exact List.foldl_ge_init_of_step_ge h_mono result2.nextLoc' ls.toList
  -- Rewrite res.nextLoc' using hnextloc to match h_ineq
  rw [hnextloc]
  exact ⟨result1, result2, ctx', htc1, rfl, htc2, h_ineq⟩

private lemma typecheckAssign_nextLoc_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckAssign_preserves_nextLoc ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, hnextloc⟩
  cases fuel with
  | zero => unfold typecheckAssign at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextLoc : ctx'.nextLoc = result1.nextLoc' := by simp [hctx']
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = ctx'.nextLoc := h_ctx'_nextLoc.symm
        _ ≤ result2.nextLoc' := IH2
        _ ≤ res.nextLoc' := hnextloc

-- Helper lemma for typecheckDeref: all branches preserve nextLoc'
lemma typecheckDeref_preserves_nextLoc (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckDeref ctx e fuel = .ok res →
  ∃ (result1 : TypeResult),
    typecheckExpr ctx e (fuel - 1) = .ok result1 ∧
    res.nextLoc' = result1.nextLoc' := by
  intro htc
  have hstruct := typecheckDeref_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, hnextloc, _hnexttag, _hregime⟩
  exact ⟨result1, htc1, hnextloc⟩

private lemma typecheckDeref_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckDeref ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckDeref_preserves_nextLoc ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, hnextloc⟩
  cases fuel with
  | zero => unfold typecheckDeref at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckVlet_nextLoc_mono (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckVlet ctx x e1 e2 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckVlet_structure ctx x e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _hetyp, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckVlet at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by simpa using htc2
      have IH2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have h_ctx'_nextLoc : ctx'.nextLoc = result1.nextLoc' := by simp [hctx']
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = ctx'.nextLoc := h_ctx'_nextLoc.symm
        _ ≤ result2.nextLoc' := IH2
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckIf_nextLoc_mono (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckIf ctx e1 e2 e3 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  cases fuel with
  | zero => unfold typecheckIf at htc; simp at htc
  | succ fuel' =>
      have hstruct := typecheckIf_structure ctx e1 e2 e3 (fuel' + 1) res htc
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      -- Extract nextLoc equality from all four cases and prove monotonicity
      cases hstruct with
      | inl h1 =>
        -- R(k) = some true
        obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, hnextloc, _hnexttag, _, _⟩ := h1
        have IH2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
        simp at IH2
        calc ctx.nextLoc
          _ ≤ res2.nextLoc' := IH2
          _ ≤ max res2.nextLoc' res3.nextLoc' := Nat.le_max_left _ _
          _ = res.nextLoc' := hnextloc.symm
      | inr h_rest =>
        cases h_rest with
        | inl h2 =>
          -- R(k) = some false
          obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, hnextloc, _hnexttag, _, _⟩ := h2
          have IH2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
          have IH3 := IH fuel' h_fuel e3 _ res3 htc3
          simp at IH2
          -- ctx.nextLoc ≤ res2.nextLoc' ≤ res3.nextLoc' (from ctxFalse' advancing)
          calc ctx.nextLoc
            _ ≤ res2.nextLoc' := IH2
            _ ≤ res3.nextLoc' := by omega
            _ ≤ max res2.nextLoc' res3.nextLoc' := Nat.le_max_right _ _
            _ = res.nextLoc' := hnextloc.symm
        | inr h_rest2 =>
          cases h_rest2 with
          | inl h3 =>
            -- R(k) = none
            obtain ⟨k, deps, _, _, res1, htc1, _, res2, htc2, res3, htc3, _, _, hnextloc, _hnexttag, _⟩ := h3
            have IH2 := IH fuel' h_fuel e2 _ res2 htc2
            calc ctx.nextLoc
              _ ≤ res2.nextLoc' := by omega
              _ ≤ max res2.nextLoc' res3.nextLoc' := Nat.le_max_left _ _
              _ = res.nextLoc' := hnextloc.symm
          | inr h4 =>
            -- Standard (matchGuard fails)
            obtain ⟨⟨err, _hmatch_fail⟩, res1, htc1, _, res2, htc2, res3, htc3, _, _, hnextloc, _hnexttag, _⟩ := h4
            have IH1 := IH fuel' h_fuel e1 ctx res1 htc1
            have IH2 := IH fuel' h_fuel e2 _ res2 htc2
            calc ctx.nextLoc
              _ ≤ res1.nextLoc' := IH1
              _ ≤ res2.nextLoc' := IH2
              _ ≤ max res2.nextLoc' res3.nextLoc' := Nat.le_max_left _ _
              _ = res.nextLoc' := hnextloc.symm

private lemma joinTypeResults_nextLoc_eq_max
  (ctx : TypeContext) (r : TypeResult) (rs : List TypeResult) (res : TypeResult) :
    joinTypeResults ctx r rs = .ok res →
    res.nextLoc' = List.max (r.nextLoc' :: rs.map TypeResult.nextLoc') (by intro h; cases h) := by
  intro hjoin
  -- Helper: the join fold computes the max of nextLoc' across the list.
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvs acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_nextLoc :
      ∀ (rs : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs = Except.ok acc' →
        acc'.2.2.2.2.2.2.1 = List.foldl max acc.2.2.2.2.2.2.1 (rs.map TypeResult.nextLoc') := by
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
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              simp
              have h_fold := h_fold_nextLoc rs _ _ hfold
              -- List.max on a non-empty list is foldl max.
              simpa [List.max] using h_fold

/-- joinTypeResults preserves arrow/parrow structure: if first result is arrow st1 st2, result is arrow st1 st2.
    TODO: this is not a good way to prove this. We need to define helper lemma on FoldM which holds a pairwise property and proves that it holds for the resut!
-/
private lemma joinTypeResults_preserves_arrow_structure_nextLoc
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
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
                TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      joinRegimes acc.2.2.2.2.2.1 result.regime',
                      max acc.2.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2.2 result.nextTag')
          -- Helper: the join fold preserves arrow structure
          -- Generalized to work with any p' tcls' that have signature st1 st2
          have h_fold_arrow :
              ∀ (rs : List TypeResult)
                (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
                (p_acc : Poison) (tcls_acc : List FnTClosure),
                acc.1 = ETyp.arrow st1 st2 p_acc tcls_acc →
                List.foldlM joinStep acc rs = Except.ok acc' →
                ∃ (p' : Poison) (tcls' : List FnTClosure),
                  acc'.1 = ETyp.arrow st1 st2 p' tcls' := by
            intro rs acc acc' p_acc tcls_acc h_acc_arrow h_fold
            induction rs generalizing acc p_acc tcls_acc with
            | nil =>
                simp [List.foldlM_nil, pure, Except.pure] at h_fold
                cases h_fold
                exact ⟨p_acc, tcls_acc, h_acc_arrow⟩
            | cons x xs ih =>
                cases h_x_qt : x.qualType with
                | mk resEtyp resPoison resPred =>
                    have h_fold' := h_fold
                    simp [List.foldlM_cons, joinStep, h_x_qt, bind, Except.bind] at h_fold'
                    set acc_new :
                        (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
                      (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                        joinMemEnvs acc.2.1 x.memEnv',
                        joinPoison acc.2.2.1 resPoison,
                        joinPredicates acc.2.2.2.1 resPred,
                        joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                        joinRegimes acc.2.2.2.2.2.1 x.regime',
                        max acc.2.2.2.2.2.2.1 x.nextLoc',
                        max acc.2.2.2.2.2.2.2 x.nextTag') with h_acc_new_def
                    have h_fold_tail : List.foldlM joinStep acc_new xs = Except.ok acc' := by
                      simpa [h_acc_new_def] using h_fold'
                    have h_acc_new_arrow :
                        ∃ (p' : Poison) (tcls' : List FnTClosure),
                          acc_new.1 = ETyp.arrow st1 st2 p' tcls' := by
                      cases h_resEtyp : resEtyp with
                      | arrow st1' st2' p2 tcls2 =>
                          by_cases hsig : (st1 == st1' && st2 == st2')
                          · refine ⟨joinPoison p_acc p2, mergeFnTClosures tcls_acc tcls2, ?_⟩
                            simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps, hsig]
                          · refine ⟨p_acc, tcls_acc, ?_⟩
                            simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps, hsig]
                      | _ =>
                          refine ⟨p_acc, tcls_acc, ?_⟩
                          simp [h_acc_new_def, h_acc_arrow, h_resEtyp, joinETyps]
                    obtain ⟨p_new, tcls_new, h_acc_new_arrow_eq⟩ := h_acc_new_arrow
                    exact ih acc_new p_new tcls_new h_acc_new_arrow_eq h_fold_tail
          -- Apply the helper
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
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
                cases hjoin
                rfl
              -- Use h_fold_arrow to show a.1 is arrow
              have h_fold_arrow_result :=
                h_fold_arrow rs (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') a p tcls h_etyp_eq hfold
              obtain ⟨p', tcls', h_a1_arrow⟩ := h_fold_arrow_result
              -- Now show res.qualType.etyp = arrow st1 st2 p' tcls'
              use p', tcls'
              rw [h_res_etyp, h_a1_arrow]


/-- joinTypeResults sets pred to noPred when the joined etyp is a function type (arrow or parrow).
    NOTE: This lemma may be difficult to prove directly because it requires extracting
    the structure from the nested match in joinTypeResults. Consider using a stronger
    lemma that extracts the full structure first. -/
private lemma joinTypeResults_pred_noPred_for_function_types_nextLoc
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
              (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
                TypeResult →
                  Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
            fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
              (result : TypeResult) =>
              match result.qualType with
              | ⟨resEtyp, resPoison, resPred⟩ =>
                  Except.ok
                    (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                      joinMemEnvs acc.2.1 result.memEnv',
                      joinPoison acc.2.2.1 resPoison,
                      joinPredicates acc.2.2.2.1 resPred,
                      joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
                      joinRegimes acc.2.2.2.2.2.1 result.regime',
                      max acc.2.2.2.2.2.2.1 result.nextLoc',
                      max acc.2.2.2.2.2.2.2 result.nextTag')
          cases hfold :
              List.foldlM joinStep
                (etyp, r.memEnv', poison, pred, r.tagEnv', r.regime', r.nextLoc', r.nextTag') rs with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok a =>
              erw [hfold] at hjoin
              -- At this point `hjoin` pins down `res` (including the `finalPred` match).
              simp at hjoin
              cases hjoin
              -- Destructure the fold accumulator so we can case-split on the joined etyp directly.
              rcases a with ⟨joinedEtyp, joinedMemEnv, joinedPoison, joinedPred, joinedTagEnv, joinedRegime, maxNextLoc, maxNextTag⟩
              -- Reduce the goal to the `finalPred` match, and eliminate non-function cases
              have hfun' : joinedEtyp.isArrow = true ∨ joinedEtyp.isParrow = true := by
                simpa using hfun
              cases joinedEtyp <;>
                (simp [ETyp.isArrow, ETyp.isParrow] at hfun' <;> simp)

private lemma returnSpecToQTyp_preserves_nextLoc
  (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
  (varEnv : VarTypeEnv) (nextLoc : Loc) (ret : QTyp × Loc) :
  returnSpecToQTyp typ poison pred varEnv nextLoc = .ok ret →
  ret.2 = nextLoc := by
  intro h
  unfold returnSpecToQTyp at h
  cases typ with
  | int | bool | unit | string =>
      cases hpred : attachVarEnvToPredicate pred varEnv with
      | error _ =>
          rw [hpred] at h
          simp [bind, Except.bind, pure, Except.pure] at h
      | ok _ =>
          rw [hpred] at h
          simp [bind, Except.bind, pure, Except.pure] at h
          exact (congrArg Prod.snd h).symm
  | ref _ =>
      simp [bind, Except.bind] at h
  | arrow _ _ =>
      simp [bind, Except.bind] at h


private lemma applyFnTClosure_nextLoc_mono
  (tcl : FnTClosure) (ctx : TypeContext)
  (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' → ctx'.nextLoc ≤ res'.nextLoc') :
  applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 fuel = .ok r2 →
  r1.nextLoc' ≤ r2.nextLoc' := by
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
            have hret_nextLoc : hret.2 = r1.nextLoc' := by
              exact returnSpecToQTyp_preserves_nextLoc _ _ _ _ _ _ retVal
            cases hret_etyp : hret.1.etyp with
            | ref t ls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                  split at happly
                  · cases happly
                  · cases happly
                    simp [hret_nextLoc]
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | int =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | bool =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | unit =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | string =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | arrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]
            | parrow arg retTy poison tcls =>
                simp [hret_etyp] at happly
                split at happly
                · simp [Functor.map, Except.map] at happly
                · simp [pure, Except.pure] at happly
                  cases happly
                  simp [hret_nextLoc]

private lemma typecheckApp_nextLoc_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckApp ctx e1 e2 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
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
    regime := res2.regime',
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
    -- ctx.nextLoc <= res1.nextLoc (by IH on htce1)
    -- res1.nextLoc = ctx'.nextLoc
    -- ctx'.nextLoc <= res2.nextLoc (by IH on hcte2)
    -- res2.nextLoc <= r.nextLoc (by applyFnTClosure_nextLoc_mono)
    -- forall r in rs', res2.nextLoc <= r.nextLoc (by applyFnTClosure_nextLoc_mono)
    -- res2.nextLoc <= max (r.nextLoc, map rs' .nextLoc) (follows from above)
    -- max (res2.nextLoc, map rs' .nextLoc) = res.nextLoc (by joinTypeResults_nextLoc_eq_max)
    have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
    have hcte2' : typecheck ctx e2 fuel' = .ok res2 := by
      simpa [typecheck] using hcte2
    have IH2 := IH fuel' h_fuel e2 ctx res2 hcte2'
    have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by
      simpa [typecheck] using htce1
    have _IH1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextLoc ≤ res'.nextLoc' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res2.nextLoc' ≤ r.nextLoc' := by
      exact applyFnTClosure_nextLoc_mono f ctx t1 t2 p poison1 etyp2 poison2 pred2 res2 r fuel' IH' happly
    have h_join :
        res.nextLoc' =
          List.max (r.nextLoc' :: rs'.map TypeResult.nextLoc') (by intro h; cases h) :=
      joinTypeResults_nextLoc_eq_max ctx r rs' res htc
    have h_r_le_res : r.nextLoc' ≤ res.nextLoc' := by
      have h_r_le_max :
          r.nextLoc' ≤
            List.max (r.nextLoc' :: rs'.map TypeResult.nextLoc') (by intro h; cases h) := by
        apply List.le_max_of_mem
        simp
      simpa [h_join] using h_r_le_max
    calc
      ctx.nextLoc ≤ res2.nextLoc' := IH2
      _ = ctx'.nextLoc := by simp [hctx']
      _ ≤ r.nextLoc' := h_r
      _ ≤ res.nextLoc' := h_r_le_res
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
          typecheck ctx'' e m = .ok res' → ctx''.nextLoc ≤ res'.nextLoc' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res2.nextLoc' ≤ r.nextLoc' := by
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
                          regime := res2.regime',
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
                      have hret_nextLoc : ret.2 = res2.nextLoc' := by
                        exact returnSpecToQTyp_preserves_nextLoc _ _ _ _ _ _ hret
                      simp [hret_nextLoc]
              | nestedFn innerArg innerArgTyp innerRet innerEffects =>
                  simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
              | nestedPfn innerArg innerArgTyp innerRet =>
                  simp [pure, Except.pure] at happly
                  cases happly
                  exact le_rfl
    have h_join :
        res.nextLoc' =
          List.max (r.nextLoc' :: rs'.map TypeResult.nextLoc') (by intro h; cases h) :=
      joinTypeResults_nextLoc_eq_max ctx r rs' res htc
    have h_r_le_res : r.nextLoc' ≤ res.nextLoc' := by
      have h_r_le_max :
          r.nextLoc' ≤
            List.max (r.nextLoc' :: rs'.map TypeResult.nextLoc') (by intro h; cases h) := by
        apply List.le_max_of_mem
        simp
      simpa [h_join] using h_r_le_max
    calc
      ctx.nextLoc ≤ res2.nextLoc' := IH2
      _ = ctx'.nextLoc := by simp [hctx']
      _ ≤ r.nextLoc' := h_r
      _ ≤ res.nextLoc' := h_r_le_res

private lemma runWhileFixpoint_nextLoc_mono
  (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (pureGuard : Bool) (guardOpt : Option (Tag × Deps))
  (pc : Poison) (mem : MemoryTypeEnv) (tag : TagEnv) (nextLoc : Loc) (nextTag : Tag)
  (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
    typecheck ctx' e m = .ok res' →
    ctx'.nextLoc ≤ res'.nextLoc') :
  runWhileFixpoint ctx e1 e2 fuel pureGuard guardOpt = .ok (pc, mem, tag, regime, nextLoc, nextTag) →
  ctx.nextLoc ≤ nextLoc := by
  intro hfix
  induction fuel generalizing ctx pureGuard guardOpt pc mem tag regime nextLoc nextTag with
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
            have hguard_nextLoc : ctxForGuard.nextLoc ≤ guardRes.nextLoc' :=
              IH fuel' (lt_add_one fuel') e1 ctxForGuard guardRes htc_guard
            have hctx_nextLoc_le : ctx.nextLoc ≤ guardRes.nextLoc' := by
              have hctxForGuard_nextLoc : ctxForGuard.nextLoc = ctx.nextLoc := by
                cases pureGuard <;> simp [hctxForGuard]
              simpa [hctxForGuard_nextLoc] using hguard_nextLoc
            set bodyPcCtx : TypeContext := { ctx with pc := joinPoison ctx.pc p1 } with hbodyPcCtx
            set bodyTagEnv : TagEnv := if pureGuard then ctx.tagEnv else guardRes.tagEnv' with hbodyTagEnv
            set bodyRegime : Regime := if pureGuard then ctx.regime else guardRes.regime' with hbodyRegime
            set bodyEnvCtx : TypeContext := { bodyPcCtx with memEnv := guardRes.memEnv', tagEnv := bodyTagEnv, regime := bodyRegime } with hbodyEnvCtx
            set bodyCtxBase : TypeContext := { bodyEnvCtx with nextLoc := guardRes.nextLoc', nextTag := guardRes.nextTag', pureCtx := ctx.pureCtx } with hbodyCtxBase
            set bodyCtx : TypeContext :=
              match guardOpt with
              | some (k, deps) => { bodyCtxBase with tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
              | none => bodyCtxBase with hbodyCtx
            have htc_body : typecheck bodyCtx e2 fuel' = .ok bodyRes := by
              simp [typecheck, bodyCtx]
              cases guardOpt <;> simp at hbody <;> simp <;> apply hbody
            have hbody_nextLoc : bodyCtx.nextLoc ≤ bodyRes.nextLoc' :=
              IH fuel' (lt_add_one fuel') e2 bodyCtx bodyRes htc_body
            have hctx_body_nextLoc : ctx.nextLoc ≤ bodyRes.nextLoc' := by
              have hbodyCtx_nextLoc : bodyCtx.nextLoc = guardRes.nextLoc' := by
                cases guardOpt <;> simp [hbodyCtx, hbodyCtxBase]
              calc
                ctx.nextLoc ≤ guardRes.nextLoc' := hctx_nextLoc_le
                _ = bodyCtx.nextLoc := hbodyCtx_nextLoc.symm
                _ ≤ bodyRes.nextLoc' := hbody_nextLoc
            set newPc : Poison := joinPoison ctx.pc p2 with hnewPc
            set restrictedBodyEnv : MemoryTypeEnv := restrictMemEnv bodyRes.memEnv' ctx.memEnv with hrestrictedBodyEnv
            set newMemEnv : MemoryTypeEnv := joinMemEnvs ctx.memEnv restrictedBodyEnv with hnewMemEnv
            set newTagEnv : TagEnv := joinTagEnvs ctx.tagEnv bodyRes.tagEnv' with hnewTagEnv
            set newRegime : Regime := joinRegimes ctx.regime bodyRes.regime' with hnewRegime
            by_cases hfixpoint : newMemEnv == ctx.memEnv && newPc == ctx.pc && newTagEnv == ctx.tagEnv && newRegime.bound == ctx.regime.bound
            · simp at hfixpoint
              simp [if_pos hfixpoint] at hfix
              simp [pure, Except.pure] at hfix
              rcases hfix with ⟨_, _, _, _, _, hfix⟩
              subst nextLoc
              apply hctx_body_nextLoc
            · simp [pure, Except.pure] at hfix
              rw [if_neg (by simpa using hfixpoint)] at hfix
              set nextCtx : TypeContext :=
                { ctx with pc := newPc, memEnv := newMemEnv, tagEnv := newTagEnv, regime := newRegime, nextLoc := bodyRes.nextLoc', nextTag := bodyRes.nextTag' } with hnextCtx
              have hnextCtx_nextLoc : nextCtx.nextLoc = bodyRes.nextLoc' := by
                simp [hnextCtx]
              have ih' : nextCtx.nextLoc ≤ nextLoc := by
                apply ih _ _ _ _ _ _ _ _ _ hfix
                intros fuel'' hfuel'' expr tc r htc
                apply IH fuel'' (by linarith) expr tc r htc
              calc
                ctx.nextLoc ≤ bodyRes.nextLoc' := hctx_body_nextLoc
                _ = nextCtx.nextLoc := hnextCtx_nextLoc.symm
                _ ≤ nextLoc := ih'

private lemma typecheckWhile_nextLoc_mono (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckWhile ctx e1 e2 fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
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
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_nextLoc_mono ctx e1 e2 fuel'' true (some (k, deps))
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
                  rcases r with ⟨finalPc, finalMemEnv, finalTagEnv, finalRegime, finalNextLoc, finalNextTag⟩
                  simp [hfix] at htc
                  cases htc
                  dsimp
                  apply runWhileFixpoint_nextLoc_mono ctx e1 e2 fuel'' false none
                        finalPc finalMemEnv finalTagEnv finalNextLoc finalNextTag _ hfix
                  intros fuel hfuel expr ctx r hctx
                  apply IH fuel (by linarith) expr ctx r hctx

private lemma typecheckRand_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckRand ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckRand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hetyp, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckRand at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckFrand_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckFrand ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  -- Use the structure lemma to extract the intermediate result
  have hstruct := typecheckFrand_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, hnextloc, _hnexttag, _hetyp, _hpoison, _hguard⟩
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
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckPrintInt_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckPrintInt ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckPrintInt_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckPrintInt at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckPrintString_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckPrintString ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckPrintString_structure ctx e fuel res htc
  rcases hstruct with ⟨result1, htc1, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckPrintString at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma typecheckUnaryOp_nextLoc_mono (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc') :
  typecheckUnaryOp ctx op e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  have hstruct := typecheckUnaryOp_structure ctx op e fuel res htc
  rcases hstruct with ⟨result1, _result_etyp, htc1, _hop, _hmem, _htag, hnextloc, _hnexttag, _⟩
  cases fuel with
  | zero => unfold typecheckUnaryOp at htc; simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e fuel' = .ok result1 := by simpa using htc1
      have IH1 := IH fuel' h_fuel e ctx result1 htc1_simp
      calc ctx.nextLoc
        _ ≤ result1.nextLoc' := IH1
        _ = res.nextLoc' := hnextloc.symm

private lemma surfaceSpecToQTyp_nextLoc_mono
  (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
  (varEnv : VarTypeEnv) (ctx : TypeContext) (result : QTyp × TypeContext) :
  surfaceSpecToQTyp typ poison pred varEnv ctx = .ok result →
  ctx.nextLoc ≤ result.2.nextLoc := by
  intro h
  unfold surfaceSpecToQTyp at h
  cases typ with
  | int | bool | unit | string =>
      cases hpred : attachVarEnvToPredicate pred varEnv with
      | error _ =>
          rw [hpred] at h
          simp [bind, Except.bind, pure, Except.pure] at h
      | ok _ =>
          rw [hpred] at h
          simp [bind, Except.bind, pure, Except.pure] at h
          have hs : result.2 = ctx := (congrArg Prod.snd h).symm
          simp [hs]
  | ref t =>
      cases t with
      | int =>
          cases hpred : attachVarEnvToPredicate pred varEnv <;>
            simp [hpred, freshTLoc, bind, Except.bind, pure, Except.pure] at h
          · cases h
          · have hinner :
                surfaceSpecToQTyp Typ.int false SyntaxPredicate.noPred varEnv
                  { ctx with nextLoc := ctx.nextLoc + 1 } =
                .ok ({ etyp := ETyp.int, poison := false, pred := Predicate.noPred },
                    { ctx with nextLoc := ctx.nextLoc + 1 }) := by
                simp [surfaceSpecToQTyp, attachVarEnvToPredicate, bind, Except.bind, pure, Except.pure]
            rw [hinner] at h
            simp at h
            have hs : result.2.nextLoc = ctx.nextLoc + 1 := (congrArg (fun pr => pr.2.nextLoc) h).symm
            simp [hs]
      | bool | unit | string | ref _ | arrow _ _ =>
          simp [bind, Except.bind] at h
  | arrow _ _ =>
      simp [bind, Except.bind] at h

-- Helper lemma for typecheckExternVal: nextLoc is monotone.
lemma typecheckExternVal_nextLoc_mono (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) (res : TypeResult) :
  typecheckExternVal ctx typ poison pred = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  unfold typecheckExternVal at htc
  split at htc
  · -- error case: clean types cannot have predicates
    simp at htc
  · -- error case: clean types cannot have predicates (second pattern)
    simp at htc
  · -- success case
    simp [bind, Except.bind] at htc
    cases hsurf : surfaceSpecToQTyp typ poison pred ctx.varEnv ctx with
    | error _ => simp [hsurf] at htc
    | ok result =>
        have hmono : ctx.nextLoc ≤ result.2.nextLoc :=
          surfaceSpecToQTyp_nextLoc_mono typ poison pred ctx.varEnv ctx result hsurf
        simp [hsurf, pure, Except.pure] at htc
        cases htc
        simpa using hmono

-- Helper lemma for typecheckExternFn: always preserves nextLoc
lemma typecheckExternFn_preserves_nextLoc (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) (res : TypeResult) :
  typecheckExternFn ctx arg argTyp retSpec effects = .ok res →
  res.nextLoc' = ctx.nextLoc := by
  intro htc
  unfold typecheckExternFn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

-- Helper lemma for typecheckExternPfn: always preserves nextLoc
lemma typecheckExternPfn_preserves_nextLoc (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (res : TypeResult) :
  typecheckExternPfn ctx arg argTyp retSpec = .ok res →
  res.nextLoc' = ctx.nextLoc := by
  intro htc
  unfold typecheckExternPfn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

private lemma typecheck_nextLoc_mono_main : ∀ (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult),
  typecheck ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro ctx e fuel res htc
  revert ctx e res htc
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res htc
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      ctx'.nextLoc ≤ res'.nextLoc' := by
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
          ctx'.nextLoc ≤ res'.nextLoc' := by
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
            exact typecheckVar_nextLoc_mono ctx x res htc
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
            -- typecheckExternVal may allocate for `ref` specs, but never decreases nextLoc.
            simp at htc
            exact typecheckExternVal_nextLoc_mono ctx typ poison pred res htc
        | externFn arg argTyp retSpec effects =>
            -- typecheckExternFn returns nextLoc' := ctx.nextLoc
            simp at htc
            have h_preserve := typecheckExternFn_preserves_nextLoc ctx arg argTyp retSpec effects res htc
            rw [h_preserve]
        | externPfn arg argTyp retSpec =>
            -- typecheckExternPfn returns nextLoc' := ctx.nextLoc
            simp at htc
            have h_preserve := typecheckExternPfn_preserves_nextLoc ctx arg argTyp retSpec res htc
            rw [h_preserve]
        | op e1 op e2 =>
            simp at htc
            exact typecheckOp_nextLoc_mono ctx e1 e2 fuel' op res IH_fuel' htc
        | unaryop op e1 =>
            simp at htc
            exact typecheckUnaryOp_nextLoc_mono ctx op e1 fuel' res IH_fuel' htc
        | ite e1 e2 e3 =>
            simp at htc
            exact typecheckIf_nextLoc_mono ctx e1 e2 e3 fuel' res IH_fuel' htc
        | newRef e1 =>
            simp at htc
            exact typecheckNewRef_nextLoc_mono ctx e1 fuel' res IH_fuel' htc
        | assign e1 e2 =>
            simp at htc
            exact typecheckAssign_nextLoc_mono ctx e1 e2 fuel' res IH_fuel' htc
        | deref e1 =>
            simp at htc
            exact typecheckDeref_nextLoc_mono ctx e1 fuel' res IH_fuel' htc
        | seq e1 e2 =>
            simp at htc
            exact typecheckSeq_nextLoc_mono ctx e1 e2 fuel' res IH_fuel' htc
        | vlet x e1 e2 =>
            simp at htc
            exact typecheckVlet_nextLoc_mono ctx x e1 e2 fuel' res IH_fuel' htc
        | app e1 e2 =>
            simp at htc
            exact typecheckApp_nextLoc_mono ctx e1 e2 fuel' res IH_fuel' htc
        | kwhile e1 e2 =>
            simp at htc
            exact typecheckWhile_nextLoc_mono ctx e1 e2 fuel' res IH_fuel' htc
        | rand e1 =>
            simp at htc
            exact typecheckRand_nextLoc_mono ctx e1 fuel' res IH_fuel' htc
        | frand e1 =>
            simp at htc
            exact typecheckFrand_nextLoc_mono ctx e1 fuel' res IH_fuel' htc
        | printInt e1 =>
            simp at htc
            exact typecheckPrintInt_nextLoc_mono ctx e1 fuel' res IH_fuel' htc
        | printString e1 =>
            simp at htc
            exact typecheckPrintString_nextLoc_mono ctx e1 fuel' res IH_fuel' htc

end typecheck_nextLoc_mono_proof

-- `nextLoc` is monotone for successful typechecking: typing never decreases the fresh-location supply.
-- This is analogous to typecheck_nextTag_mono but for memory locations.
lemma typecheck_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  exact typecheck_nextLoc_mono_main ctx e fuel res htc


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

/-- If a location is in joinMemEnvs, it was in at least one of the inputs. -/
lemma joinMemEnvs_contains_implies_or (env1 env2 : MemoryTypeEnv) (l : Loc) :
  (joinMemEnvs env1 env2).contains l → env1.contains l ∨ env2.contains l := by
  intro hcontains
  by_cases h1 : env1.contains l = true
  · left; exact h1
  · by_cases h2 : env2.contains l = true
    · right; exact h2
    · exfalso
      have h1not : l ∉ env1 := (Std.ExtTreeMap.contains_iff_mem).not.1 h1
      have h2not : l ∉ env2 := (Std.ExtTreeMap.contains_iff_mem).not.1 h2
      have h1_none : env1[l]? = none := Std.ExtTreeMap.getElem?_eq_none h1not
      have h2_none : env2[l]? = none := Std.ExtTreeMap.getElem?_eq_none h2not
      have hjoin_none : (joinMemEnvs env1 env2)[l]? = none := by
        classical
        let f : Loc → Option QTyp → Option QTyp → Option QTyp := fun _ oq1 oq2 =>
          match oq1, oq2 with
          | some qt1, none => some qt1
          | none, some qt2 => some qt2
          | some qt1, some qt2 =>
            let ⟨t1, p1, pred1⟩ := qt1
            let ⟨t2, p2, pred2⟩ := qt2
            if t1 == t2 then
              let p := joinPoison p1 p2
              let pred := joinPredicates pred1 pred2
              some ⟨t1, p, pred⟩
            else
              none
          | none, none => none
        -- unfold joinMemEnvs/ combineExtTreeMaps and reason on membership in `ks`
        dsimp [joinMemEnvs, f, combineExtTreeMaps]
        change
          (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv))[l]? = none
        by_cases h_in : l ∈ (env1.keys ++ env2.keys).eraseDups
        · have hgo :=
            combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv) l h_in
          have hfun : f l (env1.get? l) (env2.get? l) = none := by
            simp [ExtTreeMap.get?_eq_getElem?, h1_none, h2_none, f]
          -- rewrite the RHS to `none` and close
          rw [hfun] at hgo
          exact hgo
        · have hgo :=
            combineExtTreeMaps_go_get_not_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv) l h_in
          have hempty : (({} : MemoryTypeEnv)[l]?) = none := by
            rfl
          rw [hempty] at hgo
          exact hgo
      have hmem : l ∈ joinMemEnvs env1 env2 := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hsome : Option.isSome (joinMemEnvs env1 env2)[l]? :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      simp [hjoin_none] at hsome

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
  intro hjoin hclean henv1
  classical
  cases h1 : env1.lookup l with
  | none =>
      exact (henv1 h1).elim
  | some qt1 =>
      -- Unfold the join at `l` and analyze the branch on env2.
      let f : Loc → Option QTyp → Option QTyp → Option QTyp := fun _ oq1 oq2 =>
        match oq1, oq2 with
        | some qt1, none => some qt1
        | none, some qt2 => some qt2
        | some qt1, some qt2 =>
          let ⟨t1, p1, pred1⟩ := qt1
          let ⟨t2, p2, pred2⟩ := qt2
          if t1 == t2 then
            let p := joinPoison p1 p2
            let pred := joinPredicates pred1 pred2
            some ⟨t1, p, pred⟩
          else
            none
        | none, none => none
      have hjoin' :
          (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv))[l]? = some qt := by
        simpa [joinMemEnvs, MemoryTypeEnv.lookup, f, combineExtTreeMaps] using hjoin
      by_cases h_in : l ∈ (env1.keys ++ env2.keys).eraseDups
      · have hgo :=
          combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
            ({} : MemoryTypeEnv) l h_in
        have hgo' :
            (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
                ({} : MemoryTypeEnv))[l]? =
              f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) := by
          -- eliminate the wrapper `match` in `hgo` by case splitting on the option
          cases hopt : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) with
          | none =>
              have hgo' := hgo
              rw [hopt] at hgo'
              exact hgo'
          | some v =>
              have hgo' := hgo
              rw [hopt] at hgo'
              exact hgo'
        have hmatch :
            f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) = some qt := by
          exact Eq.trans hgo'.symm hjoin'
        have h1' : ExtTreeMap.get? env1 l = some qt1 := by
          simpa [MemoryTypeEnv.lookup] using h1
        have htp : qt1.etyp = qt.etyp ∧ qt1.poison = false := by
          cases h2 : env2.lookup l with
          | none =>
              have h2' : ExtTreeMap.get? env2 l = none := by
                simpa [MemoryTypeEnv.lookup] using h2
              have hqt : qt1 = qt := by
                have hmatch' := hmatch
                rw [h1', h2'] at hmatch'
                simp [f] at hmatch'
                simp [hmatch']
              exact ⟨by simp [hqt], by simpa [hqt] using hclean⟩
          | some qt2 =>
              have h2' : ExtTreeMap.get? env2 l = some qt2 := by
                simpa [MemoryTypeEnv.lookup] using h2
              cases qt1 with
              | mk t1 p1 pred1 =>
                  cases qt2 with
                  | mk t2 p2 pred2 =>
                      have hmatch' := hmatch
                      rw [h1', h2'] at hmatch'
                      simp [f] at hmatch'
                      by_cases hteq : t1 = t2
                      · have hqt :
                          qt =
                            ⟨t1, joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
                          have hmatch'' := hmatch'
                          simp [hteq] at hmatch''
                          have hqt' :
                              qt =
                                ⟨t2, joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
                            simpa using hmatch''.symm
                          simpa [hteq] using hqt'
                        have hclean' : joinPoison p1 p2 = false := by
                          simpa [hqt] using hclean
                        have hpo' : p1 = false ∧ p2 = false :=
                          (Bool.or_eq_false_iff).1 (by simpa [joinPoison] using hclean')
                        exact ⟨by simp [hqt], by simpa using hpo'.1⟩
                      · -- if types disagree, joinMemEnvs would return none
                        simp [hteq] at hmatch'
        exact ⟨qt1, ⟨rfl, ⟨htp.1, htp.2⟩⟩⟩
      · -- key not in domain list -> join result is none, contradicting hjoin
        have hgo :=
          combineExtTreeMaps_go_get_not_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
            ({} : MemoryTypeEnv) l h_in
        have hempty : (({} : MemoryTypeEnv)[l]?) = none := by
          rfl
        rw [hempty] at hgo
        -- contradiction with `hjoin' : ... = some qt`
        simp [hjoin'] at hgo

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
