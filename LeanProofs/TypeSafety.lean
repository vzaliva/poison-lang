-- Common type safety definitions for the Poison Language
--
-- This file contains shared definitions used by both Progress and Preservation
-- properties, including evaluation relations and runtime context instantiation.

import LeanPoison.Syntax
import LeanProofs.Equality
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanProofs.Aux
import Init.Data.List.Lemmas
import Std.Data.ExtTreeSet.Lemmas
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

open Std

-- ================================================================
-- OpEType / opEType? (moved from Properties for type-safety use)
-- ================================================================

theorem OpEType.sound {o t₁ t₂ r}
  (h : OpEType o t₁ t₂ r) : opEType? o t₁ t₂ = some r := by
  cases h <;> simp [opEType?]

theorem OpEType.complete {o t₁ t₂ r}
  (h : opEType? o t₁ t₂ = some r) : OpEType o t₁ t₂ r := by
  cases o <;> cases t₁ <;> cases t₂
   <;> simp [opEType?] at h <;> rw [<-h] <;> constructor

theorem opEType?_iff (o t₁ t₂ r) :
  opEType? o t₁ t₂ = some r ↔ OpEType o t₁ t₂ r :=
  ⟨OpEType.complete, OpEType.sound⟩

-- ================================================================
-- MemoryTypeEnv (moved from Properties)
-- ================================================================

instance : LawfulBEq MemEntry where
  eq_of_beq := @fun a b h => by
    cases a with
    | mk pa preda =>
    cases b with
    | mk pb predb =>
    simp only [BEq.beq] at h
    obtain ⟨hp, hpred⟩ := (Bool.and_eq_true (pa == pb) (preda == predb)).mp h
    congr
    · exact of_decide_eq_true hp
    · exact (inferInstance : LawfulBEq Predicate).eq_of_beq hpred
  rfl {a} := by
    cases a with | mk po preda =>
    simp only [BEq.beq]
    exact (Bool.and_eq_true (po == po) (preda == preda)).mpr
      ⟨by cases po <;> rfl, (inferInstance : LawfulBEq Predicate).rfl (a := preda)⟩

theorem MemoryTypeEnv_eq_equiv {m₁ m₂ : MemoryTypeEnv} (h : m₁ = m₂) : m₁.equiv m₂ := by
  rw [h]
  simp only [MemoryTypeEnv.equiv]
  have : LawfulBEq (List (Loc × MemEntry)) := inferInstance
  exact this.rfl

/-- Memory lookup builds QTyp with etyp = ETyp.int (memory stores only integers). -/
lemma memEnv_lookup_etyp_int (env : MemoryTypeEnv) (l : Loc) (qt : QTyp) (h : env.lookup l = some qt) :
    qt.etyp = ETyp.int := by
  unfold MemoryTypeEnv.lookup at h
  generalize env.get? l = opt at h
  cases opt with
  | none => simp only [Option.map] at h; nomatch h
  | some e =>
    simp only [Option.map] at h
    have heq : qt = ⟨ETyp.int, e.poison, e.pred⟩ := (Option.some.inj h).symm
    rw [heq]

/-- Memory lookup returns QTyp equal to ⟨ETyp.int, qt.poison, qt.pred⟩ when lookup succeeds. -/
lemma memEnv_lookup_toQTyp (env : MemoryTypeEnv) (l : Loc) (qt : QTyp) (h : env.lookup l = some qt) :
    qt = ⟨ETyp.int, qt.poison, qt.pred⟩ := by
  unfold MemoryTypeEnv.lookup at h
  generalize env.get? l = opt at h
  cases opt with
  | none => simp only [Option.map] at h; nomatch h
  | some e =>
    simp only [Option.map] at h
    have heq : qt = ⟨ETyp.int, e.poison, e.pred⟩ := (Option.some.inj h).symm
    rw [heq]

/-- When lookup succeeds, get? returns the corresponding MemEntry. -/
lemma memEnv_get_eq_of_lookup (env : MemoryTypeEnv) (l : Loc) (qt : QTyp) (h : env.lookup l = some qt) :
    env.get? l = some ⟨qt.poison, qt.pred⟩ := by
  unfold MemoryTypeEnv.lookup at h
  revert h
  cases env.get? l with
  | none => intro h; simp only [Option.map] at h; nomatch h
  | some e =>
    intro h
    simp only [Option.map] at h
    congr 1
    have heq := Option.some.inj h
    have hp : e.poison = qt.poison := congr_arg QTyp.poison heq
    have hpred : e.pred = qt.pred := congr_arg QTyp.pred heq
    rw [← hp, ← hpred]

/-- Captured variable env from the type context has no duplicate names.
    Should follow from ExtTreeMap key uniqueness; admitted for now. -/
lemma VarTypeEnv_toCaptured_nodup_fst (σ : VarTypeEnv) :
  List.Nodup ((VarTypeEnv.toCaptured σ).map Prod.fst) := by
  unfold VarTypeEnv.toCaptured
  have h : (Std.ExtTreeMap.toList σ).map Prod.fst = σ.keys :=
    Std.ExtTreeMap.map_fst_toList_eq_keys
  rw [h]
  exact Std.ExtTreeMap.nodup_keys

-- ================================================================
-- combineExtTreeMaps helpers
-- ================================================================

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

-- ================================================================
-- Lookup/Update and ExtTreeMap lemmas (type envs and CapturedVarEnv)
-- ================================================================

@[simp] lemma CapturedVarEnv.lookup_eq (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.lookup env x = List.lookup x env := rfl

@[simp] lemma CapturedVarEnv.update_eq (env : CapturedVarEnv) (x : Name) (qt : QTyp) :
  CapturedVarEnv.update env x qt = (x, qt) :: env := rfl

@[simp] lemma CapturedVarEnv.hasKey_iff (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.hasKey env x ↔ List.lookup x env ≠ none := by
  rfl

lemma VarTypeEnv_lookup_update_eq (env : VarTypeEnv) (x : Name) (qt : QTyp) :
  (env.update x qt).lookup x = some qt := by
  simp [VarTypeEnv.update, VarTypeEnv.lookup]

lemma VarTypeEnv_lookup_update_ne (env : VarTypeEnv) (x y : Name) (qt : QTyp) (h_ne : y ≠ x) :
  (env.update x qt).lookup y = env.lookup y := by
  by_cases h_eq : varTypeEnvCmp x y = .eq
  · have h_xy : x = y := LawfulEqCmp.eq_of_compare h_eq
    exact (h_ne h_xy.symm).elim
  · simp [VarTypeEnv.update, VarTypeEnv.lookup, ExtTreeMap.getElem?_insert, h_eq]

-- ================================================================
-- MemoryTypeEnv equiv and joinMemEnv idempotency
-- ================================================================

private lemma joinPoison_idempotent (p : Poison) : joinPoison p p = p := by
  cases p <;> rfl

private lemma joinPredicates_idempotent (pred : Predicate) : joinPredicates pred pred = pred := by
  simp [joinPredicates]
  have h_refl : beqPredicate pred pred = true := by
    have : LawfulBEq Predicate := inferInstance
    have h_eq : (pred == pred) = true := this.rfl
    simp [BEq.beq] at h_eq
    exact h_eq
  simp [h_refl]

private lemma joinMemEnvs_func_some_idempotent :
  ∀ (k : Address) (qt : QTyp),
    (fun _ oq1 oq2 =>
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
        else none
      | none, none => none) k (some qt) (some qt) = some qt := by
  intros k qt
  cases qt with
  | mk t p pred =>
    have h_pred_idem : joinPredicates pred pred = pred := joinPredicates_idempotent pred
    simp [joinPoison_idempotent, h_pred_idem]

private lemma joinMemEnvs_func_none_idempotent :
  ∀ (k : Address),
    (fun (_ : Address) (oq1 oq2 : Option QTyp) =>
      match oq1, oq2 with
      | some qt1, none => some qt1
      | none, some qt2 => some qt2
      | some qt1, some qt2 =>
        let ⟨t1, p1, pred1⟩ := qt1
        let ⟨t2, p2, pred2⟩ := qt2
        if t1 == t2 then
          let p := joinPoison p1 p2
          let pred :=
            match pred1, pred2 with
            | Predicate.guardClosure k1 an1 pb1 ve1, Predicate.guardClosure k2 _ _ _ =>
                if k1 == k2 then Predicate.guardClosure k1 an1 pb1 ve1 else Predicate.noPred
            | Predicate.guardOnly k1, Predicate.guardOnly k2 =>
                if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
            | Predicate.guardClosure k1 _ _ _, Predicate.guardOnly k2 =>
                if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
            | Predicate.guardOnly k1, Predicate.guardClosure k2 _ _ _ =>
                if k1 == k2 then Predicate.guardOnly k1 else Predicate.noPred
            | Predicate.noPred, _ => Predicate.noPred
            | _, Predicate.noPred => Predicate.noPred
          some ⟨t1, p, pred⟩
        else none
      | none, none => none) k none none = none := by
  intro _k
  rfl

private lemma joinMemEnvs_func_self :
  ∀ (k : Address) (oq : Option QTyp),
    (fun _ oq1 oq2 =>
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
        else none
      | none, none => none) k oq oq = oq := by
  intro k oq
  cases oq with
  | none =>
      exact joinMemEnvs_func_none_idempotent k
  | some qt =>
      exact joinMemEnvs_func_some_idempotent k qt

namespace MemoryTypeEnv

theorem equiv.refl (m : MemoryTypeEnv) : m.equiv m := by
  simp only [equiv]
  have : LawfulBEq (List (Loc × MemEntry)) := inferInstance
  exact this.rfl

theorem equiv.trans (m₁ m₂ m₃ : MemoryTypeEnv) : m₁.equiv m₂ → m₂.equiv m₃ → m₁.equiv m₃ := by
  simp only [equiv]
  intro h1 h2
  have : LawfulBEq (List (Loc × MemEntry)) := inferInstance
  have h_list_eq : ExtTreeMap.toList m₁ = ExtTreeMap.toList m₂ := this.eq_of_beq h1
  have h_list_eq2 : ExtTreeMap.toList m₂ = ExtTreeMap.toList m₃ := this.eq_of_beq h2
  have h_list_eq3 : ExtTreeMap.toList m₁ = ExtTreeMap.toList m₃ := by
    rw [h_list_eq, h_list_eq2]
  have h_beq_eq : (ExtTreeMap.toList m₁ == ExtTreeMap.toList m₃) = true := by
    rw [h_list_eq3]
    exact this.rfl
  exact h_beq_eq

end MemoryTypeEnv

theorem joinMemEnv_idempotent : ∀ (m m1 m2 : MemoryTypeEnv),
  m.equiv m1 → m.equiv m2 → m.equiv (joinMemEnvs m1 m2) := by
  intros m m1 m2 h1 h2
  simp only [MemoryTypeEnv.equiv]
  have : LawfulBEq (List (Loc × MemEntry)) := inferInstance
  have h_list_eq1 : ExtTreeMap.toList m = ExtTreeMap.toList m1 := this.eq_of_beq h1
  have h_list_eq2 : ExtTreeMap.toList m = ExtTreeMap.toList m2 := this.eq_of_beq h2
  have h_list_eq12 : ExtTreeMap.toList m1 = ExtTreeMap.toList m2 := by
    rw [← h_list_eq1, h_list_eq2]
  have hm1m2 : m1 = m2 := (ExtTreeMap.toList_inj).1 h_list_eq12
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      let p := joinPoison e1.poison e2.poison
      let pred := joinPredicates e1.pred e2.pred
      some ⟨p, pred⟩
    | none, none => none
  rw [h_list_eq1]
  have h_join_self : joinMemEnvs m1 m1 = m1 := by
    unfold joinMemEnvs
    have hkeys_nodup : m1.keys.Nodup := ExtTreeMap.nodup_keys (t := m1)
    have hkeys_erase : m1.keys.eraseDups = m1.keys :=
      list_eraseDups_eq_self_of_nodup (h := hkeys_nodup)
    have hks : (m1.keys ++ m1.keys).eraseDups = m1.keys := by
      simp [List.eraseDups_append, list_removeAll_self, hkeys_erase]
    apply ExtTreeMap.ext_getElem?
    intro k
    dsimp [combineExtTreeMaps]
    rw [hks]
    by_cases hmem : k ∈ m1.keys
    · have hgo := combineExtTreeMaps_go_get_mem m1 m1 (fun _ oe1 oe2 =>
        match oe1, oe2 with
        | some e1, none => some e1
        | none, some e2 => some e2
        | some e1, some e2 => some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
        | none, none => none) m1.keys ({} : MemoryTypeEnv) k hmem
      have hfun : (fun _ oe1 oe2 => match oe1, oe2 with
        | some e1, none => some e1
        | none, some e2 => some e2
        | some e1, some e2 => some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
        | none, none => none) k (m1[k]?) (m1[k]?) = m1[k]? := by
        cases m1[k]? with
        | none => rfl
        | some e => simp [joinPoison_idempotent, joinPredicates_idempotent]
      rw [ExtTreeMap.get?_eq_getElem?] at hgo
      simp [hfun] at hgo
      convert hgo using 1
      cases m1[k]? <;> rfl
    · have hgo := combineExtTreeMaps_go_get_not_mem m1 m1 (fun _ oe1 oe2 =>
        match oe1, oe2 with
        | some e1, none => some e1
        | none, some e2 => some e2
        | some e1, some e2 => some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
        | none, none => none) m1.keys ({} : MemoryTypeEnv) k hmem
      have hnot_mem : k ∉ m1 := by
        intro hk
        have hk' : k ∈ m1.keys := (ExtTreeMap.mem_keys).2 hk
        exact hmem hk'
      have hm1_none : m1[k]? = none := ExtTreeMap.getElem?_eq_none hnot_mem
      simpa [hm1_none] using hgo
  have h_toList : ExtTreeMap.toList m1 = ExtTreeMap.toList (joinMemEnvs m1 m2) := by
    rw [← hm1m2, h_join_self]
  rw [h_toList]
  exact this.rfl

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

-- ================================================================
-- PExpr / Expr round-trip
-- ================================================================

theorem toExpr_toPExpr? (pe : PExpr) :
  pe.toExpr.toPExpr? = some pe := by
  induction pe with
  | unit | num _ | bool _ | str _ | var _ =>
    simp [PExpr.toExpr, Expr.toPExpr?]
  | vlet x e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH1, IH2]
  | app e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH1, IH2]
  | op e1 o e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH1, IH2]
  | unaryop opname e IH =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH]
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH1, IH2, IH3]
  | deref e IH =>
    simp [PExpr.toExpr, Expr.toPExpr?, IH]

theorem toExpr_toPExpr (pe : PExpr) :
  pe.toExpr.toPExpr = Except.ok pe := by
  simp [Expr.toPExpr, toExpr_toPExpr?, pure, Except.pure]

lemma Expr_toPExpr?_eq_some_of_toPExpr_ok (e : Expr) (pe : PExpr) :
  e.toPExpr = .ok pe →
  Expr.toPExpr? e = some pe := by
  intro h
  unfold Expr.toPExpr at h
  cases hpe : Expr.toPExpr? e with
  | none => simp [hpe] at h
  | some pe' =>
      simp [hpe] at h
      simp [pure, Except.pure] at h
      cases h
      rfl

lemma typecheckExpr_op_succ (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat) :
  typecheckExpr ctx (Expr.op e1 op e2) (fuel + 1) = typecheckOp ctx e1 e2 fuel op := by
  simp [typecheckExpr]

lemma typecheckExpr_unaryop_succ (ctx : TypeContext) (op : UnaryOp) (e : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = typecheckUnaryOp ctx op e fuel := by
  simp [typecheckExpr]

lemma typecheckExpr_seq_succ (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.seq e1 e2) (fuel + 1) = typecheckSeq ctx e1 e2 fuel := by
  simp [typecheckExpr]

lemma typecheckExpr_vlet_succ (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.vlet x e1 e2) (fuel + 1) = typecheckVlet ctx x e1 e2 fuel := by
  simp [typecheckExpr]

lemma typecheckExpr_ite_succ (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.ite e1 e2 e3) (fuel + 1) = typecheckIf ctx e1 e2 e3 fuel := by
  simp [typecheckExpr]

lemma typecheckExpr_app_succ (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) :
  typecheckExpr ctx (Expr.app e1 e2) (fuel + 1) = typecheckApp ctx e1 e2 fuel := by
  simp [typecheckExpr]

-- ================================================================
-- updateMemEnv / list_fold env helpers (generic typechecker helpers)
-- ================================================================

lemma MemoryTypeEnv_lookup_updateMemEnv_ne {Γ : MemoryTypeEnv} {l l' : Loc} {qt : QTyp} :
  l' ≠ l → (updateMemEnv Γ l qt).lookup l' = Γ.lookup l' := by
  intro hne
  have hcmp : compare l l' ≠ Ordering.eq := by
    intro hcmp
    have : l = l' := LawfulEqCmp.eq_of_compare hcmp
    exact hne this.symm
  simp [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.getElem?_insert, hcmp]

lemma updateMemEnv_contains_of_contains (env : MemoryTypeEnv) (l l' : Loc) (qt : QTyp)
  (h : env.contains l' = true) : (updateMemEnv env l qt).contains l' = true := by
  by_cases hEq : l' = l
  · subst hEq
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert]
  · have hCmp : compare l l' ≠ Ordering.eq := by
      intro hce
      have : l = l' := (Nat.compare_eq_eq).1 hce
      exact hEq this.symm
    simp [updateMemEnv, Std.ExtTreeMap.contains_insert, h]

lemma updateMemEnv_contains_eq_or_old (env : MemoryTypeEnv) (l0 l : Loc) (qt : QTyp)
  (h : (updateMemEnv env l0 qt).contains l = true) : l = l0 ∨ env.contains l = true := by
  by_cases hEq : l = l0
  · exact Or.inl hEq
  · have hCmp : compare l0 l ≠ Ordering.eq := by
      intro hce
      have : l0 = l := (Nat.compare_eq_eq).1 hce
      exact hEq this.symm
    have hOld : env.contains l = true := by
      simp [updateMemEnv, Std.ExtTreeMap.contains_insert, hCmp] at h
      exact h
    exact Or.inr hOld

lemma list_fold_updateMemEnv_contains_of_contains (xs : List Loc) (env : MemoryTypeEnv) (l' : Loc) (qt : QTyp)
  (h : env.contains l' = true) :
  (xs.foldl (fun acc l => updateMemEnv acc l qt) env).contains l' = true := by
  induction xs generalizing env with
  | nil => simpa using h
  | cons x xs ih =>
      have h1 : (updateMemEnv env x qt).contains l' = true :=
        updateMemEnv_contains_of_contains env x l' qt h
      exact ih (env := updateMemEnv env x qt) h1

lemma list_fold_updateMemEnv_contains_eq_or_mem (xs : List Loc) (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (h : (xs.foldl (fun acc l0 => updateMemEnv acc l0 qt) env).contains l = true) :
  env.contains l = true ∨ l ∈ xs := by
  induction xs generalizing env with
  | nil => simp at h; exact Or.inl h
  | cons x xs ih =>
      have h' : (xs.foldl (fun acc l0 => updateMemEnv acc l0 qt) (updateMemEnv env x qt)).contains l = true := by
        simpa using h
      have hRec := ih (env := updateMemEnv env x qt) h'
      cases hRec with
      | inl hInUpd =>
          have hstep := updateMemEnv_contains_eq_or_old env x l qt hInUpd
          cases hstep with
          | inl hEq => right; simp [hEq]
          | inr hOld => left; exact hOld
      | inr hMemTail => right; simp [hMemTail]

lemma list_fold_updateMemEnv_lookup_eq_of_not_mem (xs : List Loc) (env : MemoryTypeEnv) (l' : Loc) (qt : QTyp)
  (hnot : l' ∉ xs) :
  (xs.foldl (fun acc l => updateMemEnv acc l qt) env).lookup l' = env.lookup l' := by
  induction xs generalizing env with
  | nil => simp
  | cons x xs ih =>
      simp at hnot
      have hneq : l' ≠ x := by intro hEq; exact hnot.1 hEq
      calc
        (xs.foldl (fun acc l => updateMemEnv acc l qt) (updateMemEnv env x qt)).lookup l' =
            (updateMemEnv env x qt).lookup l' := ih (env := updateMemEnv env x qt) hnot.2
        _ = env.lookup l' := MemoryTypeEnv_lookup_updateMemEnv_ne hneq

lemma list_fold_updateMemEnv_lookup_eq_of_lookup_eq (xs : List Loc) (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (hlookup : env.lookup l = some qt) :
  (xs.foldl (fun acc l0 => updateMemEnv acc l0 qt) env).lookup l = some qt := by
  induction xs generalizing env with
  | nil => simpa using hlookup
  | cons x xs ih =>
      by_cases hEq : l = x
      · subst hEq
        have hself : (updateMemEnv env l qt).lookup l = some qt := by
          simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self, Option.map]
          rw [← memEnv_lookup_toQTyp env l qt hlookup]
        exact ih (env := updateMemEnv env l qt) hself
      · have hneq : l ≠ x := hEq
        have hlookup' : (updateMemEnv env x qt).lookup l = some qt := by
          rw [MemoryTypeEnv_lookup_updateMemEnv_ne hneq]
          exact hlookup
        exact ih (env := updateMemEnv env x qt) hlookup'

lemma list_fold_updateMemEnv_lookup_eq_of_mem (xs : List Loc) (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (hmem : l ∈ xs) (hqt_int : qt.etyp = ETyp.int) :
  (xs.foldl (fun acc l0 => updateMemEnv acc l0 qt) env).lookup l = some qt := by
  induction xs generalizing env with
  | nil => cases hmem
  | cons x xs ih =>
      simp at hmem
      cases hmem with
      | inl hEq =>
          subst hEq
          have hself : (updateMemEnv env l qt).lookup l = some qt := by
            simp only [updateMemEnv, MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self, Option.map]
            congr 1
            cases qt with | mk etyp _ _ => congr 1; exact hqt_int.symm
          exact list_fold_updateMemEnv_lookup_eq_of_lookup_eq xs (updateMemEnv env l qt) l qt hself
      | inr hTail => exact ih (env := updateMemEnv env x qt) hTail

lemma list_fold_joinPoison_first_true (env : MemoryTypeEnv) (xs : List Loc) (pred0 : Predicate) :
  ((xs.foldl
      (fun acc l0 =>
        match env[l0]? with
        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
        | none => acc)
      (true, pred0)).1) = true := by
  induction xs generalizing pred0 with
  | nil => simp
  | cons x xs ih =>
      cases hgetx : env[x]? with
      | none => simpa [List.foldl, hgetx] using ih pred0
      | some qtX => simpa [List.foldl, hgetx, joinPoison] using ih (joinPredicates pred0 qtX.pred)

lemma list_fold_joinPoison_true_of_mem_lookup_true (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) (storedPred : Predicate)
  (l : Loc) (qt : QTyp) (hmem : l ∈ xs) (hlookup : env.lookup l = some qt) (hpoison : qt.poison = true) :
  ((xs.foldl
      (fun acc l0 =>
        match env[l0]? with
        | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
        | none => acc)
      (storedPoison, storedPred)).1) = true := by
  induction xs generalizing storedPoison storedPred l qt with
  | nil => cases hmem
  | cons x xs ih =>
      simp at hmem
      cases hmem with
      | inl hl =>
          subst hl
          have hget := memEnv_get_eq_of_lookup env l qt hlookup
          have h_acc : (match env[l]? with
              | some qt0 => (storedPoison || qt0.poison, joinPredicates storedPred qt0.pred)
              | none => (storedPoison, storedPred)) = (true, joinPredicates storedPred qt.pred) := by
            rw [← ExtTreeMap.get?_eq_getElem?]; rw [hget]; simp [hpoison]
          have htail :
              ((xs.foldl
                  (fun acc l0 =>
                    match env[l0]? with
                    | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                    | none => acc)
                  (true, joinPredicates storedPred qt.pred)).1) = true :=
            list_fold_joinPoison_first_true env xs (joinPredicates storedPred qt.pred)
          simpa [List.foldl, h_acc, joinPoison] using htail
      | inr hmem_tail =>
          cases hgetx : env[x]? with
          | none =>
              simpa [List.foldl, hgetx] using
                ih storedPoison storedPred l qt hmem_tail hlookup hpoison
          | some qtX =>
              simpa [List.foldl, hgetx, joinPoison] using
                ih (joinPoison storedPoison qtX.poison) (joinPredicates storedPred qtX.pred)
                  l qt hmem_tail hlookup hpoison

lemma list_fold_joinPoison_false_implies_lookup_poison_false (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) (storedPred : Predicate)
  (l : Loc) (qt : QTyp) (hmem : l ∈ xs) (hlookup : env.lookup l = some qt)
  (hfold :
    ((xs.foldl
        (fun acc l0 =>
          match env[l0]? with
          | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
          | none => acc)
        (storedPoison, storedPred)).1) = false) :
  qt.poison = false := by
  by_cases hp : qt.poison = true
  · have htrue := list_fold_joinPoison_true_of_mem_lookup_true env xs storedPoison storedPred l qt hmem hlookup hp
    have : false = true := hfold.symm.trans htrue
    cases this
  · cases hq : qt.poison <;> simp [hq] at hp ⊢

-- Extract the guard tag from a qualified type's predicate, if present.
-- (Defined here so joinPredicates_guardTag_eq_some_implies_left_right and list_fold_joinPredicates_guardOnly_implies_init_and_lookup_guardTag can use it.)
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

lemma joinPredicates_guardTag_eq_some_implies_left_right {p q : Predicate} {k : Tag} :
  qtypGuardTag { etyp := ETyp.int, poison := false, pred := joinPredicates p q } = some k →
  qtypGuardTag { etyp := ETyp.int, poison := false, pred := p } = some k ∧
    qtypGuardTag { etyp := ETyp.int, poison := false, pred := q } = some k := by
  intro htag
  cases hbeq : beqPredicate p q with
  | true =>
      have hpq : p = q := eq_of_beq (a := p) (b := q) hbeq
      subst hpq
      simp [joinPredicates, hbeq] at htag
      exact ⟨htag, by simpa using htag⟩
  | false =>
      cases p with
      | noPred => cases q <;> simp [joinPredicates, hbeq, qtypGuardTag] at htag
      | guardOnly k1 =>
          cases q with
          | noPred => simp [joinPredicates, hbeq, qtypGuardTag] at htag
          | guardOnly k2 =>
              cases hkk : (k1 == k2) with
              | false => simp [joinPredicates, hbeq, hkk, qtypGuardTag] at htag
              | true =>
                  have hk12 : k1 = k2 := eq_of_beq (a := k1) (b := k2) hkk
                  have hk1 : k1 = k := by
                    have : some k1 = some k := by simpa [joinPredicates, hbeq, hkk, qtypGuardTag] using htag
                    exact Option.some.inj this
                  subst hk1
                  subst hk12
                  simp [qtypGuardTag]
          | guardClosure k2 _ _ _ =>
              cases hkk : (k1 == k2) with
              | false => simp [joinPredicates, hbeq, hkk, qtypGuardTag] at htag
              | true =>
                  have hk12 : k1 = k2 := eq_of_beq (a := k1) (b := k2) hkk
                  have hk1 : k1 = k := by
                    have : some k1 = some k := by simpa [joinPredicates, hbeq, hkk, qtypGuardTag] using htag
                    exact Option.some.inj this
                  subst hk1
                  subst hk12
                  simp [qtypGuardTag]
      | guardClosure k1 _ _ _ =>
          cases q with
          | noPred => simp [joinPredicates, hbeq, qtypGuardTag] at htag
          | guardOnly k2 =>
              cases hkk : (k1 == k2) with
              | false => simp [joinPredicates, hbeq, hkk, qtypGuardTag] at htag
              | true =>
                  have hk12 : k1 = k2 := eq_of_beq (a := k1) (b := k2) hkk
                  have hk1 : k1 = k := by
                    have : some k1 = some k := by simpa [joinPredicates, hbeq, hkk, qtypGuardTag] using htag
                    exact Option.some.inj this
                  subst hk1
                  subst hk12
                  simp [qtypGuardTag]
          | guardClosure k2 _ _ _ =>
              cases hkk : (k1 == k2) with
              | false => simp [joinPredicates, hbeq, hkk, qtypGuardTag] at htag
              | true =>
                  have hk12 : k1 = k2 := eq_of_beq (a := k1) (b := k2) hkk
                  have hk1 : k1 = k := by
                    have : some k1 = some k := by simpa [joinPredicates, hbeq, hkk, qtypGuardTag] using htag
                    exact Option.some.inj this
                  subst hk1
                  subst hk12
                  simp [qtypGuardTag]

lemma list_fold_joinPredicates_guardOnly_implies_init_and_lookup_guardTag (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) (storedPred : Predicate) {k : Tag}
  (hfold :
    ((xs.foldl
        (fun acc l0 =>
          match env[l0]? with
          | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
          | none => acc)
        (storedPoison, storedPred)).2) = Predicate.guardOnly k) :
  qtypGuardTag { etyp := ETyp.int, poison := false, pred := storedPred } = some k ∧
    ∀ l qt, l ∈ xs → env.lookup l = some qt → qtypGuardTag qt = some k := by
  induction xs generalizing storedPoison storedPred with
  | nil =>
      have hstored : storedPred = Predicate.guardOnly k := by simpa using hfold
      refine ⟨?_, ?_⟩
      · rw [hstored]; simp [qtypGuardTag]
      · intro l qt hmem _hlookup; cases hmem
  | cons x xs ih =>
      simp [List.foldl] at hfold
      cases hget : env[x]? with
      | none =>
          have htail :
              ((xs.foldl
                    (fun acc l0 =>
                      match env[l0]? with
                      | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                      | none => acc)
                    (storedPoison, storedPred)).2) = Predicate.guardOnly k := by
            simpa [hget] using hfold
          have ih' := ih (storedPoison := storedPoison) (storedPred := storedPred) htail
          refine ⟨ih'.1, ?_⟩
          intro l qt hmem hlookup
          simp at hmem
          cases hmem with
          | inl hEq =>
              exfalso
              have hlookup_x : env.lookup x = some qt := by subst hEq; exact hlookup
              have hget_qt := memEnv_get_eq_of_lookup env x qt hlookup_x
              rw [← ExtTreeMap.get?_eq_getElem?] at hget
              rw [hget_qt] at hget
              exact Option.noConfusion hget
          | inr hmem_tail =>
              exact ih'.2 l qt hmem_tail hlookup
      | some qtX =>
          have htail :
              ((xs.foldl
                    (fun acc l0 =>
                      match env[l0]? with
                      | some qt0 => (joinPoison acc.1 qt0.poison, joinPredicates acc.2 qt0.pred)
                      | none => acc)
                    (joinPoison storedPoison qtX.poison, joinPredicates storedPred qtX.pred)).2) =
                Predicate.guardOnly k := by
            simpa [hget] using hfold
          have ih' := ih (storedPoison := joinPoison storedPoison qtX.poison) (storedPred := joinPredicates storedPred qtX.pred) htail
          have hsplit := joinPredicates_guardTag_eq_some_implies_left_right (p := storedPred) (q := qtX.pred) (k := k) ih'.1
          have hx_tag : qtypGuardTag ⟨ETyp.int, qtX.poison, qtX.pred⟩ = some k := by
            simpa [qtypGuardTag] using hsplit.2
          refine ⟨hsplit.1, ?_⟩
          intro l qt hmem hlookup
          simp at hmem
          cases hmem with
          | inl hEq =>
              have hlookup_x : env.lookup x = some qt := by simpa [hEq] using hlookup
              have heq_qtX : qtX = ⟨qt.poison, qt.pred⟩ := by
                have hget_qt := memEnv_get_eq_of_lookup env x qt hlookup_x
                rw [← ExtTreeMap.get?_eq_getElem?] at hget
                rw [hget_qt] at hget
                injection hget with heq
                exact heq.symm
              have heq_qt : qt = ⟨ETyp.int, qtX.poison, qtX.pred⟩ := by
                rw [memEnv_lookup_toQTyp env x qt hlookup_x, heq_qtX]
              rw [heq_qt]
              exact hx_tag
          | inr hmem_tail =>
              exact ih'.2 l qt hmem_tail hlookup

lemma list_fold_max_ge_init (xs : List Loc) (init : Nat) :
  init ≤ List.foldl (fun acc x => max acc (x + 1)) init xs := by
  induction xs generalizing init with
  | nil => rfl
  | cons a as ih =>
      calc
        init ≤ max init (a + 1) := Nat.le_max_left init (a + 1)
        _ ≤ List.foldl (fun acc x => max acc (x + 1)) (max init (a + 1)) as := ih (max init (a + 1))

lemma list_fold_max_succ_ge_of_mem (xs : List Loc) (init l : Nat) (h : l ∈ xs) :
  l + 1 ≤ List.foldl (fun acc x => max acc (x + 1)) init xs := by
  induction xs generalizing init with
  | nil => cases h
  | cons a as ih =>
      simp at h
      cases h with
      | inl hEq =>
          subst hEq
          have hge : max init (l + 1) ≤ List.foldl (fun acc x => max acc (x + 1)) (max init (l + 1)) as :=
            list_fold_max_ge_init as (max init (l + 1))
          have hstart : l + 1 ≤ max init (l + 1) := Nat.le_max_right init (l + 1)
          exact _root_.le_trans hstart hge
      | inr hTail =>
          have htail : l + 1 ≤ List.foldl (fun acc x => max acc (x + 1)) (max init (a + 1)) as :=
            ih (init := max init (a + 1)) hTail
          simpa using htail

-- Helper: updateLocsetWeak containment implies original or membership
lemma updateLocsetWeak_contains_eq_or_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) (l : Loc)
    (h : (updateLocsetWeak env ls storedPoison storedPred).contains l = true) :
    env.contains l = true ∨ l ∈ ls := by
  unfold updateLocsetWeak at h
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  dsimp at h
  unfold LocSet.fold at h
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at h
  have hList := list_fold_updateMemEnv_contains_eq_or_mem ls.toList env l finalQt h
  cases hList with
  | inl hOld =>
      exact Or.inl hOld
  | inr hMem =>
      exact Or.inr (by simpa using hMem)

lemma updateLocsetWeak_contains_of_contains
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) (l : Loc)
    (h : env.contains l = true) :
    (updateLocsetWeak env ls storedPoison storedPred).contains l = true := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  exact list_fold_updateMemEnv_contains_of_contains ls.toList env l finalQt h

-- Helper: assign memEnv formula containment
lemma assign_memEnv_formula_contains_eq_or_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) (l : Loc)
    (h :
      (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 { etyp := ETyp.int, poison := storedPoison, pred := storedPred }
      | _ => updateLocsetWeak env ls storedPoison storedPred).contains l = true) :
    env.contains l = true ∨ l ∈ ls := by
  cases hls : Std.ExtTreeSet.toList ls with
  | nil =>
      simp [hls] at h
      exact updateLocsetWeak_contains_eq_or_mem env ls storedPoison storedPred l h
  | cons x xs =>
      cases xs with
      | nil =>
          simp [hls] at h
          have hstep := updateMemEnv_contains_eq_or_old env x l { etyp := ETyp.int, poison := storedPoison, pred := storedPred } h
          cases hstep with
          | inl hEq =>
              right
              have hxInList : x ∈ ls.toList := by simp [hls]
              have hxIn : x ∈ ls := (Std.ExtTreeSet.mem_toList).1 hxInList
              simpa [hEq] using hxIn
          | inr hOld =>
              exact Or.inl hOld
      | cons y ys =>
          simp [hls] at h
          exact updateLocsetWeak_contains_eq_or_mem env ls storedPoison storedPred l h

lemma assign_memEnv_formula_contains_of_contains
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate) (l : Loc)
    (h : env.contains l = true) :
    (match Std.ExtTreeSet.toList ls with
     | [l0] => updateMemEnv env l0 { etyp := ETyp.int, poison := storedPoison, pred := storedPred }
     | _ => updateLocsetWeak env ls storedPoison storedPred).contains l = true := by
  cases hls : Std.ExtTreeSet.toList ls with
  | nil =>
      simp
      exact updateLocsetWeak_contains_of_contains env ls storedPoison storedPred l h
  | cons x xs =>
      cases xs with
      | nil =>
          simp
          exact
            updateMemEnv_contains_of_contains env x l
              { etyp := ETyp.int, poison := storedPoison, pred := storedPred } h
      | cons y ys =>
          simp
          exact updateLocsetWeak_contains_of_contains env ls storedPoison storedPred l h

lemma updateLocsetWeak_lookup_eq_of_not_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (hnot : l ∉ ls) :
    (updateLocsetWeak env ls storedPoison storedPred).lookup l = env.lookup l := by
  unfold updateLocsetWeak
  set joined :=
    LocSet.fold ls (storedPoison, storedPred) (fun (accP, accPred) l =>
      match env.get? l with
      | some qt => (joinPoison accP qt.poison, joinPredicates accPred qt.pred)
      | none => (accP, accPred))
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩
  dsimp
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  have hnotList : l ∉ ls.toList := by
    intro hmem
    exact hnot ((Std.ExtTreeSet.mem_toList).1 hmem)
  exact
    list_fold_updateMemEnv_lookup_eq_of_not_mem
      ls.toList env l finalQt hnotList

lemma assign_memEnv_formula_lookup_eq_of_not_mem
    (env : MemoryTypeEnv) (ls : LocSet) (storedPoison : Poison) (storedPred : Predicate)
    (l : Loc) (hnot : l ∉ ls) :
    (match Std.ExtTreeSet.toList ls with
      | [l0] => updateMemEnv env l0 { etyp := ETyp.int, poison := storedPoison, pred := storedPred }
      | _ => updateLocsetWeak env ls storedPoison storedPred).lookup l = env.lookup l := by
  cases hls : Std.ExtTreeSet.toList ls with
  | nil =>
      simp
      exact updateLocsetWeak_lookup_eq_of_not_mem env ls storedPoison storedPred l hnot
  | cons x xs =>
      cases xs with
      | nil =>
          have hxInList : x ∈ ls.toList := by simp [hls]
          have hxIn : x ∈ ls := (Std.ExtTreeSet.mem_toList).1 hxInList
          have hneq : l ≠ x := by
            intro hEq
            exact hnot (by simpa [hEq] using hxIn)
          simp [MemoryTypeEnv_lookup_updateMemEnv_ne
            (Γ := env) (l := x) (l' := l)
            (qt := { etyp := ETyp.int, poison := storedPoison, pred := storedPred }) hneq]
      | cons y ys =>
          simp
          exact updateLocsetWeak_lookup_eq_of_not_mem env ls storedPoison storedPred l hnot

-- Helper: locset fold max successor bound from membership
lemma locset_fold_max_succ_ge_of_mem
    (ls : LocSet) (init l : Nat)
    (h : l ∈ ls) :
    l + 1 ≤ LocSet.fold ls init (fun acc x => max acc (x + 1)) := by
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  have hList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 h
  exact list_fold_max_succ_ge_of_mem ls.toList init l hList

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
  | loc {a : Address} {ls : LocSet} {l : Loc}
      (hlookup : θ.lookup l = some a)
      (hin : l ∈ ls) :
      valueHasETyp θ (Value.loc a) (ETyp.ref ls)
  | closure {x e env st1 st2 p tcl} {tenv : CapturedVarEnv}
      (htcl : FnTClosure.regular x e tenv ∈ tcl)
      (henv : ∀ y qt v, tenv.lookup y = some qt →
        env.lookup y = some v → valueHasETyp θ v qt.etyp)
      (hcover : ∀ y qt, tenv.lookup y = some qt → ∃ v, env.lookup y = some v) :
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure {x body env st1 st2 p tcl} {pbody : PExpr} {tenv : CapturedVarEnv}
      (hpure : Expr.toPExpr? body = some pbody)
      (htcl : PFnTClosure.regular x pbody tenv ∈ tcl)
      (henv : ∀ y qt v, tenv.lookup y = some qt →
        env.lookup y = some v → valueHasETyp θ v qt.etyp)
      (hcover : ∀ y qt, tenv.lookup y = some qt → ∃ v, env.lookup y = some v) :
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

/-- Inversion: closure typed at et has et = arrow for some arrow type. -/
lemma valueHasETyp_closure_etyp_arrow_inv
  {θ : RealizationMap} {x : Name} {e : Expr} {env : VarEnv} {et : ETyp}
  (h : valueHasETyp θ (Value.closure x e env) et) :
  ∃ st1 st2 p tcl, et = ETyp.arrow st1 st2 p tcl := by
  cases h with
  | closure => exact ⟨_, _, _, _, rfl⟩

/-- Inversion: closure typed at arrow gives a member of the closure list. -/
lemma valueHasETyp_closure_mem_inv
  {θ : RealizationMap} {x : Name} {e : Expr} {env : VarEnv}
  {st1 st2 : Typ} {p : Poison} {tcl : List FnTClosure}
  (h : valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)) :
  ∃ tenv, FnTClosure.regular x e tenv ∈ tcl := by
  cases h with
  | closure htcl => exact ⟨_, htcl⟩

/-- Inversion: peClosure typed at et has et = parrow for some parrow type. -/
lemma valueHasETyp_peClosure_etyp_parrow_inv


  {θ : RealizationMap} {x : Name} {body : Expr} {env : VarEnv} {et : ETyp}
  (h : valueHasETyp θ (Value.peClosure x body env) et) :
  ∃ st1 st2 p tcl, et = ETyp.parrow st1 st2 p tcl := by
  cases h with
  | peClosure => exact ⟨_, _, _, _, rfl⟩

/-- Inversion: peClosure typed at parrow gives a member of the closure list. -/
lemma valueHasETyp_peClosure_mem_inv
  {θ : RealizationMap} {x : Name} {body : Expr} {env : VarEnv}
  {st1 st2 : Typ} {p : Poison} {tcl : List PFnTClosure}
  (h : valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcl)) :
  ∃ pbody tenv, Expr.toPExpr? body = some pbody ∧ PFnTClosure.regular x pbody tenv ∈ tcl := by
  cases h with
  | peClosure hpure htcl => exact ⟨_, _, hpure, htcl⟩

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
  | closure htcl henv hcover =>
      exact valueHasETyp.closure (htcl := hsub _ htcl) (henv := henv) (hcover := hcover)

/-- Future-use lemma for preservation proofs:
    pure analogue of `valueHasETyp_closure_weaken_tcl` for joined parrow closure sets. -/
lemma valueHasETyp_peClosure_weaken_tcl
    {θ : RealizationMap} {x : Name} {body : Expr} {env : VarEnv}
    {st1 st2 : Typ} {p₁ p₂ : Poison} {tcls₁ tcls₂ : List PFnTClosure}
    (h : valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₁ tcls₁))
    (hsub : ∀ tc, tc ∈ tcls₁ → tc ∈ tcls₂) :
    valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₂ tcls₂) := by
  cases h with
  | peClosure hpure htcl henv hcover =>
      exact valueHasETyp.peClosure (hpure := hpure) (htcl := hsub _ htcl) (henv := henv) (hcover := hcover)

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

-- LocSet.foldM preserves a property P when the fold function preserves P
-- (uses List.foldlM_Except_preserves_property from Properties)
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
  exact List.foldlM_Except_preserves_property s.toList init f P h_init h_preserve result h_fold

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
    typecheckExpr (updateCtxFromResult ctx result1) e2 (fuel - 1) = .ok result2 ∧
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
              cases h_tc2_result : typecheckExpr (updateCtxFromResult ctx result1) e2 fuel' with
              | ok result2 =>
                  have h_tc2_orig := h_tc2_result
                  simp only [updateCtxFromResult] at h_tc2_result
                  rw [h_tc2_result] at h_typecheck
                  simp only [pure, Except.pure] at h_typecheck
                  match h_qt2 : result2.qualType with
                  | QTyp.mk etyp2 p2 pred2 =>
                      rw [h_qt2] at h_typecheck
                      simp at h_typecheck
                      cases h_opEType_result : opEType? op etyp1 etyp2 with
                      | some result_etyp =>
                          simp [h_opEType_result] at h_typecheck
                          have h_opEType_final :
                              opEType? op result1.qualType.etyp result2.qualType.etyp = some result_etyp := by
                            rw [h_qt1, h_qt2]
                            exact h_opEType_result
                          simp only [Nat.add_sub_cancel]
                          rw [← h_typecheck]
                          refine ⟨result1, result2, result_etyp, h_tc1_result, h_tc2_orig, h_opEType_final,
                                  rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
                          simp [h_qt1, h_qt2]
                      | none =>
                          simp [h_opEType_result] at h_typecheck
              | error _msg2 =>
                  have hctx : updateCtxFromResult ctx result1 = { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' } := by simp only [updateCtxFromResult]
                  rw [hctx] at h_tc2_result
                  simp only [h_tc2_result] at h_typecheck
                  exact absurd h_typecheck (fun h => by injection h)
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
    res.qualType.etyp = ETyp.ref (LocSet.singleton l) ∧
    res.qualType.poison = ctx.pc ∧
    res.qualType.pred = Predicate.noPred ∧
    res.memEnv' = updateMemEnv result1.memEnv' l
      ⟨ETyp.int, joinPoison ctx.pc result1.qualType.poison,
        if ctx.pc then Predicate.noPred else result1.qualType.pred⟩ ∧
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
          have h_qualType : res.qualType = ⟨ETyp.ref (LocSet.singleton result1.nextLoc'), ctx.pc, Predicate.noPred⟩ := by
            have := congrArg TypeResult.qualType h_typecheck
            simp at this
            exact this.symm
          have h_memEnv :
              res.memEnv' = updateMemEnv result1.memEnv' result1.nextLoc'
                ⟨ETyp.int, joinPoison ctx.pc poison, if ctx.pc then Predicate.noPred else pred⟩ := by
            have := congrArg TypeResult.memEnv' h_typecheck
            simp at this
            simpa using this.symm
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
          have h_etyp : res.qualType.etyp = ETyp.ref (LocSet.singleton result1.nextLoc') := by
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
          · -- res.qualType.etyp = ETyp.ref (LocSet.singleton l)
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

/-- Structure lemma for `typecheckIf` with known-regime and conservative cases exposed. -/
lemma typecheckIf_structure (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    (-- True case: `matchGuard` succeeds and `R(k) = some true`.
     -- Both branches are typechecked; result uses e2's memEnv/tagEnv/regime.
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .ok (k, deps) ∧
       ctx.regime.lookup? k = some true ∧
       ∃ res1 : TypeResult,
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ (res2 : TypeResult) (res3 : TypeResult),
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                      nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           typecheckExpr ctxFalse e3 (fuel - 1) = .ok res3 ∧
           res.memEnv' = res2.memEnv' ∧
           res.tagEnv' = res2.tagEnv' ∧
           res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
           res.nextTag' = max res2.nextTag' res3.nextTag' ∧
           res.regime' = res2.regime' ∧
           res.qualType.poison = joinPoison ctx.pc res2.qualType.poison ∧
           res.qualType.etyp = res2.qualType.etyp)
    ∨
    (-- False case: `matchGuard` succeeds and `R(k) = some false`.
     -- Both branches are typechecked; result uses e3's memEnv/tagEnv/regime.
     ∃ (k : Tag) (deps : Deps),
       matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .ok (k, deps) ∧
       ctx.regime.lookup? k = some false ∧
       ∃ res1 : TypeResult,
         typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1 ∧
         res1.qualType.etyp = ETyp.bool ∧
         ∃ (res2 : TypeResult) (res3 : TypeResult),
           let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
           typecheckExpr ctxTrue e2 (fuel - 1) = .ok res2 ∧
           let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                      nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           typecheckExpr ctxFalse e3 (fuel - 1) = .ok res3 ∧
           res.memEnv' = res3.memEnv' ∧
           res.tagEnv' = res3.tagEnv' ∧
           res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
           res.nextTag' = max res2.nextTag' res3.nextTag' ∧
           res.regime' = res3.regime' ∧
           res.qualType.poison = joinPoison ctx.pc res3.qualType.poison ∧
           res.qualType.etyp = res3.qualType.etyp)
    ∨
    (-- Standard conservative branch:
     -- either `matchGuard` succeeds but `R(k) = none`, or `matchGuard` fails.
     ((∃ (k : Tag) (deps : Deps),
        matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .ok (k, deps) ∧
        ctx.regime.lookup? k = none)
      ∨
      (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .error err)) ∧
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
          res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv' ∧
          res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv' ∧
          res.nextLoc' = max res2.nextLoc' res3.nextLoc' ∧
          res.nextTag' = max res2.nextTag' res3.nextTag' ∧
          res.regime' = joinRegimes res2.regime' res3.regime' ∧
          res.qualType.poison = joinPoison ctx.pc (joinPoison res1.qualType.poison
                                  (joinPoison res2.qualType.poison res3.qualType.poison)) ∧
          res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                                res2.qualType.poison res3.qualType.poison ∧
          res.qualType.pred = Predicate.noPred) := by
  intro htc
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    simp only [Nat.succ_sub_one]
    unfold typecheckIf at htc
    simp only [bind, Except.bind] at htc
    cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
    | ok kd =>
      obtain ⟨k, deps⟩ := kd
      simp only [hmatch] at htc
      cases hregime : ctx.regime.lookup? k with
      | some b =>
        cases b with
        | true =>
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
                match hq2 : result2.qualType with
                | ⟨etyp2, p2, pred2⟩ =>
                  simp only [hq2] at htc
                  -- Case-split on e3 typechecking (non-dominant branch)
                  let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                              nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
                  cases htc3 : typecheckExpr ctxFalse e3 fuel' with
                  | error e => rw [htc3] at htc; simp at htc
                  | ok result3 =>
                    rw [htc3] at htc; simp at htc
                    match hq3 : result3.qualType with
                    | ⟨etyp3, _p3, _pred3⟩ =>
                    simp only [hq3] at htc
                    split at htc
                    · cases htc
                    · simp only [Except.ok.injEq] at htc
                      subst htc
                      exact ⟨result2, result3, rfl, htc3, rfl, rfl, rfl, rfl, rfl,
                             by simp [hq2], by simp [hq2]⟩
            · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
        | false =>
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
                match hq2 : result2.qualType with
                | ⟨etyp2, _p2, _pred2⟩ =>
                simp only [hq2] at htc
                let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                            nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
                cases htc3 : typecheckExpr ctxFalse e3 fuel' with
                | error e => rw [htc3] at htc; simp at htc
                | ok result3 =>
                  rw [htc3] at htc; simp at htc
                  match hq3 : result3.qualType with
                  | ⟨etyp3, p3, _pred3⟩ =>
                  simp only [hq3] at htc
                  split at htc
                  · cases htc
                  · simp only [Except.ok.injEq] at htc
                    subst htc
                    exact ⟨result2, result3, rfl, htc3, rfl, rfl, rfl, rfl, rfl,
                           by simp [hq3], by simp [hq3]⟩
            · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
      | none =>
        right; right
        refine ⟨Or.inl ⟨k, deps, rfl, hregime⟩, ?_⟩
        simp only [hregime] at htc
        cases htc1pure : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
        | error e => simp only [htc1pure] at htc; cases htc
        | ok guardResult =>
          simp only [htc1pure] at htc
          match hqGuard : guardResult.qualType with
          | ⟨guardEtyp, guardP, guardPred⟩ =>
          simp only [hqGuard] at htc
          by_cases hguardBool : guardEtyp = ETyp.bool
          · simp only [hguardBool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at htc
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
                simp only [hbool, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at htc
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
                      simp only [hcompat', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htc
                      cases htc
                      simp
              · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc
          · simp only [hguardBool, bne_iff_ne, ne_eq] at htc; cases htc
    | error err =>
      right; right
      simp only [hmatch] at htc
      refine ⟨Or.inr ⟨err, rfl⟩, ?_⟩
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
                rw [← htc]
                simp
        · simp only [hbool, bne_iff_ne, ne_eq] at htc; cases htc

/-- In standard mode (when matchGuard fails), typecheckIf produces a result with noPred. -/
lemma typecheckIf_standard_etyp (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .error err) →
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
    have hmatch_err' : matchGuard e1 ctx.memEnv ctx.varEnv fuel' = .error err := by
      simpa [Nat.succ_sub_one] using hmatch_err
    unfold typecheckIf at htc
    simp only [bind, Except.bind, hmatch_err'] at htc
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
    (hmatch_fail : ∃ err, matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .error err)
    (htc1 : typecheckExpr ctx e1 (fuel - 1) = .ok res1)
    (hbool1 : res1.qualType.etyp = ETyp.bool)
    (htc2 : typecheckExpr ({ ctx with pc := joinPoison ctx.pc res1.qualType.poison, memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }) e2 (fuel - 1) = .ok res2)
    (htc3 : typecheckExpr ({ ctx with pc := joinPoison ctx.pc res1.qualType.poison, memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res2.nextLoc', nextTag := res2.nextTag', regime := res1.regime' }) e3 (fuel - 1) = .ok res3) :
    res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
                          res2.qualType.poison res3.qualType.poison := by
  obtain ⟨err, hmatch_err⟩ := hmatch_fail
  cases fuel with
  | zero =>
    simp [typecheckIf] at htc
  | succ fuel' =>
    have hmatch_err' : matchGuard e1 ctx.memEnv ctx.varEnv fuel' = .error err := by
      simpa [Nat.succ_sub_one] using hmatch_err
    unfold typecheckIf at htc
    simp only [bind, Except.bind, hmatch_err'] at htc
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

-- Structure lemma for assign typechecking
-- NOTE: Now requires both reference and RHS to be int type (heap stores only integers)
lemma typecheckAssign_structure (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ls : LocSet),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.ref ls ∧
    typecheckExpr (updateCtxFromResult ctx result1) e2 (fuel - 1) = .ok result2 ∧
    result2.qualType.etyp = ETyp.int ∧
    res.nextLoc' = LocSet.fold ls result2.nextLoc' (fun acc l => max acc (l + 1)) ∧
    res.nextTag' = result2.nextTag' ∧
    res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls ∧
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
              | ref ls =>
                  simp at h_typecheck
                  let ctx' := updateCtxFromResult ctx result1
                  cases h_tc2 : typecheckExpr { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' } e2 fuel' with
                  | ok result2 =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
                      have h_tc2_orig : typecheckExpr (updateCtxFromResult ctx result1) e2 fuel' = .ok result2 := by simp only [updateCtxFromResult]; exact h_tc2
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
                            · -- result1.qualType.etyp = ETyp.ref ls
                              rw [h_qt1]
                            constructor
                            · exact h_tc2_orig
                            constructor
                            · -- result2.qualType.etyp = ETyp.int
                              rw [h_qt2]
                              exact h_etyp2_int
                            constructor
                            · rfl
                            constructor
                            · trivial
                            constructor
                            · trivial
                            constructor
                            · trivial
                            constructor
                            · rw [h_qt1]
                            · trivial
                          · -- Case: etyp2 ≠ ETyp.int (error - contradiction)
                            cases h_typecheck
                  | error _err =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
              | _ =>
                  -- Non-reference type - error case
                  simp at h_typecheck
      | error _err =>
          simp [h_tc1] at h_typecheck

lemma typecheckAssign_memEnv_formula (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult) :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ∃ (result1 result2 : TypeResult) (ls : LocSet),
    typecheckExpr ctx e1 (fuel - 1) = .ok result1 ∧
    result1.qualType.etyp = ETyp.ref ls ∧
    typecheckExpr (updateCtxFromResult ctx result1) e2 (fuel - 1) = .ok result2 ∧
    result2.qualType.etyp = ETyp.int ∧
    (res.memEnv' =
      match Std.ExtTreeSet.toList ls with
      | [l] =>
          updateMemEnv result2.memEnv' l
            { etyp := ETyp.int
              poison := joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison)
              pred := if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred }
      | _ =>
          updateLocsetWeak result2.memEnv' ls
            (joinPoison ctx.pc (joinPoison result1.qualType.poison result2.qualType.poison))
            (if result1.qualType.poison = true ∨ ctx.pc = true then Predicate.noPred else result2.qualType.pred)) ∧
    res.regime' = invalidateRegimeDeps result2.regime' result2.tagEnv' ls := by
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
              | ref ls =>
                  simp at h_typecheck
                  cases h_tc2 :
                    typecheckExpr
                        { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv',
                                   nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
                        e2 fuel' with
                  | ok result2 =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
                      have h_tc2_orig :
                          typecheckExpr (updateCtxFromResult ctx result1) e2 fuel' = .ok result2 := by
                        simpa [updateCtxFromResult] using h_tc2
                      cases h_qt2 : result2.qualType with
                      | mk etyp2 p2 pred2 =>
                          rw [h_qt2] at h_typecheck
                          simp at h_typecheck
                          split at h_typecheck
                          · rename_i h_etyp2_int
                            simp [pure, Except.pure] at h_typecheck
                            cases h_typecheck
                            simp only [Nat.add_sub_cancel]
                            refine ⟨result1, result2, ls, h_tc1, ?_, h_tc2_orig, ?_, ?_, ?_⟩
                            · rw [h_qt1]
                            · rw [h_qt2]
                              exact h_etyp2_int
                            · have hself :
                                  (match Std.ExtTreeSet.toList ls with
                                   | [l] =>
                                       updateMemEnv result2.memEnv' l
                                         { etyp := ETyp.int
                                           poison := joinPoison ctx.pc (joinPoison p1 p2)
                                           pred := if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2 }
                                   | _ =>
                                       updateLocsetWeak result2.memEnv' ls
                                         (joinPoison ctx.pc (joinPoison p1 p2))
                                         (if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2)) =
                                  (match Std.ExtTreeSet.toList ls with
                                   | [l] =>
                                       updateMemEnv result2.memEnv' l
                                         { etyp := ETyp.int
                                           poison := joinPoison ctx.pc (joinPoison p1 p2)
                                           pred := if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2 }
                                   | _ =>
                                       updateLocsetWeak result2.memEnv' ls
                                         (joinPoison ctx.pc (joinPoison p1 p2))
                                         (if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2)) := rfl
                              convert hself using 1
                              simp [h_qt1, h_qt2]
                            · rfl
                          · cases h_typecheck
                  | error _err =>
                      rw [h_tc2] at h_typecheck
                      simp at h_typecheck
              | _ =>
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
                rename_i ls
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
          · -- res.tagEnv' = result1.tagEnv'
            -- Same analysis as memEnv'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · contradiction
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
                rename_i ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · contradiction
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
                rename_i ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · contradiction
                  · split at h_typecheck
                    · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                    · split at h_typecheck
                      · simp [pure, Except.pure] at h_typecheck; cases h_typecheck; rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
                      · split at h_typecheck <;> simp [pure, Except.pure] at h_typecheck <;> cases h_typecheck <;> rfl
          · -- res.regime' = result1.regime'
            cases h_qt : result1.qualType with
            | mk etyp poisonRef predRef =>
                rw [h_qt] at h_typecheck
                simp at h_typecheck
                cases etyp <;> simp at h_typecheck
                rename_i ls
                split at h_typecheck
                · contradiction
                · split at h_typecheck
                  · contradiction
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
        List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel') tcls =
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
        List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel') tcls =
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
                                applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel') tcls with
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
                            applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 fuel') tcls with
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
-- Typechecker monotonicity and preservation lemmas
-- ================================================================

section regime_monotone_proof

private lemma regimeMonotone_refl (R : Regime) :
    Regime.monotoneStep R R := by
  refine ⟨?_, ?_⟩
  · intro k b hk
    exact Or.inl hk
  · intro k hk
    exact hk

lemma regimeMonotone_trans {R R' R'' : Regime}
    (h₁ : Regime.monotoneStep R R')
    (h₂ : Regime.monotoneStep R' R'') :
    Regime.monotoneStep R R'' := by
  refine ⟨?_, ?_⟩
  · intro k b hkR
    have hR' : R'.lookup? k = some b ∨ R'.lookup? k = none := h₁.1 k b hkR
    cases hR' with
    | inl hkR' =>
        exact h₂.1 k b hkR'
    | inr hkR'_none =>
        exact Or.inr (by
          by_contra hkR''_not_none
          exact hkR''_not_none (by
            have hkR'_not_none : R'.lookup? k ≠ none := h₂.2 k hkR''_not_none
            exact False.elim (hkR'_not_none hkR'_none)))
  · intro k hkR''_not_none
    have hkR'_not_none : R'.lookup? k ≠ none := h₂.2 k hkR''_not_none
    exact h₁.2 k hkR'_not_none

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
  have hmap1 : R1.get? k = some b := h1
  have hmap2 : R2.get? k = some b := h2
  have hmap1' : R1[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap1
  have hmap2' : R2[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap2
  have hcombine :
      (combineExtTreeMaps R1 R2
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 == b2 then some b1 else none
          | _, _ => none)).get? k = some b := by
    have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1 R2
      (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 = b2 then some b1 else none
        | _, _ => none) k rfl
    have hcombine0s :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 = b2 then some b1 else none
            | _, _ => none))[k]? = some b := by
      simpa [hmap1', hmap2'] using hcombine0
    have hcombine0' :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none))[k]? = some b := by
      simpa [joinRegimes_combine_fun_eq] using hcombine0s
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
  unfold Regime.lookup?
  simpa [joinRegimes] using hcombine

private lemma joinRegimes_lookup_of_some_disagree
    (R1 R2 : Regime) (k : Tag)
    (h1 : R1.lookup? k = some false)
    (h2 : R2.lookup? k = some true) :
    (joinRegimes R1 R2).lookup? k = none := by
  have hmap1 : R1[k]? = some false := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h1
  have hmap2 : R2[k]? = some true := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h2
  have hcombine := combineExtTreeMaps_getElem?_of_none_none R1 R2
    (fun _ ob1 ob2 => match ob1, ob2 with | some b1, some b2 => if b1 == b2 then some b1 else none | _, _ => none)
    k rfl
  have hcombine' : (joinRegimes R1 R2).get? k = none := by
    unfold joinRegimes
    have h := hcombine
    simp [hmap1, hmap2] at h
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h
  unfold Regime.lookup?
  simp only [joinRegimes]
  exact hcombine'

private lemma joinRegimes_lookup_of_some_disagree_symm
    (R1 R2 : Regime) (k : Tag)
    (h1 : R1.lookup? k = some true)
    (h2 : R2.lookup? k = some false) :
    (joinRegimes R1 R2).lookup? k = none := by
  have hmap1 : R1[k]? = some true := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h1
  have hmap2 : R2[k]? = some false := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h2
  have hcombine := combineExtTreeMaps_getElem?_of_none_none R1 R2
    (fun _ ob1 ob2 => match ob1, ob2 with | some b1, some b2 => if b1 == b2 then some b1 else none | _, _ => none)
    k rfl
  have hcombine' : (joinRegimes R1 R2).get? k = none := by
    unfold joinRegimes
    have h := hcombine
    simp [hmap1, hmap2] at h
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using h
  unfold Regime.lookup?
  simp only [joinRegimes]
  exact hcombine'

private lemma joinRegimes_lookup_of_left_none
    (R1 R2 : Regime) (k : Tag)
    (h1 : R1.lookup? k = none) :
    (joinRegimes R1 R2).lookup? k = none := by
  have hmap1 : R1.get? k = none := h1
  have hmap1' : R1[k]? = none := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap1
  have hcombine :
      (combineExtTreeMaps R1 R2
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 == b2 then some b1 else none
          | _, _ => none)).get? k = none := by
    have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1 R2
      (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 = b2 then some b1 else none
        | _, _ => none) k rfl
    have hcombine0s :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 = b2 then some b1 else none
            | _, _ => none))[k]? = none := by
      simpa [hmap1'] using hcombine0
    have hcombine0' :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none))[k]? = none := by
      simpa [joinRegimes_combine_fun_eq] using hcombine0s
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
  unfold Regime.lookup?
  simpa [joinRegimes] using hcombine

private lemma joinRegimes_lookup_of_right_none
    (R1 R2 : Regime) (k : Tag)
    (h2 : R2.lookup? k = none) :
    (joinRegimes R1 R2).lookup? k = none := by
  have hmap2 : R2.get? k = none := h2
  have hmap2' : R2[k]? = none := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap2
  have hcombine :
      (combineExtTreeMaps R1 R2
        (fun _ ob1 ob2 =>
          match ob1, ob2 with
          | some b1, some b2 => if b1 == b2 then some b1 else none
          | _, _ => none)).get? k = none := by
    have hcombine0 := combineExtTreeMaps_getElem?_of_none_none R1 R2
      (fun _ ob1 ob2 =>
        match ob1, ob2 with
        | some b1, some b2 => if b1 = b2 then some b1 else none
        | _, _ => none) k rfl
    have hcombine0s :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 = b2 then some b1 else none
            | _, _ => none))[k]? = none := by
      simpa [hmap2'] using hcombine0
    have hcombine0' :
        (combineExtTreeMaps R1 R2
          (fun _ ob1 ob2 =>
            match ob1, ob2 with
            | some b1, some b2 => if b1 == b2 then some b1 else none
            | _, _ => none))[k]? = none := by
      simpa [joinRegimes_combine_fun_eq] using hcombine0s
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine0'
  unfold Regime.lookup?
  simpa [joinRegimes] using hcombine

private lemma joinRegimes_lookup_comm (R1 R2 : Regime) (k : Tag) :
    (joinRegimes R1 R2).lookup? k = (joinRegimes R2 R1).lookup? k := by
  by_cases h1 : R1.lookup? k = none
  · rw [joinRegimes_lookup_of_left_none R1 R2 k h1]
    rw [joinRegimes_lookup_of_right_none R2 R1 k]
    exact h1
  · obtain ⟨b1, h1⟩ := Option.ne_none_iff_exists'.1 h1
    by_cases h2 : R2.lookup? k = none
    · rw [joinRegimes_lookup_of_right_none R1 R2 k h2]
      rw [joinRegimes_lookup_of_left_none R2 R1 k]
      exact h2
    · obtain ⟨b2, h2⟩ := Option.ne_none_iff_exists'.1 h2
      by_cases heq : b1 = b2
      · rw [joinRegimes_lookup_of_some_some R1 R2 k b1 h1 (heq ▸ h2)]
        rw [joinRegimes_lookup_of_some_some R2 R1 k b2 h2 (heq.symm ▸ h1)]
        exact congr_arg some heq
      · -- b1 ≠ b2: one true, one false; both joins give none
        cases b1 <;> cases b2 <;> simp at heq
        · -- b1 = false, b2 = true: R1 has false, R2 has true
          rw [joinRegimes_lookup_of_some_disagree R1 R2 k h1 h2,
              joinRegimes_lookup_of_some_disagree_symm R2 R1 k h2 h1]
        · -- b1 = true, b2 = false: R1 has true, R2 has false
          rw [joinRegimes_lookup_of_some_disagree_symm R1 R2 k h1 h2,
              joinRegimes_lookup_of_some_disagree R2 R1 k h2 h1]

lemma joinRegimes_lookup_some_left
    (R1 R2 : Regime) (k : Tag) (b : Bool) :
    (joinRegimes R1 R2).lookup? k = some b →
    R1.lookup? k = some b := by
  intro hjoin
  let f : Tag → Option Bool → Option Bool → Option Bool := fun _ ob1 ob2 =>
    match ob1, ob2 with
    | some b1, some b2 => if b1 = b2 then some b1 else none
    | _, _ => none
  have hcombine : (combineExtTreeMaps R1 R2 f).get? k = some b := by
    unfold Regime.lookup? at hjoin
    simp [joinRegimes] at hjoin
    exact hjoin
  simp only [combineExtTreeMaps] at hcombine
  have hk_mem : k ∈ (R1.keys ++ R2.keys).eraseDups := by
    by_contra hnot
    have hgo_not :=
      combineExtTreeMaps_go_get_not_mem R1 R2 f
        (R1.keys ++ R2.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hnot
    have hempty : (({} : ExtTreeMap Tag Bool)[k]?) = none := by
      rfl
    rw [hempty] at hgo_not
    have hcombine_get : (combineExtTreeMaps.go R1 R2 f (R1.keys ++ R2.keys).eraseDups
        ({} : ExtTreeMap Tag Bool))[k]? = some b := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine
    rw [hgo_not] at hcombine_get
    simp at hcombine_get
  have hgo :=
    combineExtTreeMaps_go_get_mem R1 R2 f
      (R1.keys ++ R2.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hk_mem
  have hcombine_get :
      (combineExtTreeMaps.go R1 R2 f (R1.keys ++ R2.keys).eraseDups
        ({} : ExtTreeMap Tag Bool))[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine
  rw [hcombine_get] at hgo
  simp only [f] at hgo
  cases h1 : R1[k]? <;> cases h2 : R2[k]? <;> simp [h1, h2] at hgo
  rename_i b1 b2
  by_cases hbeq : b1 = b2
  · simp [hbeq] at hgo
    have hb2 : b = b2 := by simpa using hgo
    have hb1 : b = b1 := by
      calc
        b = b2 := hb2
        _ = b1 := hbeq.symm
    have hmap1 : R1.get? k = some b := by
      have hmap1' : R1[k]? = some b := by simpa [hb1] using h1
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap1'
    exact hmap1
  · simp [hbeq] at hgo

lemma joinRegimes_lookup_some_right
    (R1 R2 : Regime) (k : Tag) (b : Bool) :
    (joinRegimes R1 R2).lookup? k = some b →
    R2.lookup? k = some b := by
  intro hjoin
  let f : Tag → Option Bool → Option Bool → Option Bool := fun _ ob1 ob2 =>
    match ob1, ob2 with
    | some b1, some b2 => if b1 = b2 then some b1 else none
    | _, _ => none
  have hcombine : (combineExtTreeMaps R1 R2 f).get? k = some b := by
    unfold Regime.lookup? at hjoin
    simp [joinRegimes] at hjoin
    exact hjoin
  simp only [combineExtTreeMaps] at hcombine
  have hk_mem : k ∈ (R1.keys ++ R2.keys).eraseDups := by
    by_contra hnot
    have hgo_not :=
      combineExtTreeMaps_go_get_not_mem R1 R2 f
        (R1.keys ++ R2.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hnot
    have hempty : (({} : ExtTreeMap Tag Bool)[k]?) = none := by
      rfl
    rw [hempty] at hgo_not
    have hcombine_get :
        (combineExtTreeMaps.go R1 R2 f (R1.keys ++ R2.keys).eraseDups
          ({} : ExtTreeMap Tag Bool))[k]? = some b := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine
    rw [hgo_not] at hcombine_get
    simp at hcombine_get
  have hgo :=
    combineExtTreeMaps_go_get_mem R1 R2 f
      (R1.keys ++ R2.keys).eraseDups ({} : ExtTreeMap Tag Bool) k hk_mem
  have hcombine_get :
      (combineExtTreeMaps.go R1 R2 f (R1.keys ++ R2.keys).eraseDups
        ({} : ExtTreeMap Tag Bool))[k]? = some b := by
    simpa [Std.ExtTreeMap.get?_eq_getElem?] using hcombine
  rw [hcombine_get] at hgo
  simp only [f] at hgo
  cases h1 : R1[k]? <;> cases h2 : R2[k]? <;> simp [h1, h2] at hgo
  rename_i b1 b2
  by_cases hbeq : b1 = b2
  · simp [hbeq] at hgo
    have hb2 : b = b2 := by simpa using hgo
    have hmap2 : R2.get? k = some b := by
      have hmap2' : R2[k]? = some b := by simpa [hb2] using h2
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hmap2'
    exact hmap2
  · simp [hbeq] at hgo

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
  refine ⟨?_, ?_⟩
  · intro k b hkR
    have hk1 := h1.1 k b hkR
    have hk2 := h2.1 k b hkR
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
    exact h1.2 k hk1

lemma invalidateRegimeDeps_monotone
    (R : Regime) (env : TagEnv) (ls : LocSet) :
    Regime.monotoneStep R (invalidateRegimeDeps R env ls) := by
  refine ⟨?_, ?_⟩
  · intro k b hkR
    have hkmap : R[k]? = some b := by
      simpa [Std.ExtTreeMap.get?_eq_getElem?] using hkR
    have hmapFiltered :
        (R.filter (fun k _ =>
          (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k))[k]? =
        Option.filter
          (fun _ =>
            (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k)
          (some b) := by
      rw [Std.ExtTreeMap.getElem?_filter']
      simp [hkmap]
    unfold invalidateRegimeDeps Regime.lookup?
    simp [hmapFiltered]
    exact em (k ∈ ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env)
  · intro k hkInv
    by_contra hkRnone
    have hnone : (invalidateRegimeDeps R env ls).lookup? k = none := by
      have hkmapNone : R[k]? = none := by
        rw [← Std.ExtTreeMap.get?_eq_getElem?]; exact hkRnone
      have hmapFilteredNone :
          (R.filter (fun k _ =>
            (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k))[k]? =
          Option.filter
            (fun _ =>
              (ExtTreeMap.filter (fun x tv => !tv.deps.any (ExtTreeSet.contains ls)) env).contains k)
            (none : Option Bool) := by
        rw [Std.ExtTreeMap.getElem?_filter']
        simp [hkmapNone]
      unfold invalidateRegimeDeps Regime.lookup?
      simp [hmapFilteredNone]
    exact hkInv hnone

lemma joinTypeResults_regime_monotone
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
              joinMemEnvsStrong acc.2.1 result.memEnv',
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

lemma applyFnTClosure_regime_mono
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
    -- Extern case: all return paths set regime' := r1.regime'
    split at happly
    · simp at happly
    · split at happly
      · simp at happly
      · split at happly
        · -- simple case: after resolveSyntaxPred ok, happly has (<$> returnSpecToQTyp) form
          split at happly
          · simp at happly
          · simp only [Functor.map, Except.map] at happly
            split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly
              rw [← happly]; exact regimeMonotone_refl r1.regime'
        · simp only [pure, Except.pure, Except.ok.injEq] at happly
          rw [← happly]; exact regimeMonotone_refl r1.regime'
        · simp only [pure, Except.pure, Except.ok.injEq] at happly
          rw [← happly]; exact regimeMonotone_refl r1.regime'

lemma applyPFnTClosure_regime_mono
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
      simp at happly
      -- Extern case: all return paths set regime' := r1.regime'
      -- split on retSpec: simple / nestedFn / nestedPfn
      split at happly
      · -- simple case: do-block → unfold bind, then split on collectAndAllocExternTags
        simp only [bind, Except.bind] at happly
        split at happly
        · simp at happly
        · split at happly
          · simp at happly
          · simp only [Functor.map, Except.map] at happly
            split at happly
            · simp at happly
            · simp only [Except.ok.injEq] at happly
              rw [← happly]; exact regimeMonotone_refl r1.regime'
      · -- nestedFn case: pure {regime' := r1.regime'}
        simp only [pure, Except.pure, Except.ok.injEq] at happly
        rw [← happly]; exact regimeMonotone_refl r1.regime'
      · -- nestedPfn case: pure {regime' := r1.regime'}
        simp only [pure, Except.pure, Except.ok.injEq] at happly
        rw [← happly]; exact regimeMonotone_refl r1.regime'

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
      set ctx' : TypeContext := { ctx with memEnv := res2.memEnv', tagEnv := res2.tagEnv', nextLoc := res2.nextLoc', nextTag := res2.nextTag', regime := res2.regime' }
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
          have hmono1 : Regime.monotoneStep res2.regime' res1.regime' := by
            have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by simpa [typecheck] using hte1
            exact IH fuel' h_fuel e1 ctx' res1 htce1'
          have hmap_prop :
              ∀ x ∈ (first :: rest), Regime.monotoneStep res1.regime' x.regime' := by
            apply List.mapM_Except_preserves_property
              (f := fun tcl => applyFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx res1 fuel')
              (P := fun x => Regime.monotoneStep res1.regime' x.regime')
            · intro tcl result htcl
              exact applyFnTClosure_regime_mono tcl ctx st1 st2 p p1 etyp2 p2 pred2 res1 result fuel' IH' htcl
            · simpa using hmap
          have hfirst : Regime.monotoneStep res1.regime' first.regime' := by
            exact hmap_prop first (by simp)
          have hrest : ∀ x ∈ rest, Regime.monotoneStep res1.regime' x.regime' := by
            intro x hx
            exact hmap_prop x (by simp [hx])
          have hjoin_mono : Regime.monotoneStep res1.regime' res.regime' :=
            joinTypeResults_regime_monotone ctx first rest res res1.regime' hfirst hrest hjoin
          exact regimeMonotone_trans (regimeMonotone_trans hmono2 hmono1) hjoin_mono
      | inr hparr =>
          rcases hparr with
            ⟨st1, st2, p, p1, tcls, results, first, rest,
              hetyp1, hpoison1, _hnonempty, _hsub, hmap, hresults, hjoin⟩
          subst results
          have hmono1 : Regime.monotoneStep res2.regime' res1.regime' := by
            have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by simpa [typecheck] using hte1
            exact IH fuel' h_fuel e1 ctx' res1 htce1'
          have hmap_prop :
              ∀ x ∈ (first :: rest), Regime.monotoneStep res1.regime' x.regime' := by
            apply List.mapM_Except_preserves_property
              (f := fun tcl => applyPFnTClosure tcl st1 st2 p p1 etyp2 p2 pred2 ctx res1 fuel')
              (P := fun x => Regime.monotoneStep res1.regime' x.regime')
            · intro tcl result htcl
              exact applyPFnTClosure_regime_mono tcl ctx st1 st2 p p1 etyp2 p2 pred2 res1 result fuel' IH' htcl
            · simpa using hmap
          have hfirst : Regime.monotoneStep res1.regime' first.regime' := by
            exact hmap_prop first (by simp)
          have hrest : ∀ x ∈ rest, Regime.monotoneStep res1.regime' x.regime' := by
            intro x hx
            exact hmap_prop x (by simp [hx])
          have hjoin_mono : Regime.monotoneStep res1.regime' res.regime' :=
            joinTypeResults_regime_monotone ctx first rest res res1.regime' hfirst hrest hjoin
          exact regimeMonotone_trans (regimeMonotone_trans hmono2 hmono1) hjoin_mono

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
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e m = .ok res' →
      Regime.monotoneStep ctx'.regime res'.regime') :
    typecheckAssign ctx e1 e2 fuel = .ok res →
    Regime.monotoneStep ctx.regime res.regime' := by
  intro htc
  have hstruct := typecheckAssign_structure ctx e1 e2 fuel res htc
  rcases hstruct with ⟨result1, result2, ls, htc1, _hetyp1, htc2, _hetyp2, _hloc, _hnexttag, hregime, _hqtetyp, _hqtpoison, _hqtpred⟩
  cases fuel with
  | zero =>
      unfold typecheckAssign at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have htc1_simp : typecheckExpr ctx e1 fuel' = .ok result1 := by
        simpa using htc1
      have hm1 := IH fuel' h_fuel e1 ctx result1 htc1_simp
      let ctx' := updateCtxFromResult ctx result1
      have htc2_simp : typecheckExpr ctx' e2 fuel' = .ok result2 := by
        simpa [ctx', updateCtxFromResult] using htc2
      have hm2 := IH fuel' h_fuel e2 ctx' result2 htc2_simp
      have hm2' : Regime.monotoneStep result1.regime' result2.regime' := by
        simpa [ctx', updateCtxFromResult] using hm2
      have hm12 : Regime.monotoneStep ctx.regime result2.regime' :=
        regimeMonotone_trans hm1 hm2'
      have hmInv : Regime.monotoneStep result2.regime' (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
        invalidateRegimeDeps_monotone result2.regime' result2.tagEnv' ls
      have hmFinal : Regime.monotoneStep ctx.regime (invalidateRegimeDeps result2.regime' result2.tagEnv' ls) :=
        regimeMonotone_trans hm12 hmInv
      simpa [hregime] using hmFinal

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
          rcases h1 with ⟨k, deps, _, _, res1, _htc1, _hbool, res2, _res3, htc2, _htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison, _hetyp⟩
          have hm2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
          simpa [hregime] using hm2
      | inr h_rest =>
          cases h_rest with
          | inl h2 =>
              rcases h2 with ⟨k, deps, _, _, res1, _htc1, _hbool, _res2, res3, _htc2, htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison, _hetyp⟩
              let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                         nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
              have htc3' : typecheck ctxFalse e3 fuel' = .ok res3 := by
                simpa [typecheck, ctxFalse] using htc3
              have hm3 := IH fuel' h_fuel e3 ctxFalse res3 htc3'
              simpa [hregime, ctxFalse] using hm3
          | inr hstd =>
              have ⟨_h_std_case, h_res⟩ := hstd
              have ⟨res1, htc1, _hbool, h_res2⟩ := h_res
              have ⟨res2, h_body⟩ := h_res2
              have ⟨htc2, h_res3⟩ := h_body
              have ⟨res3, h_body3⟩ := h_res3
              have ⟨htc3, _hmem, _htag, _hloc, _hnexttag, hregime, _hpoison, _hetyp, _hpred⟩ := h_body3
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
              simp only [typecheckExternVal] at htc
              simp [Bind.bind, Except.bind, pure, Except.pure] at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              cases htc
              exact regimeMonotone_refl ctx.regime
          | externFn arg argTyp retSpec effects =>
              simp only [typecheckExternFn, pure, Except.pure] at htc
              cases htc
              exact regimeMonotone_refl ctx.regime
          | externPfn arg argTyp retSpec =>
              simp only [typecheckExternPfn, pure, Except.pure] at htc
              cases htc
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



-- [Deleted: typecheck_ioFree_preserves_nextTag section]
-- The nextTag-equality statements were false for extern expressions (extern tag
-- allocation via collectAndAllocExternTags advances nextTag). The public interface
-- typecheck_ioFree_preserves_nextTag was unused. The following helpers are retained
-- because they are used by the nextTag monotonicity proofs below.

lemma joinTypeResults_nextTag_eq_max
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
              joinMemEnvsStrong acc.2.1 result.memEnv',
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

-- ================================================================

-- Exact next-tag preservation for `.ioFree` is proved below.

lemma typecheckVar_preserves_nextTag (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.nextTag' = ctx.nextTag := by
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
              rfl
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
                      rfl
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
                              rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              rfl
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
                      rfl
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
                              rfl
                          | false =>
                              simp [pure, Except.pure] at htc
                              cases htc
                              rfl

-- ==========================================================================
-- PFnTClosure.extern structural lemmas
-- All branches of applyPFnTClosure for PFnTClosure.extern set
-- memEnv'/tagEnv'/regime' = result2.memEnv'/tagEnv'/regime'.
-- ==========================================================================

private lemma applyPFnTClosure_extern_field_eq_aux
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (happly : applyPFnTClosure (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.memEnv' = r1.memEnv' ∧ r2.tagEnv' = r1.tagEnv' ∧ r2.regime' = r1.regime' := by
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero => simp at happly
  | succ n =>
      simp only [bind, Except.bind] at happly
      split at happly
      · -- ExternReturn.simple: 3 monadic binds then pure return
        split at happly
        · exact Except.noConfusion happly
        · split at happly
          · exact Except.noConfusion happly
          · split at happly
            · exact Except.noConfusion happly
            · simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl, rfl⟩
      · -- ExternReturn.nestedFn: pure return
        simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl, rfl⟩
      · -- ExternReturn.nestedPfn: pure return
        simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl, rfl⟩

lemma applyPFnTClosure_extern_memEnv_eq
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (happly : applyPFnTClosure (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.memEnv' = r1.memEnv' :=
  (applyPFnTClosure_extern_field_eq_aux ctx st1 st2 p p1 argEtyp argPoison argPred r1 r2
    fuel x retSpec capturedEnv happly).1

lemma applyPFnTClosure_extern_tagEnv_eq
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (happly : applyPFnTClosure (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.tagEnv' = r1.tagEnv' :=
  (applyPFnTClosure_extern_field_eq_aux ctx st1 st2 p p1 argEtyp argPoison argPred r1 r2
    fuel x retSpec capturedEnv happly).2.1

lemma applyPFnTClosure_extern_regime_eq
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
  (happly : applyPFnTClosure (PFnTClosure.extern x retSpec capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.regime' = r1.regime' :=
  (applyPFnTClosure_extern_field_eq_aux ctx st1 st2 p p1 argEtyp argPoison argPred r1 r2
    fuel x retSpec capturedEnv happly).2.2

-- ==========================================================================
-- FnTClosure.extern structural lemmas
-- tagEnv and regime are preserved (all return branches use result2's values).
-- memEnv may differ due to the effects loop.
-- ==========================================================================

private lemma applyFnTClosure_extern_field_eq_aux
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.tagEnv' = r1.tagEnv' ∧ r2.regime' = r1.regime' := by
  unfold applyFnTClosure at happly
  cases fuel with
  | zero => simp at happly
  | succ n =>
      simp only [bind, Except.bind] at happly
      -- collectAndAllocExternTags
      split at happly
      · exact Except.noConfusion happly
      · -- effects loop result
        split at happly
        · exact Except.noConfusion happly
        · -- match retSpec
          split at happly
          · -- ExternReturn.simple: resolveSyntaxPred + returnSpecToQTyp
            split at happly
            · exact Except.noConfusion happly
            · split at happly
              · exact Except.noConfusion happly
              · simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl⟩
          · -- ExternReturn.nestedFn
            simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl⟩
          · -- ExternReturn.nestedPfn
            simp only [pure, Except.pure] at happly; cases happly; exact ⟨rfl, rfl⟩

lemma applyFnTClosure_extern_tagEnv_eq
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.tagEnv' = r1.tagEnv' :=
  (applyFnTClosure_extern_field_eq_aux ctx st1 st2 p p1 argEtyp argPoison argPred r1 r2
    fuel x retSpec effects capturedEnv happly).1

lemma applyFnTClosure_extern_regime_eq
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx r1 fuel = .ok r2) :
  r2.regime' = r1.regime' :=
  (applyFnTClosure_extern_field_eq_aux ctx st1 st2 p p1 argEtyp argPoison argPred r1 r2
    fuel x retSpec effects capturedEnv happly).2

/-- All tags in the tagEnv are strictly below nextTag. This is a typechecker invariant
    that ensures freshly allocated tags (from collectAndAllocExternTags) are absent from
    the tagEnv. -/
def tagEnvBounded (tagEnv : TagEnv) (nextTag : Tag) : Prop :=
  ∀ k, tagEnv.get? k ≠ none → k < nextTag

/-- Context-level version: the tagEnv is bounded by nextTag. -/
abbrev tagEnvBoundedInCtx (ctx : TypeContext) : Prop :=
  tagEnvBounded ctx.tagEnv ctx.nextTag

/-- If all tags in tagEnv are < nextTag and k ≥ nextTag, then k is absent from tagEnv. -/
lemma tagEnvBounded_get_none_of_ge
    (tagEnv : TagEnv) (nextTag : Tag) (k : Tag)
    (hbound : tagEnvBounded tagEnv nextTag)
    (hge : k ≥ nextTag) :
    tagEnv.get? k = none := by
  by_contra h
  have hlt := hbound k h
  exact absurd hge (Nat.not_le.mpr hlt)

/-- Helper: the tag-allocating forIn loop in collectAndAllocExternTags never decreases the tag counter. -/
private lemma forIn_tag_incr_ge
    (L : List (TagIndex × Name × Expr))
    (init_map : ExtTreeMap TagIndex Tag compare) (init_tag : Tag)
    (r : MProd (ExtTreeMap TagIndex Tag compare) Tag)
    (h : (forIn L ⟨init_map, init_tag⟩
      (fun (x : TagIndex × Name × Expr) (r : MProd (ExtTreeMap TagIndex Tag compare) Tag) =>
        (Except.ok (ForInStep.yield ⟨r.fst.insert x.1 r.snd, r.snd + 1⟩) : Except String _))
      = Except.ok r)) :
    init_tag ≤ r.snd := by
  induction L generalizing init_map init_tag with
  | nil =>
    simp only [forIn, List.forIn'_nil, pure, Except.pure, Except.ok.injEq] at h
    cases h; exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [forIn, List.forIn'_cons, bind, Except.bind] at h
    exact Nat.le_trans (Nat.le_succ _) (ih _ _ h)

/-- collectAndAllocExternTags never decreases nextTag: the returned nextTag' ≥ input nextTag. -/
lemma collectAndAllocExternTags_nextTag_ge (preds : List SyntaxPredicate) (t : Tag)
    (map : ExtTreeMap TagIndex Tag) (t' : Tag) :
    collectAndAllocExternTags preds t = .ok (map, t') → t ≤ t' := by
  intro h
  unfold collectAndAllocExternTags at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  revert h
  split
  · intro h; exact absurd h Except.noConfusion
  · rename_i v _
    split
    · intro h; exact absurd h Except.noConfusion
    · split
      · intro h; exact absurd h Except.noConfusion
      · rename_i result hpass3
        intro h
        have heq := Except.ok.inj h
        have htagEq := (Prod.mk.inj heq).2
        rw [← htagEq]
        exact forIn_tag_incr_ge v.snd ∅ t result hpass3

/-- Helper: all values in the mapping produced by the forIn loop in
    collectAndAllocExternTags are ≥ the base tag. -/
private lemma forIn_tag_mapping_values_ge
    (L : List (TagIndex × Name × Expr))
    (init_map : ExtTreeMap TagIndex Tag compare) (init_tag base_tag : Tag)
    (r : MProd (ExtTreeMap TagIndex Tag compare) Tag)
    (hbase : base_tag ≤ init_tag)
    (hinit : ∀ (idx : TagIndex) (tag : Tag), init_map.get? idx = some tag → base_tag ≤ tag)
    (h : (forIn L ⟨init_map, init_tag⟩
      (fun (x : TagIndex × Name × Expr) (r : MProd (ExtTreeMap TagIndex Tag compare) Tag) =>
        (Except.ok (ForInStep.yield ⟨r.fst.insert x.1 r.snd, r.snd + 1⟩) : Except String _))
      = Except.ok r)) :
    ∀ (idx : TagIndex) (tag : Tag), r.fst.get? idx = some tag → base_tag ≤ tag := by
  induction L generalizing init_map init_tag with
  | nil =>
    simp only [forIn, List.forIn'_nil, pure, Except.pure, Except.ok.injEq] at h
    cases h; exact hinit
  | cons hd tl ih =>
    simp only [forIn, List.forIn'_cons, bind, Except.bind] at h
    apply ih (init_map.insert hd.1 init_tag) (init_tag + 1) (Nat.le_trans hbase (Nat.le_succ _)) _ h
    intro idx tag hget
    rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert] at hget
    split at hget
    · exact (Option.some.inj hget).symm ▸ hbase
    · rw [← ExtTreeMap.get?_eq_getElem?] at hget; exact hinit idx tag hget

/-- All concrete tags in the mapping produced by collectAndAllocExternTags are ≥ the input nextTag. -/
lemma collectAndAllocExternTags_mapping_values_ge (preds : List SyntaxPredicate) (t : Tag)
    (map : ExtTreeMap TagIndex Tag) (t' : Tag)
    (htc : collectAndAllocExternTags preds t = .ok (map, t'))
    (idx : TagIndex) (tag : Tag)
    (hget : map.get? idx = some tag) :
    t ≤ tag := by
  unfold collectAndAllocExternTags at htc
  simp only [bind, Except.bind, pure, Except.pure] at htc
  revert htc
  split
  · intro h; exact absurd h Except.noConfusion
  · rename_i v _
    split
    · intro h; exact absurd h Except.noConfusion
    · split
      · intro h; exact absurd h Except.noConfusion
      · rename_i result hpass3
        intro htc
        have heq := Except.ok.inj htc
        have hmapEq := (Prod.mk.inj heq).1
        rw [← hmapEq] at hget
        refine forIn_tag_mapping_values_ge v.snd ∅ t t result (Nat.le_refl _) ?_ hpass3 idx tag hget
        intro idx' tag' hget'
        simp [ExtTreeMap.get?_eq_getElem?] at hget'

section typecheck_nextTag_normal_mono_proof

lemma typecheckExternVal_nextTag_mono
    (ctx : TypeContext) (typ : Typ)
    (poison : Bool) (pred : SyntaxPredicate) (res : TypeResult) :
    typecheckExternVal ctx typ poison pred = .ok res →
    ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckExternVal at htc
  split at htc
  · simp at htc
  · simp at htc
  · simp only [bind, Except.bind, pure, Except.pure] at htc
    cases halloc : collectAndAllocExternTags [pred] ctx.nextTag with
    | error err => simp [halloc] at htc
    | ok result =>
      rcases result with ⟨tagMapping, nextTag'⟩
      simp only [halloc] at htc
      cases hresolve : resolveSyntaxPred pred ctx.varEnv tagMapping with
      | error err => simp [hresolve] at htc
      | ok resolvedPred =>
        simp only [hresolve] at htc
        cases hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx with
        | error err => simp [hsurf] at htc
        | ok surfResult =>
          simp only [hsurf, Except.ok.injEq] at htc; cases htc
          exact collectAndAllocExternTags_nextTag_ge [pred] ctx.nextTag tagMapping nextTag' halloc

lemma typecheckExternFn_preserves_nextTag
    (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) (res : TypeResult) :
    typecheckExternFn ctx arg argTyp retSpec effects = .ok res →
    res.nextTag' = ctx.nextTag := by
  intro htc
  unfold typecheckExternFn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

lemma typecheckExternPfn_preserves_nextTag
    (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (res : TypeResult) :
    typecheckExternPfn ctx arg argTyp retSpec = .ok res →
    res.nextTag' = ctx.nextTag := by
  intro htc
  unfold typecheckExternPfn at htc
  simp [pure, Except.pure] at htc
  cases htc
  rfl

private lemma generateFreshTagRes_nextTag_succ (r : TypeResult) :
    (generateFreshTagRes r).2.nextTag' = r.nextTag' + 1 := by
  simp [generateFreshTagRes]

private lemma applyFnTClosure_nextTag_mono_normal
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
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          rcases htc : typecheckExpr _ _ _ with _ | ⟨r⟩
            <;> rw [htc] at happly
            <;> simp at happly
          rcases hqt : r.qualType with ⟨etyp, poison, pred⟩
          simp [hqt] at happly
          cases hsub : isSubtype st2 _ with
          | false =>
              rw [hsub] at happly
              simp at happly
          | true =>
              rw [hsub] at happly
              simp [pure, Except.pure] at happly
              subst r2
              set ctx' : TypeContext := {
                pc := joinPoison p (joinPoison p1 ctx.pc),
                regime := r1.regime',
                memEnv := r1.memEnv',
                varEnv := (VarTypeEnv.ofCaptured env).update x
                    { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred },
                tagEnv := r1.tagEnv',
                nextLoc := r1.nextLoc',
                nextTag := r1.nextTag',
                pureCtx := ctx.pureCtx } with hctx'
              have htc' : typecheck ctx' body fuel' = .ok r := by
                simpa [typecheck, hctx'] using htc
              have hmono := IH fuel' (Nat.lt_succ_self fuel') body ctx' r htc'
              simpa [hctx'] using hmono
      | extern x retSpec effects capturedEnv =>
          simp [bind, Except.bind, pure, Except.pure] at happly
          -- Extern case: r2.nextTag' = v.2 from collectAndAllocExternTags, and v.2 ≥ r1.nextTag'
          split at happly
          · simp at happly
          · rename_i heq'
            have htag := collectAndAllocExternTags_nextTag_ge _ _ _ _ heq'
            split at happly
            · simp at happly
            · split at happly
              · split at happly
                · simp at happly
                · split at happly
                  · simp at happly
                  · simp only [Except.ok.injEq] at happly; rw [← happly]; exact htag
              · simp only [Except.ok.injEq] at happly; rw [← happly]; exact htag
              · simp only [Except.ok.injEq] at happly; rw [← happly]; exact htag

private lemma applyPFnTClosure_nextTag_mono_normal
  (tcl : PFnTClosure) (ctx : TypeContext)
  (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (r1 r2 : TypeResult) (fuel : Nat)
  (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' → ctx'.nextTag ≤ res'.nextTag') :
  applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 fuel = .ok r2 →
  r1.nextTag' ≤ r2.nextTag' := by
  intro happly
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body env =>
          simp [bind, Except.bind] at happly
          rcases htc : typecheckExpr _ _ _ with _ | ⟨r⟩
            <;> rw [htc] at happly
            <;> simp at happly
          rcases hqt : r.qualType with ⟨etyp, poison, pred⟩
          simp [hqt] at happly
          cases hsub : isSubtype st2 _ with
          | false =>
              rw [hsub] at happly
              simp at happly
          | true =>
              rw [hsub] at happly
              simp [pure, Except.pure] at happly
              subst r2
              set ctx' : TypeContext := {
                pc := joinPoison p (joinPoison ctx.pc p1),
                regime := r1.regime',
                memEnv := r1.memEnv',
                varEnv := (VarTypeEnv.ofCaptured env).update x
                    { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred },
                tagEnv := r1.tagEnv',
                nextLoc := r1.nextLoc',
                nextTag := r1.nextTag',
                pureCtx := true } with hctx'
              have htc' : typecheck ctx' body.toExpr fuel' = .ok r := by
                simpa [typecheck, hctx'] using htc
              have hmono := IH fuel' (Nat.lt_succ_self fuel') body.toExpr ctx' r htc'
              simpa [hctx'] using hmono
      | extern x retSpec capturedEnv =>
          simp [bind, Except.bind] at happly
          -- Extern case: simple uses collectAndAllocExternTags (≥ r1.nextTag');
          -- nestedFn/nestedPfn use r1.nextTag' directly (le_refl)
          split at happly
          · -- simple case: allocates tags
            split at happly
            · simp at happly
            · rename_i heq'
              have htag := collectAndAllocExternTags_nextTag_ge _ _ _ _ heq'
              split at happly
              · simp at happly
              · split at happly
                · simp at happly
                · simp only [pure, Except.pure, Except.ok.injEq] at happly
                  rw [← happly]; exact htag
          · simp only [pure, Except.pure, Except.ok.injEq] at happly; rw [← happly]
          · simp only [pure, Except.pure, Except.ok.injEq] at happly; rw [← happly]

private lemma foldl_max_ge_init (a : Nat) (xs : List Nat) :
    a ≤ List.foldl max a xs := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      calc
        a ≤ max a x := Nat.le_max_left a x
        _ ≤ List.foldl max (max a x) xs := ih (max a x)

private lemma typecheckApp_nextTag_mono_normal (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
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
  · rcases hctxPure : ctx.pureCtx <;> simp [hctxPure] at htc
    rcases fs with _ | ⟨f, fs'⟩ <;> simp at htc
    rcases hsub1 : isSubtype t1 _
      <;> rw [hsub1] at htc
      <;> simp at htc
    simp [bind, Except.bind] at htc
    rcases happly : applyFnTClosure f t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons :
        List.cons r <$>
          List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
        with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap :
        List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
        with _ | ⟨rs''⟩
      <;> rw [hmap] at hcons
      <;> simp at hcons
    rcases hcons with ⟨_, heq2⟩
    subst r1
    subst rs''
    have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
    have hcte2' : typecheck ctx e2 fuel' = .ok res2 := by
      simpa [typecheck] using hcte2
    have h2 := IH fuel' h_fuel e2 ctx res2 hcte2'
    have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by
      simpa [typecheck] using htce1
    have h1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have h_res2_le_res1 : res2.nextTag' ≤ res1.nextTag' := by
      simpa [hctx'] using h1
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextTag ≤ res'.nextTag' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r_mono : res1.nextTag' ≤ r.nextTag' := by
      exact applyFnTClosure_nextTag_mono_normal f ctx t1 t2 p poison1 etyp2 poison2 pred2 res1 r fuel' IH' happly
    have h_join :
        res.nextTag' =
          List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      joinTypeResults_nextTag_eq_max ctx r rs' res htc
    have h_ctx_le_r : ctx.nextTag ≤ r.nextTag' := by
      exact Nat.le_trans h2 (Nat.le_trans h_res2_le_res1 h_r_mono)
    have h_r_le_max :
        r.nextTag' ≤ List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) := by
      simpa [List.max] using foldl_max_ge_init r.nextTag' (rs'.map TypeResult.nextTag')
    have h_ctx_le_max :
        ctx.nextTag ≤ List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      Nat.le_trans h_ctx_le_r h_r_le_max
    simpa [h_join] using h_ctx_le_max
  · rename_i st1 st2 p tcls
    rcases tcls with _ | ⟨f, fs'⟩ <;> simp at htc
    rcases hsub1 : isSubtype st1 _
      <;> rw [hsub1] at htc
      <;> simp at htc
    simp [bind, Except.bind] at htc
    rcases happly : applyPFnTClosure f st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons :
        List.cons r <$>
          List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
        with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap :
        List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
        with _ | ⟨rs''⟩
      <;> rw [hmap] at hcons
      <;> simp at hcons
    rcases hcons with ⟨_, heq2⟩
    subst r1
    subst rs''
    have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
    have hcte2' : typecheck ctx e2 fuel' = .ok res2 := by
      simpa [typecheck] using hcte2
    have h2 := IH fuel' h_fuel e2 ctx res2 hcte2'
    have htce1' : typecheck ctx' e1 fuel' = .ok res1 := by
      simpa [typecheck] using htce1
    have h1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have h_res2_le_res1 : res2.nextTag' ≤ res1.nextTag' := by
      simpa [hctx'] using h1
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextTag ≤ res'.nextTag' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r_mono : res1.nextTag' ≤ r.nextTag' := by
      exact applyPFnTClosure_nextTag_mono_normal f ctx st1 st2 p poison1 etyp2 poison2 pred2 res1 r fuel' IH' happly
    have h_join :
        res.nextTag' =
          List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      joinTypeResults_nextTag_eq_max ctx r rs' res htc
    have h_ctx_le_r : ctx.nextTag ≤ r.nextTag' := by
      exact Nat.le_trans h2 (Nat.le_trans h_res2_le_res1 h_r_mono)
    have h_r_le_max :
        r.nextTag' ≤ List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) := by
      simpa [List.max] using foldl_max_ge_init r.nextTag' (rs'.map TypeResult.nextTag')
    have h_ctx_le_max :
        ctx.nextTag ≤ List.max (r.nextTag' :: rs'.map TypeResult.nextTag') (by intro h; cases h) :=
      Nat.le_trans h_ctx_le_r h_r_le_max
    simpa [h_join] using h_ctx_le_max

private lemma typecheckUnaryOp_nextTag_mono_normal (ctx : TypeContext) (op : UnaryOp) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckUnaryOp ctx op e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckUnaryOp at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte : typecheckExpr ctx e fuel' with
      | error err =>
          simp [hte] at htc
      | ok r1 =>
          simp [hte] at htc
          rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          cases hop : opUnaryEType? op etyp1 with
          | none =>
              simp [hop] at htc
          | some outType =>
              simp [hop, pure, Except.pure] at htc
              cases htc
              have hte' : typecheck ctx e fuel' = .ok r1 := by
                simpa [typecheck] using hte
              exact IH fuel' (Nat.lt_succ_self fuel') e ctx r1 hte'

private lemma typecheckOp_nextTag_mono_normal (ctx : TypeContext) (e1 e2 : Expr)
    (fuel : Nat) (op : Op) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckOp ctx e1 e2 fuel op = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckOp at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte1 : typecheckExpr ctx e1 fuel' with
      | error err =>
          simp [hte1] at htc
      | ok r1 =>
          simp [hte1] at htc
          rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          let ctx' : TypeContext := updateCtxFromResult ctx r1
          cases hte2 : typecheckExpr ctx' e2 fuel' with
          | error err =>
              erw [hte2] at htc
              simp at htc
          | ok r2 =>
              erw [hte2] at htc
              simp at htc
              rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
              simp [hq2] at htc
              cases hop : opEType? op etyp1 etyp2 with
              | none =>
                  simp [hop] at htc
              | some outType =>
                  simp [hop, pure, Except.pure] at htc
                  cases htc
                  have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                    simpa [typecheck] using hte1
                  have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                  have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                    simpa [typecheck, ctx'] using hte2
                  have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                  exact Nat.le_trans h1 (by simpa [ctx'] using h2)

private lemma typecheckSeq_nextTag_mono_normal (ctx : TypeContext) (e1 e2 : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckSeq ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckSeq at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte1 : typecheckExpr ctx e1 fuel' with
      | error err =>
          simp [hte1] at htc
      | ok r1 =>
          simp [hte1] at htc
          let ctx' := updateCtxFromResult ctx r1
          cases hte2 : typecheckExpr ctx' e2 fuel' with
          | error err =>
              simp [hte2, ctx'] at htc
          | ok r2 =>
              simp [hte2, ctx'] at htc
              have hres : r2 = res := by
                simpa [pure, Except.pure] using htc
              have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                simpa [typecheck] using hte1
              have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
              have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                simpa [typecheck, ctx'] using hte2
              have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
              have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', updateCtxFromResult] using h2)
              simpa [hres] using hctx

private lemma typecheckNewRef_nextTag_mono_normal (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckNewRef ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckNewRef at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte : typecheckExpr ctx e fuel' with
      | error err =>
          simp [hte] at htc
      | ok r1 =>
          simp [hte] at htc
          rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          by_cases hInt : etyp1 = ETyp.int
          · simp [hInt, freshTLocRes, pure, Except.pure] at htc
            cases htc
            have hte' : typecheck ctx e fuel' = .ok r1 := by
              simpa [typecheck] using hte
            exact IH fuel' (Nat.lt_succ_self fuel') e ctx r1 hte'
          · exfalso
            simp [hInt] at htc

private lemma typecheckAssign_nextTag_mono_normal (ctx : TypeContext) (e1 e2 : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckAssign ctx e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckAssign at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte1 : typecheckExpr ctx e1 fuel' with
      | error err =>
          simp [hte1] at htc
      | ok r1 =>
          simp [hte1] at htc
          rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
          simp [hq1] at htc
          cases etyp1 with
          | int =>
              simp at htc
          | bool =>
              simp at htc
          | unit =>
              simp at htc
          | string =>
              simp at htc
          | arrow st1 st2 p tcls =>
              simp at htc
          | parrow st1 st2 p tcls =>
              simp at htc
          | ref ls =>
              simp at htc
              let ctx' : TypeContext := updateCtxFromResult ctx r1
              cases hte2 : typecheckExpr ctx' e2 fuel' with
              | error err2 =>
                  erw [hte2] at htc
                  simp at htc
              | ok r2 =>
                  erw [hte2] at htc
                  simp at htc
                  rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                  simp [hq2] at htc
                  by_cases hInt2 : etyp2 = ETyp.int
                  · simp [hInt2, pure, Except.pure] at htc
                    have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                      simpa [typecheck] using hte1
                    have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                    have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                      simpa [typecheck, ctx'] using hte2
                    have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                    have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', updateCtxFromResult] using h2)
                    have hresnext : r2.nextTag' = res.nextTag' := by
                      simpa using congrArg TypeResult.nextTag' htc
                    simpa [hresnext] using hctx
                  · exfalso
                    simp [hInt2] at htc

private lemma typecheckDeref_nextTag_mono_normal (ctx : TypeContext) (e : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckDeref ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckDeref at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hte : typecheckExpr ctx e fuel' with
      | error err =>
          simp [hte] at htc
      | ok r1 =>
          simp [hte] at htc
          rcases hq1 : r1.qualType with ⟨etyp1, pRef, predRef⟩
          simp [hq1] at htc
          cases etyp1 with
          | int =>
              simp at htc
          | bool =>
              simp at htc
          | unit =>
              simp at htc
          | string =>
              simp at htc
          | arrow st1 st2 p tcls =>
              simp at htc
          | parrow st1 st2 p tcls =>
              simp at htc
          | ref ls =>
              simp at htc
              by_cases hls : ls = ∅
              · simp [hls] at htc
              · simp [hls] at htc
                let foldStep : (Poison × Option Predicate) → Loc → Except String (Poison × Option Predicate) :=
                  fun x l =>
                    match r1.memEnv'.lookup l with
                    | some qt =>
                        pure (joinPoison x.1 qt.poison,
                          match x.2 with
                          | none => some qt.pred
                          | some p => some (joinPredicates p qt.pred))
                    | none => throw s!"Location {l} not found in memory environment"
                let foldExpr : Except String (Poison × Option Predicate) := ls.foldM (false, (none : Option Predicate)) foldStep
                cases hfold : foldExpr with
                  | error err =>
                      have hfold' := hfold
                      simp [foldExpr, foldStep] at hfold'
                      erw [hfold'] at htc
                      simp at htc
                      cases htc
                  | ok folded =>
                      rcases folded with ⟨joinedCellPoison, mergedPredOpt⟩
                      have hfold' := hfold
                      simp [foldExpr, foldStep] at hfold'
                      erw [hfold'] at htc
                      simp at htc
                      have hte' : typecheck ctx e fuel' = .ok r1 := by simpa [typecheck] using hte
                      have hmono := IH fuel' (Nat.lt_succ_self fuel') e ctx r1 hte'
                      cases hpRef : pRef with
                      | true =>
                          simp [hpRef, pure, Except.pure] at htc
                          cases htc
                          exact hmono
                      | false =>
                          simp [hpRef] at htc
                          cases hmerged : mergedPredOpt.getD Predicate.noPred with
                          | noPred =>
                              simp [hmerged, pure, Except.pure] at htc
                              cases htc
                              exact hmono
                          | guardOnly k =>
                              simp [hmerged] at htc
                              cases htag : r1.tagEnv'[k]? with
                              | none =>
                                  simp [htag, pure, Except.pure] at htc
                                  cases htc
                                  exact hmono
                              | some tv =>
                                  rcases tv with ⟨b, deps⟩
                                  cases b <;> simp [htag, pure, Except.pure] at htc <;> cases htc <;> exact hmono
                          | guardClosure k arg body env =>
                              simp [hmerged] at htc
                              cases htag : r1.tagEnv'[k]? with
                              | none =>
                                  simp [htag, pure, Except.pure] at htc
                                  cases htc
                                  exact hmono
                              | some tv =>
                                  rcases tv with ⟨b, deps⟩
                                  cases b <;> simp [htag, pure, Except.pure] at htc <;> cases htc <;> exact hmono

private lemma typecheckVlet_nextTag_mono_normal (ctx : TypeContext) (x : Name) (e1 e2 : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckVlet ctx x e1 e2 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckVlet at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hlookup : ctx.varEnv.lookup x with
      | none =>
          simp [hlookup] at htc
          try
            cases hte1 : typecheckExpr ctx e1 fuel' with
            | error err =>
                simp [hte1] at htc
                cases htc
            | ok r1 =>
                simp [hte1] at htc
                let varEnv' := ctx.varEnv.update x r1.qualType
                let ctxBase : TypeContext := updateCtxFromResult ctx r1
                let ctx' : TypeContext := { ctxBase with varEnv := varEnv' }
                cases hte2 : typecheckExpr ctx' e2 fuel' with
                | error err =>
                    erw [hte2] at htc
                    simp at htc
                    cases htc
                | ok r2 =>
                    erw [hte2] at htc
                    simp at htc
                    rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                    simp [hq2, pure, Except.pure] at htc
                    have hresnext : r2.nextTag' = res.nextTag' := by
                      simpa using congrArg TypeResult.nextTag' htc
                    have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                      simpa [typecheck] using hte1
                    have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                    have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                      simpa [typecheck, ctx', ctxBase, varEnv', updateCtxFromResult] using hte2
                    have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                    have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', ctxBase, varEnv', updateCtxFromResult] using h2)
                    simpa [hresnext] using hctx
      | some qtOuter =>
          simp [hlookup] at htc
          cases hpred : qtOuter.pred with
          | guardClosure k arg body env =>
              simp [hpred] at htc
              by_cases hregSome : (ctx.regime.lookup? k).isSome = true
              · simp [hregSome] at htc
              · simp [hregSome] at htc
                cases hte1 : typecheckExpr ctx e1 fuel' with
                | error err =>
                    simp [hte1] at htc
                    cases htc
                | ok r1 =>
                    simp [hte1] at htc
                    let varEnv' := ctx.varEnv.update x r1.qualType
                    let ctxBase : TypeContext := updateCtxFromResult ctx r1
                    let ctx' : TypeContext := { ctxBase with varEnv := varEnv' }
                    cases hte2 : typecheckExpr ctx' e2 fuel' with
                    | error err =>
                        erw [hte2] at htc
                        simp at htc
                        cases htc
                    | ok r2 =>
                        erw [hte2] at htc
                        simp at htc
                        rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                        simp [hq2, pure, Except.pure] at htc
                        have hresnext : r2.nextTag' = res.nextTag' := by
                          simpa using congrArg TypeResult.nextTag' htc
                        have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                          simpa [typecheck] using hte1
                        have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                        have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                          simpa [typecheck, ctx', ctxBase, varEnv', updateCtxFromResult] using hte2
                        have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                        have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', ctxBase, varEnv', updateCtxFromResult] using h2)
                        simpa [hresnext] using hctx
          | guardOnly k =>
              simp [hpred] at htc
              cases hte1 : typecheckExpr ctx e1 fuel' with
              | error err =>
                  simp [hte1] at htc
                  cases htc
              | ok r1 =>
                  simp [hte1] at htc
                  let varEnv' := ctx.varEnv.update x r1.qualType
                  let ctxBase : TypeContext := updateCtxFromResult ctx r1
                  let ctx' : TypeContext := { ctxBase with varEnv := varEnv' }
                  cases hte2 : typecheckExpr ctx' e2 fuel' with
                  | error err =>
                      erw [hte2] at htc
                      simp at htc
                      cases htc
                  | ok r2 =>
                      erw [hte2] at htc
                      simp at htc
                      rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                      simp [hq2, pure, Except.pure] at htc
                      have hresnext : r2.nextTag' = res.nextTag' := by
                        simpa using congrArg TypeResult.nextTag' htc
                      have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                        simpa [typecheck] using hte1
                      have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                      have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                        simpa [typecheck, ctx', ctxBase, varEnv', updateCtxFromResult] using hte2
                      have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                      have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', ctxBase, varEnv', updateCtxFromResult] using h2)
                      simpa [hresnext] using hctx
          | noPred =>
              simp [hpred] at htc
              cases hte1 : typecheckExpr ctx e1 fuel' with
              | error err =>
                  simp [hte1] at htc
                  cases htc
              | ok r1 =>
                  simp [hte1] at htc
                  let varEnv' := ctx.varEnv.update x r1.qualType
                  let ctxBase : TypeContext := updateCtxFromResult ctx r1
                  let ctx' : TypeContext := { ctxBase with varEnv := varEnv' }
                  cases hte2 : typecheckExpr ctx' e2 fuel' with
                  | error err =>
                      erw [hte2] at htc
                      simp at htc
                      cases htc
                  | ok r2 =>
                      erw [hte2] at htc
                      simp at htc
                      rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                      simp [hq2, pure, Except.pure] at htc
                      have hresnext : r2.nextTag' = res.nextTag' := by
                        simpa using congrArg TypeResult.nextTag' htc
                      have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                        simpa [typecheck] using hte1
                      have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                      have hte2' : typecheck ctx' e2 fuel' = .ok r2 := by
                        simpa [typecheck, ctx', ctxBase, varEnv', updateCtxFromResult] using hte2
                      have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx' r2 hte2'
                      have hctx : ctx.nextTag ≤ r2.nextTag' := Nat.le_trans h1 (by simpa [ctx', ctxBase, varEnv', updateCtxFromResult] using h2)
                      simpa [hresnext] using hctx

private lemma typecheckIf_nextTag_mono_normal (ctx : TypeContext) (e1 e2 e3 : Expr)
    (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
      typecheck ctx' e' m = .ok res' →
      ctx'.nextTag ≤ res'.nextTag') :
  typecheckIf ctx e1 e2 e3 fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  unfold typecheckIf at htc
  cases fuel with
  | zero =>
      simp at htc
  | succ fuel' =>
      simp [bind, Except.bind] at htc
      cases hmatch : matchGuard e1 ctx.memEnv ctx.varEnv fuel' with
      | error err =>
          simp [hmatch] at htc
          cases hte1 : typecheckExpr ctx e1 fuel' with
          | error err1 =>
              simp [hte1] at htc
          | ok r1 =>
              simp [hte1] at htc
              rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
              simp [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · simp [hbool] at htc
                let ctx1 : TypeContext := updateCtxFromResult ctx r1
                let branchPc := joinPoison ctx.pc p1
                let ctx'' := { ctx1 with pc := branchPc }
                cases hte2 : typecheckExpr ctx'' e2 fuel' with
                | error err2 =>
                    erw [hte2] at htc
                    simp at htc
                    cases htc
                | ok r2 =>
                    erw [hte2] at htc
                    simp at htc
                    rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                    simp [hq2] at htc
                    let ctxForE3 := { ctx'' with nextLoc := r2.nextLoc', nextTag := r2.nextTag' }
                    cases hte3 : typecheckExpr ctxForE3 e3 fuel' with
                    | error err3 =>
                        erw [hte3] at htc
                        simp at htc
                        cases htc
                    | ok r3 =>
                        erw [hte3] at htc
                        simp at htc
                        rcases hq3 : r3.qualType with ⟨etyp3, p3, pred3⟩
                        simp [hq3] at htc
                        by_cases hcompat : beqETypSignature etyp2 etyp3
                        · simp [hcompat, pure, Except.pure] at htc
                          cases htc
                          have hte1' : typecheck ctx e1 fuel' = .ok r1 := by
                            simpa [typecheck] using hte1
                          have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1 hte1'
                          have hte2' : typecheck ctx'' e2 fuel' = .ok r2 := by
                            simpa [typecheck, ctx'', ctx1, branchPc] using hte2
                          have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx'' r2 hte2'
                          have hctx_to_ctx2 : ctx.nextTag ≤ r2.nextTag' := by
                            have hctx1 : ctx.nextTag ≤ r1.nextTag' := h1
                            have hctx2 : ctx''.nextTag ≤ r2.nextTag' := h2
                            have hctx1eq : ctx''.nextTag = r1.nextTag' := by
                              simp [ctx'', ctx1, updateCtxFromResult]
                            exact Nat.le_trans hctx1 (by simpa [hctx1eq] using hctx2)
                          exact Nat.le_trans hctx_to_ctx2 (Nat.le_max_left _ _)
                        · simp [hcompat] at htc
                          cases htc
              · simp [hbool] at htc
      | ok kd =>
          rcases kd with ⟨k, deps⟩
          simp [hmatch] at htc
          cases hte1 : typecheckExpr { ctx with pureCtx := true } e1 fuel' with
          | error err1 =>
              simp [hte1] at htc
          | ok r1 =>
              simp [hte1] at htc
              rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
              simp [hq1] at htc
              by_cases hbool : etyp1 = ETyp.bool
              · simp [hbool] at htc
                let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
                let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                cases hreg : ctx.regime.lookup? k with
                | some b =>
                    cases b with
                    | true =>
                        simp [hreg] at htc
                        cases hte2 : typecheckExpr ctxTrue e2 fuel' with
                        | error err2 =>
                            erw [hte2] at htc
                            simp at htc
                            cases htc
                        | ok r2 =>
                            erw [hte2] at htc
                            simp at htc
                            rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                            simp [hq2] at htc
                            let ctxFalse' := { ctxFalse with nextLoc := r2.nextLoc', nextTag := r2.nextTag' }
                            cases hte3 : typecheckExpr ctxFalse' e3 fuel' with
                            | error err3 =>
                                erw [hte3] at htc
                                simp at htc
                                cases htc
                            | ok r3 =>
                                erw [hte3] at htc
                                simp at htc
                                rcases hq3 : r3.qualType with ⟨etyp3, p3, pred3⟩
                                simp [hq3] at htc
                                by_cases hcompat : beqETypSignature etyp2 etyp3
                                · simp [hcompat, pure, Except.pure] at htc
                                  cases htc
                                  have hte2' : typecheck ctxTrue e2 fuel' = .ok r2 := by
                                    simpa [typecheck, ctxTrue] using hte2
                                  have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctxTrue r2 hte2'
                                  have hctx : ctx.nextTag ≤ r2.nextTag' := by
                                    simpa [ctxTrue] using h2
                                  exact Nat.le_trans hctx (Nat.le_max_left _ _)
                                · simp [hcompat] at htc
                                  cases htc
                    | false =>
                        simp [hreg] at htc
                        cases hte2 : typecheckExpr ctxTrue e2 fuel' with
                        | error err2 =>
                            erw [hte2] at htc
                            simp at htc
                            cases htc
                        | ok r2 =>
                            erw [hte2] at htc
                            simp at htc
                            rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                            simp [hq2] at htc
                            let ctxFalse' := { ctxFalse with nextLoc := r2.nextLoc', nextTag := r2.nextTag' }
                            cases hte3 : typecheckExpr ctxFalse' e3 fuel' with
                            | error err3 =>
                                erw [hte3] at htc
                                simp at htc
                                cases htc
                            | ok r3 =>
                                erw [hte3] at htc
                                simp at htc
                                rcases hq3 : r3.qualType with ⟨etyp3, p3, pred3⟩
                                simp [hq3] at htc
                                by_cases hcompat : beqETypSignature etyp2 etyp3
                                · simp [hcompat, pure, Except.pure] at htc
                                  cases htc
                                  have hte2' : typecheck ctxTrue e2 fuel' = .ok r2 := by
                                    simpa [typecheck, ctxTrue] using hte2
                                  have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctxTrue r2 hte2'
                                  have hctx : ctx.nextTag ≤ r2.nextTag' := by
                                    simpa [ctxTrue] using h2
                                  exact Nat.le_trans hctx (Nat.le_max_left _ _)
                                · simp [hcompat] at htc
                                  cases htc
                | none =>
                    simp [hreg] at htc
                    cases hte1std : typecheckExpr ctx e1 fuel' with
                    | error err1std =>
                        erw [hte1std] at htc
                        simp at htc
                        cases htc
                    | ok r1std =>
                        erw [hte1std] at htc
                        simp at htc
                        rcases hq1std : r1std.qualType with ⟨etyp1std, p1std, pred1std⟩
                        simp [hq1std] at htc
                        by_cases hboolStd : etyp1std = ETyp.bool
                        · simp [hboolStd] at htc
                          let ctx1 : TypeContext := updateCtxFromResult ctx r1std
                          let branchPc := joinPoison ctx.pc p1std
                          let ctx'' := { ctx1 with pc := branchPc }
                          cases hte2 : typecheckExpr ctx'' e2 fuel' with
                          | error err2 =>
                              erw [hte2] at htc
                              simp at htc
                              cases htc
                          | ok r2 =>
                              erw [hte2] at htc
                              simp at htc
                              rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                              simp [hq2] at htc
                              let ctxForE3 := { ctx'' with nextLoc := r2.nextLoc', nextTag := r2.nextTag' }
                              cases hte3 : typecheckExpr ctxForE3 e3 fuel' with
                              | error err3 =>
                                  erw [hte3] at htc
                                  simp at htc
                                  cases htc
                              | ok r3 =>
                                  erw [hte3] at htc
                                  simp at htc
                                  rcases hq3 : r3.qualType with ⟨etyp3, p3, pred3⟩
                                  simp [hq3] at htc
                                  by_cases hcompat : beqETypSignature etyp2 etyp3
                                  · simp [hcompat, pure, Except.pure] at htc
                                    cases htc
                                    have hte1std' : typecheck ctx e1 fuel' = .ok r1std := by
                                      simpa [typecheck] using hte1std
                                    have h1 := IH fuel' (Nat.lt_succ_self fuel') e1 ctx r1std hte1std'
                                    have hte2' : typecheck ctx'' e2 fuel' = .ok r2 := by
                                      simpa [typecheck, ctx'', ctx1, branchPc, updateCtxFromResult] using hte2
                                    have h2 := IH fuel' (Nat.lt_succ_self fuel') e2 ctx'' r2 hte2'
                                    have hctx_to_ctx2 : ctx.nextTag ≤ r2.nextTag' := by
                                      have hctx1 : ctx.nextTag ≤ r1std.nextTag' := h1
                                      have hctx2 : ctx''.nextTag ≤ r2.nextTag' := h2
                                      have hctx1eq : ctx''.nextTag = r1std.nextTag' := by
                                        simp [ctx'', ctx1, updateCtxFromResult]
                                      exact Nat.le_trans hctx1 (by simpa [hctx1eq] using hctx2)
                                    exact Nat.le_trans hctx_to_ctx2 (Nat.le_max_left _ _)
                                  · simp [hcompat] at htc
                                    cases htc
                        · simp [hboolStd] at htc
                          cases htc
              · simp [hbool] at htc

private lemma typecheck_nextTag_mono_normal_main : ∀ (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult),
  typecheck ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro ctx e fuel res htc
  revert ctx e res htc
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro ctx e res htc
      have IH_converted : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e' m = .ok res' →
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
          have IH_fuel' : ∀ m < fuel', ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
            typecheck ctx' e' m = .ok res' →
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
              have hpres := typecheckVar_preserves_nextTag ctx x res htc
              simp [hpres]
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
              simp at htc
              exact typecheckExternVal_nextTag_mono ctx typ poison pred res htc
          | externFn arg argTyp retSpec effects =>
              simp at htc
              have hpres := typecheckExternFn_preserves_nextTag ctx arg argTyp retSpec effects res htc
              simp [hpres]
          | externPfn arg argTyp retSpec =>
              simp at htc
              have hpres := typecheckExternPfn_preserves_nextTag ctx arg argTyp retSpec res htc
              simp [hpres]
          | op e1 op e2 =>
              simp at htc
              exact typecheckOp_nextTag_mono_normal ctx e1 e2 fuel' op res IH_fuel' htc
          | unaryop op e1 =>
              simp at htc
              exact typecheckUnaryOp_nextTag_mono_normal ctx op e1 fuel' res IH_fuel' htc
          | ite e1 e2 e3 =>
              simp at htc
              exact typecheckIf_nextTag_mono_normal ctx e1 e2 e3 fuel' res IH_fuel' htc
          | newRef e1 =>
              simp at htc
              exact typecheckNewRef_nextTag_mono_normal ctx e1 fuel' res IH_fuel' htc
          | assign e1 e2 =>
              simp at htc
              exact typecheckAssign_nextTag_mono_normal ctx e1 e2 fuel' res IH_fuel' htc
          | deref e1 =>
              simp at htc
              exact typecheckDeref_nextTag_mono_normal ctx e1 fuel' res IH_fuel' htc
          | seq e1 e2 =>
              simp at htc
              exact typecheckSeq_nextTag_mono_normal ctx e1 e2 fuel' res IH_fuel' htc
          | vlet x e1 e2 =>
              simp at htc
              exact typecheckVlet_nextTag_mono_normal ctx x e1 e2 fuel' res IH_fuel' htc
          | app e1 e2 =>
              simp at htc
              exact typecheckApp_nextTag_mono_normal ctx e1 e2 fuel' res IH_fuel' htc

lemma typecheck_normal_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  exact typecheck_nextTag_mono_normal_main ctx e fuel res htc

lemma typecheck_nextTag_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextTag ≤ res.nextTag' := by
  intro htc
  exact typecheck_normal_nextTag_mono ctx e fuel res htc

end typecheck_nextTag_normal_mono_proof

section typecheck_tagEnvBounded_proof

/-- Monotonicity of tagEnvBounded under larger nextTag. -/
private lemma tagEnvBounded_mono (tagEnv : TagEnv) (nt nt' : Tag)
    (hb : tagEnvBounded tagEnv nt) (hle : nt ≤ nt') : tagEnvBounded tagEnv nt' := by
  intro k hk
  exact Nat.lt_of_lt_of_le (hb k hk) hle

/-- invalidateTagDeps only removes entries; the bound is preserved. -/
private lemma invalidateTagDeps_preserves_tagEnvBounded (te : TagEnv) (ls : LocSet) (nt : Tag)
    (hb : tagEnvBounded te nt) : tagEnvBounded (invalidateTagDeps te ls) nt := by
  intro k hk
  apply hb
  intro hte
  apply hk
  unfold invalidateTagDeps
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_filter]
  -- te[k]?.pfilter f = none because te[k]? = none
  have hk' : te[k]? = none := by simpa [Std.ExtTreeMap.get?_eq_getElem?] using hte
  rw [hk']
  simp [Option.pfilter]

/-- typecheckVar preserves tagEnv (all branches return ctx.tagEnv). -/
private lemma typecheckVar_preserves_tagEnv_aux (ctx : TypeContext) (x : Name) (res : TypeResult) :
    typecheckVar ctx x = .ok res → res.tagEnv' = ctx.tagEnv := by
  intro htc
  unfold typecheckVar at htc
  cases h_lookup : ctx.varEnv.lookup x with
  | none => simp [h_lookup] at htc
  | some qt =>
      simp [h_lookup] at htc
      cases qt with
      | mk etyp poison pred =>
          cases pred with
          | noPred =>
              simp at htc
              -- htc : Except.ok {..., tagEnv' := ctx.tagEnv, ...} = Except.ok res
              exact (congrArg TypeResult.tagEnv' (Except.ok.inj htc)).symm
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
                      have htagopt' : ctx.tagEnv[k]? = none :=
                        by simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      -- htc : {..., tagEnv' := ctx.tagEnv, ...} = res
                      exact (congrArg TypeResult.tagEnv' htc).symm
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ :=
                            by simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b <;> simp [pure, Except.pure] at htc <;>
                            exact (congrArg TypeResult.tagEnv' htc).symm
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
                      have htagopt' : ctx.tagEnv[k]? = none :=
                        by simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                      simp [htagopt', pure, Except.pure] at htc
                      exact (congrArg TypeResult.tagEnv' htc).symm
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          have htagopt' : ctx.tagEnv[k]? = some ⟨b, deps⟩ :=
                            by simpa [Std.ExtTreeMap.get?_eq_getElem?] using htagopt
                          simp [htagopt'] at htc
                          cases b <;> simp [pure, Except.pure] at htc <;>
                            exact (congrArg TypeResult.tagEnv' htc).symm

/-- The main induction: typecheckExpr preserves tagEnvBounded. -/
private lemma typecheckExpr_preserves_tagEnvBounded_main :
    ∀ (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult),
    typecheckExpr ctx e fuel = .ok res →
    tagEnvBoundedInCtx ctx →
    tagEnvBounded res.tagEnv' res.nextTag' := by
  intro ctx e fuel res htc hbound
  revert ctx e res htc hbound
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro ctx e res htc hbound
      have IH_fuel : ∀ m < fuel, ∀ (e' : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheckExpr ctx' e' m = .ok res' →
          tagEnvBoundedInCtx ctx' →
          tagEnvBounded res'.tagEnv' res'.nextTag' :=
        fun m h_lt e' ctx' res' htc' hbound' => IH m h_lt ctx' e' res' htc' hbound'
      cases fuel with
      | zero => simp [typecheckExpr] at htc
      | succ fuel' =>
          unfold typecheckExpr at htc
          cases e with
          | num _n =>
              simp [typecheckInt] at htc; cases htc; exact hbound
          | bool _b =>
              simp [typecheckBool] at htc; cases htc; exact hbound
          | unit =>
              simp [typecheckUnit] at htc; cases htc; exact hbound
          | str _s =>
              simp [typecheckString] at htc; cases htc; exact hbound
          | var x =>
              have hnext := typecheckVar_preserves_nextTag ctx x res htc
              have htagEnv : res.tagEnv' = ctx.tagEnv :=
                typecheckVar_preserves_tagEnv_aux ctx x res htc
              rw [htagEnv, hnext]; exact hbound
          | fn _x _st1 _body _st2 =>
              simp [typecheckFn] at htc; cases htc; exact hbound
          | pfn _x _st1 _body _st2 =>
              simp [typecheckPfn, Bind.bind, Except.bind] at htc
              cases h_topexpr : _body.toPExpr with
              | error _ => simp [h_topexpr] at htc
              | ok _ => simp [h_topexpr] at htc; cases htc; exact hbound
          | externVal typ poison pred =>
              have hmono := typecheckExternVal_nextTag_mono ctx typ poison pred res htc
              have htagEnv : res.tagEnv' = ctx.tagEnv := by
                have htce : typecheckExternVal ctx typ poison pred = .ok res := htc
                unfold typecheckExternVal at htce
                split at htce
                · simp at htce
                · simp at htce
                · simp only [bind, Except.bind, pure, Except.pure] at htce
                  cases halloc : collectAndAllocExternTags [pred] ctx.nextTag with
                  | error err => simp [halloc] at htce
                  | ok result =>
                      rcases result with ⟨tagMapping, nextTag'⟩
                      simp only [halloc] at htce
                      cases hresolve : resolveSyntaxPred pred ctx.varEnv tagMapping with
                      | error err => simp [hresolve] at htce
                      | ok resolvedPred =>
                          simp only [hresolve] at htce
                          cases hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx with
                          | error err => simp [hsurf] at htce
                          | ok surfResult =>
                              simp only [hsurf] at htce
                              exact (congrArg TypeResult.tagEnv' (Except.ok.inj htce)).symm
              rw [htagEnv]
              exact tagEnvBounded_mono ctx.tagEnv ctx.nextTag res.nextTag' hbound hmono
          | externFn _arg _argTyp _retSpec _effects =>
              have hpres := typecheckExternFn_preserves_nextTag ctx _arg _argTyp _retSpec _effects res htc
              have htagEnv : res.tagEnv' = ctx.tagEnv := by
                have htce : typecheckExternFn ctx _arg _argTyp _retSpec _effects = .ok res := htc
                simp [typecheckExternFn, pure, Except.pure] at htce
                exact (congrArg TypeResult.tagEnv' htce).symm
              rw [htagEnv, hpres]; exact hbound
          | externPfn _arg _argTyp _retSpec =>
              have hpres := typecheckExternPfn_preserves_nextTag ctx _arg _argTyp _retSpec res htc
              have htagEnv : res.tagEnv' = ctx.tagEnv := by
                have htce : typecheckExternPfn ctx _arg _argTyp _retSpec = .ok res := htc
                simp [typecheckExternPfn, pure, Except.pure] at htce
                exact (congrArg TypeResult.tagEnv' htce).symm
              rw [htagEnv, hpres]; exact hbound
          | unaryop op e1 =>
              -- htc : typecheckUnaryOp ctx op e1 fuel' = .ok res
              unfold typecheckUnaryOp at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  cases hte1 : typecheckExpr ctx e1 fuel'' with
                  | error err => simp [hte1] at htc
                  | ok r1 =>
                      simp [hte1] at htc
                      rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
                      simp [hq1] at htc
                      cases hop : opUnaryEType? op etyp1 with
                      | none => simp [hop] at htc
                      | some outType =>
                          simp [hop, pure, Except.pure] at htc; cases htc
                          have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by
                            simpa [typecheck] using hte1
                          have h_lt : fuel'' < fuel' + 1 := by omega
                          exact IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
          | op e1 _op e2 =>
              -- htc : typecheckOp ctx e1 e2 fuel' _op = .ok res
              unfold typecheckOp at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  cases hte1 : typecheckExpr ctx e1 fuel'' with
                  | error err => simp [hte1] at htc
                  | ok r1 =>
                      simp [hte1] at htc
                      rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
                      simp [hq1] at htc
                      let ctx' : TypeContext := updateCtxFromResult ctx r1
                      cases hte2 : typecheckExpr ctx' e2 fuel'' with
                      | error err => erw [hte2] at htc; simp at htc
                      | ok r2 =>
                          erw [hte2] at htc
                          rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                          simp [hq2] at htc
                          cases hop : opEType? _op etyp1 etyp2 with
                          | none => simp [hop] at htc
                          | some outType =>
                              simp [hop, pure, Except.pure] at htc; cases htc
                              have h_lt : fuel'' < fuel' + 1 := by omega
                              have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by
                                simpa [typecheck] using hte1
                              have hbound1 := IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
                              have hte2' : typecheck ctx' e2 fuel'' = .ok r2 := by
                                simpa [typecheck, ctx'] using hte2
                              exact IH_fuel fuel'' h_lt e2 ctx' r2 hte2'
                                (by simp only [tagEnvBoundedInCtx, updateCtxFromResult, ctx']; exact hbound1)
          | seq e1 e2 =>
              unfold typecheckSeq at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  cases hte1 : typecheckExpr ctx e1 fuel'' with
                  | error err => simp [hte1] at htc
                  | ok r1 =>
                      simp [hte1] at htc
                      let ctx' := updateCtxFromResult ctx r1
                      cases hte2 : typecheckExpr ctx' e2 fuel'' with
                      | error err => simp [hte2, ctx'] at htc
                      | ok r2 =>
                          simp [hte2, ctx'] at htc
                          have hres : r2 = res := by simpa [pure, Except.pure] using htc
                          have h_lt : fuel'' < fuel' + 1 := by omega
                          have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by
                            simpa [typecheck] using hte1
                          have hbound1 := IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
                          have hte2' : typecheck ctx' e2 fuel'' = .ok r2 := by
                            simpa [typecheck, ctx'] using hte2
                          have hbound2 := IH_fuel fuel'' h_lt e2 ctx' r2 hte2'
                            (by simp only [tagEnvBoundedInCtx, updateCtxFromResult, ctx']; exact hbound1)
                          simpa [hres] using hbound2
          | vlet x e1 e2 =>
              unfold typecheckVlet at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  -- Handle all three predicate subcases for the outer vlet
                  -- Using a common proof pattern
                  have step_e1_e2 : ∀ (ctx1 : TypeContext),
                      ctx1.tagEnv = ctx.tagEnv → ctx1.nextTag = ctx.nextTag →
                      ∀ r1 : TypeResult, typecheckExpr ctx1 e1 fuel'' = .ok r1 →
                      ∀ (ctx2 : TypeContext),
                      ctx2.tagEnv = r1.tagEnv' → ctx2.nextTag = r1.nextTag' →
                      ∀ r2 : TypeResult, typecheckExpr ctx2 e2 fuel'' = .ok r2 →
                      r2.nextTag' = res.nextTag' → r2.tagEnv' = res.tagEnv' →
                      tagEnvBounded res.tagEnv' res.nextTag' := by
                    intro ctx1 hctx1Tag hctx1Next r1 hte1 ctx2 hctx2Tag hctx2Next r2 hte2 hresnext hresTag
                    have h_lt : fuel'' < fuel' + 1 := by omega
                    have hte1' : typecheck ctx1 e1 fuel'' = .ok r1 := by
                      simpa [typecheck] using hte1
                    have hbound1 := IH_fuel fuel'' h_lt e1 ctx1 r1 hte1'
                      (by simp only [tagEnvBoundedInCtx, hctx1Tag, hctx1Next]; exact hbound)
                    have hte2' : typecheck ctx2 e2 fuel'' = .ok r2 := by
                      simpa [typecheck] using hte2
                    have hbound2 := IH_fuel fuel'' h_lt e2 ctx2 r2 hte2'
                      (by simp only [tagEnvBoundedInCtx, hctx2Tag, hctx2Next]; exact hbound1)
                    simpa [hresnext, hresTag] using hbound2
                  cases hlookup : ctx.varEnv.lookup x with
                  | none =>
                      simp [hlookup] at htc
                      cases hte1 : typecheckExpr ctx e1 fuel'' with
                      | error err => simp [hte1, pure, Except.pure] at htc
                      | ok r1 =>
                          simp [hte1] at htc
                          let ctxBase := updateCtxFromResult ctx r1
                          let ctx' : TypeContext := { ctxBase with varEnv := ctx.varEnv.update x r1.qualType }
                          cases hte2 : typecheckExpr ctx' e2 fuel'' with
                          | error err => erw [hte2] at htc; simp [pure, Except.pure] at htc
                          | ok r2 =>
                              erw [hte2] at htc; simp at htc
                              rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                              simp [hq2, pure, Except.pure] at htc
                              exact step_e1_e2 ctx rfl rfl r1 hte1 ctx' rfl rfl r2 hte2
                                (by simpa using congrArg TypeResult.nextTag' htc)
                                (by simpa using congrArg TypeResult.tagEnv' htc)
                  | some qtOuter =>
                      simp [hlookup] at htc
                      cases hpred : qtOuter.pred with
                      | guardClosure k arg body env =>
                          simp [hpred] at htc
                          by_cases hregSome : (ctx.regime.lookup? k).isSome = true
                          · simp [hregSome] at htc
                          · simp [hregSome] at htc
                            cases hte1 : typecheckExpr ctx e1 fuel'' with
                            | error err => simp [hte1, pure, Except.pure] at htc
                            | ok r1 =>
                                simp [hte1] at htc
                                let ctxBase := updateCtxFromResult ctx r1
                                let ctx' : TypeContext := { ctxBase with varEnv := ctx.varEnv.update x r1.qualType }
                                cases hte2 : typecheckExpr ctx' e2 fuel'' with
                                | error err => erw [hte2] at htc; simp [pure, Except.pure] at htc
                                | ok r2 =>
                                    erw [hte2] at htc; simp at htc
                                    rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                                    simp [hq2, pure, Except.pure] at htc
                                    exact step_e1_e2 ctx rfl rfl r1 hte1 ctx' rfl rfl r2 hte2
                                      (by simpa using congrArg TypeResult.nextTag' htc)
                                      (by simpa using congrArg TypeResult.tagEnv' htc)
                      | guardOnly k =>
                          simp [hpred] at htc
                          cases hte1 : typecheckExpr ctx e1 fuel'' with
                          | error err => simp [hte1, pure, Except.pure] at htc
                          | ok r1 =>
                              simp [hte1] at htc
                              let ctxBase := updateCtxFromResult ctx r1
                              let ctx' : TypeContext := { ctxBase with varEnv := ctx.varEnv.update x r1.qualType }
                              cases hte2 : typecheckExpr ctx' e2 fuel'' with
                              | error err => erw [hte2] at htc; simp [pure, Except.pure] at htc
                              | ok r2 =>
                                  erw [hte2] at htc; simp at htc
                                  rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                                  simp [hq2, pure, Except.pure] at htc
                                  exact step_e1_e2 ctx rfl rfl r1 hte1 ctx' rfl rfl r2 hte2
                                    (by simpa using congrArg TypeResult.nextTag' htc)
                                    (by simpa using congrArg TypeResult.tagEnv' htc)
                      | noPred =>
                          simp [hpred] at htc
                          cases hte1 : typecheckExpr ctx e1 fuel'' with
                          | error err => simp [hte1, pure, Except.pure] at htc
                          | ok r1 =>
                              simp [hte1] at htc
                              let ctxBase := updateCtxFromResult ctx r1
                              let ctx' : TypeContext := { ctxBase with varEnv := ctx.varEnv.update x r1.qualType }
                              cases hte2 : typecheckExpr ctx' e2 fuel'' with
                              | error err => erw [hte2] at htc; simp [pure, Except.pure] at htc
                              | ok r2 =>
                                  erw [hte2] at htc; simp at htc
                                  rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                                  simp [hq2, pure, Except.pure] at htc
                                  exact step_e1_e2 ctx rfl rfl r1 hte1 ctx' rfl rfl r2 hte2
                                    (by simpa using congrArg TypeResult.nextTag' htc)
                                    (by simpa using congrArg TypeResult.tagEnv' htc)
          | newRef e1 =>
              unfold typecheckNewRef at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  cases hte1 : typecheckExpr ctx e1 fuel'' with
                  | error err => simp [hte1] at htc
                  | ok r1 =>
                      simp [hte1] at htc
                      rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
                      simp [hq1] at htc
                      by_cases hInt : etyp1 = ETyp.int
                      · simp [hInt, freshTLocRes, pure, Except.pure] at htc; cases htc
                        have h_lt : fuel'' < fuel' + 1 := by omega
                        have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by
                          simpa [typecheck] using hte1
                        exact IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
                      · exfalso; simp [hInt] at htc
          | assign e1 e2 =>
              unfold typecheckAssign at htc
              cases hfuel : fuel' with
              | zero => simp [hfuel] at htc
              | succ fuel'' =>
                  rw [hfuel] at htc
                  simp [bind, Except.bind] at htc
                  cases hte1 : typecheckExpr ctx e1 fuel'' with
                  | error err => simp [hte1] at htc
                  | ok r1 =>
                      simp [hte1] at htc
                      rcases hq1 : r1.qualType with ⟨etyp1, p1, pred1⟩
                      simp [hq1] at htc
                      cases etyp1 with
                      | int => simp at htc
                      | bool => simp at htc
                      | unit => simp at htc
                      | string => simp at htc
                      | arrow st1 st2 p tcls => simp at htc
                      | parrow st1 st2 p tcls => simp at htc
                      | ref ls =>
                          simp at htc
                          let ctx' : TypeContext := updateCtxFromResult ctx r1
                          cases hte2 : typecheckExpr ctx' e2 fuel'' with
                          | error err => erw [hte2] at htc; simp at htc
                          | ok r2 =>
                              erw [hte2] at htc; simp at htc
                              rcases hq2 : r2.qualType with ⟨etyp2, p2, pred2⟩
                              simp [hq2] at htc
                              by_cases hInt2 : etyp2 = ETyp.int
                              · simp [hInt2, pure, Except.pure] at htc
                                have hresnext : r2.nextTag' = res.nextTag' := by
                                  simpa using congrArg TypeResult.nextTag' htc
                                have hresTagInv : invalidateTagDeps r2.tagEnv' ls = res.tagEnv' := by
                                  simpa using congrArg TypeResult.tagEnv' htc
                                have h_lt : fuel'' < fuel' + 1 := by omega
                                have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by
                                  simpa [typecheck] using hte1
                                have hbound1 := IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
                                have hte2' : typecheck ctx' e2 fuel'' = .ok r2 := by
                                  simpa [typecheck, ctx'] using hte2
                                have hbound2 := IH_fuel fuel'' h_lt e2 ctx' r2 hte2'
                                  (by simp only [tagEnvBoundedInCtx, updateCtxFromResult, ctx']; exact hbound1)
                                have hboundInv := invalidateTagDeps_preserves_tagEnvBounded
                                  r2.tagEnv' ls r2.nextTag' hbound2
                                rw [← hresTagInv, ← hresnext]; exact hboundInv
                              · exfalso; simp [hInt2] at htc
          | deref e1 =>
              -- Save original htc before unfolding for structure lemma
              have htc_deref : typecheckDeref ctx e1 fuel' = .ok res := by
                simpa [typecheckDeref] using htc
              cases hfuel : fuel' with
              | zero =>
                  simp [hfuel, typecheckDeref] at htc
              | succ fuel'' =>
                  have h_lt : fuel'' < fuel' + 1 := by omega
                  obtain ⟨r1, hte1, _, hte_eq, _, hnt_eq, _⟩ :=
                    typecheckDeref_structure ctx e1 (fuel'' + 1) res (by rwa [← hfuel])
                  simp only [Nat.add_sub_cancel] at hte1
                  have hte1' : typecheck ctx e1 fuel'' = .ok r1 := by simpa [typecheck] using hte1
                  have hbound1 := IH_fuel fuel'' h_lt e1 ctx r1 hte1' hbound
                  rw [hte_eq, hnt_eq]; exact hbound1
          | ite e1 e2 e3 => sorry
          | app e1 e2 => sorry

lemma typecheckExpr_preserves_tagEnvBounded
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckExpr ctx e fuel = .ok res)
    (hbound : tagEnvBoundedInCtx ctx) :
    tagEnvBounded res.tagEnv' res.nextTag' :=
  typecheckExpr_preserves_tagEnvBounded_main ctx e fuel res htc hbound

end typecheck_tagEnvBounded_proof

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
        rcases h1 with ⟨k, deps, _, _, res1, htc1, _, res2, res3, htc2, _htc3, _, _, hnextloc, _hnexttag, _, _⟩
        have IH2 := IH fuel' h_fuel e2 { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ } res2 htc2
        simp at IH2
        calc ctx.nextLoc
          _ ≤ res2.nextLoc' := IH2
          _ ≤ max res2.nextLoc' res3.nextLoc' := le_max_left _ _
          _ = res.nextLoc' := hnextloc.symm
      | inr h_rest =>
        cases h_rest with
        | inl h2 =>
          -- R(k) = some false
          rcases h2 with ⟨k, deps, _, _, res1, htc1, _, res2, res3, htc2, htc3, _, _, hnextloc, _hnexttag, _, _⟩
          let ctxTrue := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
          let ctxFalse := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                     nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
          have IH2 := IH fuel' h_fuel e2 ctxTrue res2 (by simpa [ctxTrue] using htc2)
          simp [ctxTrue] at IH2
          have IH3 := IH fuel' h_fuel e3 ctxFalse res3 (by simpa [ctxFalse] using htc3)
          simp [ctxFalse] at IH3
          calc ctx.nextLoc
            _ ≤ res2.nextLoc' := IH2
            _ ≤ res3.nextLoc' := IH3
            _ ≤ max res2.nextLoc' res3.nextLoc' := le_max_right _ _
            _ = res.nextLoc' := hnextloc.symm
        | inr hstd =>
            have ⟨_h_std_case, h_res⟩ := hstd
            have ⟨res1, htc1, _hbool, h_res2⟩ := h_res
            have ⟨res2, h_body⟩ := h_res2
            have ⟨htc2, h_res3⟩ := h_body
            have ⟨res3, h_body3⟩ := h_res3
            have ⟨htc3, _hmem, _htag, _hloc, hnextloc, _hregime, _hpoison, _hetyp, _hpred⟩ := h_body3
            let ctx1 : TypeContext := { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
            let pc' := joinPoison ctx.pc res1.qualType.poison
            let ctx'' := { ctx1 with pc := pc' }
            let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
            have htc1' : typecheck ctx e1 fuel' = .ok res1 := by simpa [typecheck] using htc1
            have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by simpa [typecheck, ctx'', ctx1, pc'] using htc2
            have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by simpa [typecheck, ctxForE3, ctx'', ctx1, pc'] using htc3
            have IH1 := IH fuel' h_fuel e1 ctx res1 htc1'
            have IH2 := IH fuel' h_fuel e2 ctx'' res2 htc2'
            have h_loc1 : ctx.nextLoc ≤ res1.nextLoc' := IH1
            have h_loc2 : res1.nextLoc' ≤ res2.nextLoc' := by
              have := IH2
              simpa [ctx'', ctx1] using this
            calc ctx.nextLoc
              _ ≤ res1.nextLoc' := h_loc1
              _ ≤ res2.nextLoc' := h_loc2
              _ ≤ max res2.nextLoc' res3.nextLoc' := Nat.le_max_left _ _
              _ = res.nextLoc' := _hloc.symm

lemma joinTypeResults_nextLoc_eq_max
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
              joinMemEnvsStrong acc.2.1 result.memEnv',
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
                      joinMemEnvsStrong acc.2.1 result.memEnv',
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
                        joinMemEnvsStrong acc.2.1 x.memEnv',
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
                      joinMemEnvsStrong acc.2.1 result.memEnv',
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
  (typ : Typ) (poison : Bool) (pred : Predicate)
  (nextLoc : Loc) (ret : QTyp × Loc) :
  returnSpecToQTyp typ poison pred nextLoc = .ok ret →
  ret.2 = nextLoc := by
  intro h
  unfold returnSpecToQTyp at h
  cases typ with
  | int | bool | unit | string =>
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
    -- Extern case: nestedFn/nestedPfn set nextLoc' := r1.nextLoc' (le_refl);
    -- simple uses returnSpecToQTyp which preserves nextLoc (equality → le_refl)
    split at happly
    · simp at happly
    · split at happly
      · simp at happly
      · split at happly
        · -- simple case: nextLoc' from returnSpecToQTyp which preserves nextLoc
          split at happly
          · simp at happly
          · -- happly now: (fun a => {nextLoc' := a.2, ...}) <$> returnSpecToQTyp ... = ok r2
            simp only [Functor.map, Except.map] at happly
            split at happly
            · simp at happly
            · -- ok case: r2 = {nextLoc' := v.2, ...}, and v.2 = r1.nextLoc' by preservation
              rename_i v hret
              simp only [Except.ok.injEq] at happly
              rw [← happly]
              have := returnSpecToQTyp_preserves_nextLoc _ _ _ r1.nextLoc' v hret
              simp [this]
        · simp only [pure, Except.pure, Except.ok.injEq] at happly; rw [← happly]
        · simp only [pure, Except.pure, Except.ok.injEq] at happly; rw [← happly]

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
    rcases happly : applyFnTClosure f t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons : List.cons r <$> List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs' with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap : List.mapM (fun tcl => applyFnTClosure tcl t1 t2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs' with _ | ⟨rs''⟩
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
    have IH1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextLoc ≤ res'.nextLoc' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res1.nextLoc' ≤ r.nextLoc' := by
      exact applyFnTClosure_nextLoc_mono f ctx t1 t2 p poison1 etyp2 poison2 pred2 res1 r fuel' IH' happly
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
      _ ≤ res1.nextLoc' := IH1
      _ ≤ r.nextLoc' := h_r
      _ ≤ res.nextLoc' := h_r_le_res
  · rename_i st1 st2 p tcls
    rcases tcls with _ | ⟨f, fs'⟩ <;> simp at htc
    rcases hsub1 : isSubtype st1 _
      <;> rw [hsub1] at htc
      <;> simp at htc
    simp [bind, Except.bind] at htc
    rcases happly : applyPFnTClosure f st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _ with _ | ⟨r⟩
      <;> rw [happly] at htc
      <;> simp at htc
    rcases hcons :
        List.cons r <$>
          List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
        with _ | ⟨rs⟩
      <;> rw [hcons] at htc
      <;> simp at htc
    rcases hrs : rs with _ | ⟨r1, rs'⟩
      <;> rw [hrs] at htc
      <;> simp at htc
    subst rs
    simp [Functor.map, Except.map] at hcons
    rcases hmap :
        List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p poison1 etyp2 poison2 pred2 ctx res1 _) fs'
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
    have IH1 := IH fuel' h_fuel e1 ctx' res1 htce1'
    have IH' :
        ∀ m < fuel', ∀ (e : Expr) (ctx'' : TypeContext) (res' : TypeResult),
          typecheck ctx'' e m = .ok res' → ctx''.nextLoc ≤ res'.nextLoc' := by
      intro m hm e ctx'' res' htc'
      exact IH m (Nat.lt_trans hm h_fuel) e ctx'' res' htc'
    have h_r : res1.nextLoc' ≤ r.nextLoc' := by
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
                          regime := res1.regime',
                          memEnv := res1.memEnv',
                          varEnv :=
                            (VarTypeEnv.ofCaptured env).update x
                              { etyp := etyp2, poison := joinPoison ctx.pc poison2, pred := pred2 },
                          tagEnv := res1.tagEnv',
                          nextLoc := res1.nextLoc',
                          nextTag := res1.nextTag',
                          pureCtx := true } with hctx''
                      have htc_body' : typecheck ctx'' body.toExpr fuel'' = .ok r3 := by
                        simpa [typecheck, hctx''] using htc_body
                      have IH_body := IH' fuel'' (Nat.lt_succ_self fuel'') body.toExpr ctx'' r3 htc_body'
                      cases happly
                      simpa using IH_body
          | extern x retSpec capturedEnv =>
              simp [bind, Except.bind] at happly
              split at happly
              · -- simple case
                split at happly
                · simp at happly
                · split at happly
                  · simp at happly
                  · unfold returnSpecToQTyp at happly
                    split at happly
                    · simp at happly
                    · simp only [pure, Except.pure] at happly
                      injection happly with happly
                      cases happly
                      rename_i _v _heqRet
                      have hnl : _v.2 = res1.nextLoc' := by
                        have h : returnSpecToQTyp _ _ _ res1.nextLoc' = Except.ok _v := _heqRet
                        exact returnSpecToQTyp_preserves_nextLoc _ _ _ _ _ h
                      exact le_of_eq hnl.symm
              · -- nestedFn case
                simp only [pure, Except.pure] at happly
                injection happly with happly; cases happly; simp
              · -- nestedPfn case
                simp only [pure, Except.pure] at happly
                injection happly with happly; cases happly; simp
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
      _ ≤ res1.nextLoc' := IH1
      _ ≤ r.nextLoc' := h_r
      _ ≤ res.nextLoc' := h_r_le_res

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

private lemma TypeContext_nextLoc_with (ctx : TypeContext) (memEnv' : MemoryTypeEnv) :
  ({ ctx with nextLoc := ctx.nextLoc + 1, memEnv := memEnv' }).nextLoc = ctx.nextLoc + 1 := rfl

private lemma surfaceSpecToQTyp_nextLoc_mono
  (typ : Typ) (poison : Bool) (pred : Predicate)
  (ctx : TypeContext) (result : QTyp × TypeContext) :
  surfaceSpecToQTyp typ poison pred ctx = .ok result →
  ctx.nextLoc ≤ result.2.nextLoc := by
  intro h
  unfold surfaceSpecToQTyp at h
  cases typ with
  | int | bool | unit | string =>
      simp [bind, Except.bind, pure, Except.pure] at h
      have hs : result.2 = ctx := (congrArg Prod.snd h).symm
      simp [hs]
  | ref t =>
      cases t with
      | int =>
          simp [freshTLoc, bind, Except.bind, pure, Except.pure] at h
          cases h
          change ctx.nextLoc ≤ ctx.nextLoc + 1
          exact Nat.le_succ ctx.nextLoc
      | bool | unit | string | ref _ | arrow _ _ =>
          simp [bind, Except.bind] at h
  | arrow _ _ =>
      simp [bind, Except.bind] at h

-- Helper lemma for typecheckExternVal: nextLoc is monotone.
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
            simp only [typecheckExternVal] at htc
            simp [Bind.bind, Except.bind, pure, Except.pure] at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            cases htc
            rename_i _surf _heqSurf
            exact surfaceSpecToQTyp_nextLoc_mono _ _ _ _ _ _heqSurf
        | externFn arg argTyp retSpec effects =>
            simp only [typecheckExternFn, pure, Except.pure] at htc
            cases htc
            exact le_rfl
        | externPfn arg argTyp retSpec =>
            simp only [typecheckExternPfn, pure, Except.pure] at htc
            cases htc
            exact le_rfl
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

end typecheck_nextLoc_mono_proof

-- `nextLoc` is monotone for successful typechecking: typing never decreases the fresh-location supply.
-- This is analogous to typecheck_nextTag_mono but for memory locations.
lemma typecheck_nextLoc_mono (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
  typecheck ctx e fuel = .ok res →
  ctx.nextLoc ≤ res.nextLoc' := by
  intro htc
  exact typecheck_nextLoc_mono_main ctx e fuel res htc

-- ================================================================
-- wfTypeResult Preservation by Typechecker
-- ================================================================


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

/-- joinETyps preserves non-function property when BOTH args are non-function/non-ref. -/
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

/-- Helper: membership in the result of foldl-addUnique implies membership in acc or xs. -/
private lemma foldl_addUnique_mem_inv {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (acc : List α) (x : α) :
    x ∈ xs.foldl (fun acc' y => if acc'.contains y then acc' else acc' ++ [y]) acc →
    x ∈ acc ∨ x ∈ xs := by
  intro hmem
  induction xs generalizing acc with
  | nil =>
      simp at hmem
      exact Or.inl hmem
  | cons hd tl ih =>
      simp only [List.foldl_cons] at hmem
      by_cases hc : acc.contains hd
      · simp only [hc, ↓reduceIte] at hmem
        cases ih acc hmem with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (List.mem_cons_of_mem _ h)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
        cases ih (acc ++ [hd]) hmem with
        | inl h =>
            cases List.mem_append.mp h with
            | inl h => exact Or.inl h
            | inr h =>
                have := List.mem_singleton.mp h
                subst this
                exact Or.inr List.mem_cons_self
        | inr h =>
            exact Or.inr (List.mem_cons_of_mem _ h)

/-- Reverse direction: membership in mergeFnTClosures implies membership in one of the inputs. -/
lemma mem_mergeFnTClosures_inv (tcls1 tcls2 : List FnTClosure) (tcl : FnTClosure) :
    tcl ∈ mergeFnTClosures tcls1 tcls2 → tcl ∈ tcls1 ∨ tcl ∈ tcls2 := by
  intro hmem
  simp only [mergeFnTClosures] at hmem
  cases foldl_addUnique_mem_inv tcls2 _ tcl hmem with
  | inl h =>
      cases foldl_addUnique_mem_inv tcls1 [] tcl h with
      | inl h => exact absurd h List.not_mem_nil
      | inr h => exact Or.inl h
  | inr h => exact Or.inr h

/-- Reverse direction: membership in mergePFnTClosures implies membership in one of the inputs. -/
lemma mem_mergePFnTClosures_inv (tcls1 tcls2 : List PFnTClosure) (tcl : PFnTClosure) :
    tcl ∈ mergePFnTClosures tcls1 tcls2 → tcl ∈ tcls1 ∨ tcl ∈ tcls2 := by
  intro hmem
  simp only [mergePFnTClosures] at hmem
  cases foldl_addUnique_mem_inv tcls2 _ tcl hmem with
  | inl h =>
      cases foldl_addUnique_mem_inv tcls1 [] tcl h with
      | inl h => exact absurd h List.not_mem_nil
      | inr h => exact Or.inl h
  | inr h => exact Or.inr h

lemma valueHasETyp_joinETyps_left
  {θ : RealizationMap} {v : Value} {t1 t2 : ETyp} {p1 p2 : Poison}
  (hval : valueHasETyp θ v t1) :
  valueHasETyp θ v (joinETyps t1 t2 p1 p2) := by
  cases hval with
  | num n =>
      simpa [joinETyps] using (valueHasETyp.num n)
  | bool b =>
      simpa [joinETyps] using (valueHasETyp.bool b)
  | unit =>
      simpa [joinETyps] using (valueHasETyp.unit (θ := θ))
  | str s =>
      simpa [joinETyps] using (valueHasETyp.str (θ := θ) s)
  | loc hlookup hin =>
      rename_i a ls l
      cases t2 with
      | int =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
      | bool =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
      | unit =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
      | string =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
      | ref ls2 =>
          have hin_union : l ∈ LocSet.union ls ls2 := by simpa [LocSet.union] using Or.inl hin
          have hloc_union : valueHasETyp θ (Value.loc a) (ETyp.ref (LocSet.union ls ls2)) :=
            valueHasETyp.loc (hlookup := hlookup) (hin := hin_union)
          simpa [joinETyps] using hloc_union
      | arrow _st1 _st2 _p _tcls =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
      | parrow _st1 _st2 _p _tcls =>
          simpa [joinETyps] using (valueHasETyp.loc (θ := θ) (hlookup := hlookup) (hin := hin))
  | closure htcl henv hcover =>
      rename_i x e env st1 st2 p tcl tenv
      cases t2 with
      | int =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | bool =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | unit =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | string =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | ref _ls =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | arrow st1' st2' p' tcls2 =>
          by_cases hshape : st1 == st1' && st2 == st2'
          · have htcl_join :
              FnTClosure.regular x e tenv ∈ mergeFnTClosures tcl tcls2 :=
              mem_mergeFnTClosures_left tcl tcls2 _ htcl
            have hclo_join :
                valueHasETyp θ (Value.closure x e env)
                  (ETyp.arrow st1 st2 (joinPoison p p') (mergeFnTClosures tcl tcls2)) :=
              valueHasETyp.closure (htcl := htcl_join) (henv := henv) (hcover := hcover)
            simpa [joinETyps, hshape] using hclo_join
          · simpa [joinETyps, hshape] using
              (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
      | parrow _st1 _st2 _p _tcls =>
          simpa [joinETyps] using (valueHasETyp.closure (θ := θ) (htcl := htcl) (henv := henv) (hcover := hcover))
  | peClosure hpure htcl henv hcover =>
      rename_i x body env st1 st2 p tcl pbody tenv
      cases t2 with
      | int =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | bool =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | unit =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | string =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | ref _ls =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | arrow _st1 _st2 _p _tcls =>
          simpa [joinETyps] using (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))
      | parrow st1' st2' p' tcls2 =>
          by_cases hshape : st1 == st1' && st2 == st2'
          · have htcl_join :
              PFnTClosure.regular x pbody tenv ∈ mergePFnTClosures tcl tcls2 :=
              mem_mergePFnTClosures_left tcl tcls2 _ htcl
            have hpclo_join :
                valueHasETyp θ (Value.peClosure x body env)
                  (ETyp.parrow st1 st2 (joinPoison p p') (mergePFnTClosures tcl tcls2)) :=
              valueHasETyp.peClosure (hpure := hpure) (htcl := htcl_join) (henv := henv) (hcover := hcover)
            simpa [joinETyps, hshape] using hpclo_join
          · simpa [joinETyps, hshape] using
              (valueHasETyp.peClosure (θ := θ) (hpure := hpure) (htcl := htcl) (henv := henv) (hcover := hcover))

lemma valueHasETyp_joinETyps_right
  {θ : RealizationMap} {v : Value} {t1 t2 : ETyp} {p1 p2 : Poison}
  (hsig : beqETypSignature t1 t2 = true)
  (hval : valueHasETyp θ v t2) :
  valueHasETyp θ v (joinETyps t1 t2 p1 p2) := by
  cases hval with
  | num n =>
      cases t1 <;> simp [joinETyps, beqETypSignature] at hsig ⊢
      exact valueHasETyp.num n
  | bool b =>
      cases t1 <;> simp [joinETyps, beqETypSignature] at hsig ⊢
      exact valueHasETyp.bool b
  | unit =>
      cases t1 <;> simp [joinETyps, beqETypSignature] at hsig ⊢
      exact valueHasETyp.unit
  | str s =>
      cases t1 <;> simp [joinETyps, beqETypSignature] at hsig ⊢
      exact valueHasETyp.str s
  | loc hlookup hin =>
      rename_i a ls l
      cases t1 with
      | ref ls1 =>
          simp [beqETypSignature] at hsig
          simp [joinETyps]
          exact valueHasETyp.loc hlookup (by simp [LocSet.union]; exact Or.inr hin)
      | _ => simp [beqETypSignature] at hsig
  | closure htcl henv hcover =>
      rename_i x e env st1r st2r pr tclr tenvr
      cases t1 with
      | arrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hsig
          obtain ⟨rfl, rfl⟩ := hsig
          simp [joinETyps]
          exact valueHasETyp.closure
            (htcl := mem_mergeFnTClosures_right tclsl tclr _ htcl)
            (henv := henv) (hcover := hcover)
      | _ => simp [beqETypSignature] at hsig
  | peClosure hpure htcl henv hcover =>
      rename_i x body env st1r st2r pr tclr pbodyr tenvr
      cases t1 with
      | parrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hsig
          obtain ⟨rfl, rfl⟩ := hsig
          simp [joinETyps]
          exact valueHasETyp.peClosure hpure
            (htcl := mem_mergePFnTClosures_right tclsl tclr _ htcl)
            (henv := henv) (hcover := hcover)
      | _ => simp [beqETypSignature] at hsig

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

/-- joinETyps preserves beqETypSignature with the left operand: when t1 and t2 are compatible,
    joinETyps t1 t2 has the same signature as t1 for any third type. -/
lemma beqETypSignature_joinETyps_left {t1 t2 t3 : ETyp} {p1 p2 : Poison}
    (h : beqETypSignature t1 t2 = true) :
    beqETypSignature t1 t3 = beqETypSignature (joinETyps t1 t2 p1 p2) t3 := by
  cases t1 with
  | int => cases t2 <;> simp [joinETyps, beqETypSignature] at h ⊢
  | bool => cases t2 <;> simp [joinETyps, beqETypSignature] at h ⊢
  | unit => cases t2 <;> simp [joinETyps, beqETypSignature] at h ⊢
  | string => cases t2 <;> simp [joinETyps, beqETypSignature] at h ⊢
  | ref ls1 =>
      cases t2 with
      | ref ls2 =>
          simp only [beqETypSignature, joinETyps]
          cases t3 <;> rfl
      | _ => simp [beqETypSignature] at h
  | arrow st1 st2 p tcls =>
      cases t2 with
      | arrow st1' st2' _ _ =>
          simp only [beqETypSignature] at h
          by_cases heq : st1 == st1' && st2 == st2'
          · simp only [heq, joinETyps]
            cases t3 <;> rfl
          · simp [heq] at h
      | _ => simp [beqETypSignature] at h
  | parrow st1 st2 p tcls =>
      cases t2 with
      | parrow st1' st2' _ _ =>
          simp only [beqETypSignature] at h
          by_cases heq : st1 == st1' && st2 == st2'
          · simp only [heq, joinETyps]
            cases t3 <;> rfl
          · simp [heq] at h
      | _ => simp [beqETypSignature] at h

/-- joinETyps for ref types with compatible signatures produces a ref type. -/
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
        let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
          match oe1, oe2 with
          | some e1, none => some e1
          | none, some e2 => some e2
          | some e1, some e2 =>
            some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
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

/-- If a location is in the left env and not in the right, it is in the join. -/
lemma joinMemEnvs_contains_of_left (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1.contains l → env2[l]? = none → (joinMemEnvs env1 env2).contains l := by
  intro h1 h2
  have h1' : env1[l]? ≠ none := by
    intro heq
    have hnot_some : ¬Option.isSome (env1[l]?) := by simp [heq]
    have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
    exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.1 h1'
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
    have hkeys : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem
    have h_in' : l ∈ env1.keys ++ env2.keys := List.mem_append_left _ hkeys
    exact list_mem_eraseDups_of_mem h_in'
  classical
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo :=
    combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
  have hfun : f l (env1.get? l) (env2.get? l) = some entry := by
    simp only [ExtTreeMap.get?_eq_getElem?, hentry, h2, f]
  rw [hfun] at hgo
  simp at hgo
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?]
  conv_lhs => arg 1; arg 1; simp only [joinMemEnvs, combineExtTreeMaps]
  have heq : (combineExtTreeMaps.go env1 env2 (fun _ oe1 oe2 => match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none)
    (env1.keys ++ env2.keys).eraseDups ∅) =
    combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅ := by
    congr 2
  trans (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅)[l]?.isSome
  · exact congr_arg (fun m => m[l]?.isSome) heq
  · rw [hgo]
    rfl

/-- When `joinPredicates p q` returns a guardClosure, both inputs must be that guardClosure. -/
lemma joinPredicates_eq_guardClosure
  {p q : Predicate} {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv} :
  joinPredicates p q = Predicate.guardClosure k arg_name pred_body var_env →
  p = Predicate.guardClosure k arg_name pred_body var_env ∧
  q = Predicate.guardClosure k arg_name pred_body var_env := by
  intro h
  by_cases hbeq : beqPredicate p q = true
  · have hpq : p = q := eq_of_beq (a := p) (b := q) hbeq
    have hp : p = Predicate.guardClosure k arg_name pred_body var_env := by
      simpa [joinPredicates, hbeq] using h
    refine ⟨hp, ?_⟩
    simpa [hpq] using hp
  · have : False := by
      cases p with
      | noPred =>
          cases q <;> simp [joinPredicates, hbeq] at h
      | guardOnly k1 =>
          cases q with
          | noPred =>
              simp [joinPredicates, hbeq] at h
          | guardOnly k2 =>
              cases htag : (k1 == k2) <;> simp [joinPredicates, hbeq, htag] at h
          | guardClosure k2 a2 b2 env2 =>
              cases htag : (k1 == k2) <;> simp [joinPredicates, hbeq, htag] at h
      | guardClosure k1 a1 b1 env1 =>
          cases q with
          | noPred =>
              simp [joinPredicates, hbeq] at h
          | guardOnly k2 =>
              cases htag : (k1 == k2) <;> simp [joinPredicates, hbeq, htag] at h
          | guardClosure k2 a2 b2 env2 =>
              cases htag : (k1 == k2) <;> simp [joinPredicates, hbeq, htag] at h
    exact False.elim this

/-- If a left fold that only updates the predicate component via `joinPredicates`
ends at a `guardClosure`, then the initial predicate was already that `guardClosure`. -/
lemma fold_joinPred_guardClosure_init
    (env : MemoryTypeEnv) (xs : List Loc) (storedPoison : Poison) (storedPred : Predicate)
    {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv}
    (hfold :
      ((xs.foldl
          (fun acc l =>
            match env.get? l with
            | some qt => (joinPoison acc.1 qt.poison, joinPredicates acc.2 qt.pred)
            | none => acc)
          (storedPoison, storedPred)).2) =
        Predicate.guardClosure k arg_name pred_body var_env) :
    storedPred = Predicate.guardClosure k arg_name pred_body var_env := by
  induction xs generalizing storedPoison storedPred with
  | nil =>
      simpa using hfold
  | cons x xs ih =>
      simp [List.foldl] at hfold
      cases hget : env.get? x with
      | none =>
          have hget' : env[x]? = none := by
            simpa using hget
          have htail :
              ((xs.foldl
                  (fun acc l =>
                    match env.get? l with
                    | some qt => (joinPoison acc.1 qt.poison, joinPredicates acc.2 qt.pred)
                    | none => acc)
                  (storedPoison, storedPred)).2) =
                Predicate.guardClosure k arg_name pred_body var_env := by
            simpa [hget'] using hfold
          exact ih (storedPoison := storedPoison) (storedPred := storedPred) htail
      | some qt =>
          have hget' : env[x]? = some qt := by
            simpa using hget
          have hjoin :
              joinPredicates storedPred qt.pred =
                Predicate.guardClosure k arg_name pred_body var_env :=
            ih
              (storedPoison := joinPoison storedPoison qt.poison)
              (storedPred := joinPredicates storedPred qt.pred)
              (by simpa [hget'] using hfold)
          exact
            (joinPredicates_eq_guardClosure
              (p := storedPred) (q := qt.pred)
              (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env) hjoin).1

/-- When the right env has nothing at l, the join returns the left env's value. -/
lemma joinMemEnvs_lookup_eq_left_of_right_none (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1.contains l → env2[l]? = none → (joinMemEnvs env1 env2).lookup l = env1.lookup l := by
  intro h1 h2
  have h1' : env1[l]? ≠ none := by
    intro heq
    have hnot_some : ¬Option.isSome (env1[l]?) := by simp [heq]
    have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
    exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.1 h1'
  have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hkeys : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem
    exact list_mem_eraseDups_of_mem (List.mem_append_left _ hkeys)
  classical
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo := combineExtTreeMaps_go_get_mem env1 env2 f
    (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfun : f l (env1.get? l) (env2.get? l) = some entry := by
    simp only [ExtTreeMap.get?_eq_getElem?, hentry, h2, f]
  rw [hfun] at hgo
  simp at hgo
  simp only [joinMemEnvs, combineExtTreeMaps, MemoryTypeEnv.lookup]
  have heq : combineExtTreeMaps.go env1 env2 (fun _ oe1 oe2 => match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none) (env1.keys ++ env2.keys).eraseDups ∅ =
    combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅ := by
    congr 2
  calc (joinMemEnvs env1 env2).lookup l
    _ = ((joinMemEnvs env1 env2).get? l).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := rfl
    _ = ((combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅).get? l).map
        (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by
        rw [joinMemEnvs, combineExtTreeMaps]
        exact congr_arg (Option.map (fun (e : MemEntry) => (⟨ETyp.int, e.poison, e.pred⟩ : QTyp)))
          (congr_arg (·.get? l) heq)
    _ = (some entry).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by rw [ExtTreeMap.get?_eq_getElem?, hgo]
    _ = some ⟨ETyp.int, entry.poison, entry.pred⟩ := rfl
    _ = (env1.get? l).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by
        have hget : env1.get? l = some entry := by rw [ExtTreeMap.get?_eq_getElem?, hentry]
        rw [hget]; simp only [Option.map]
    _ = env1.lookup l := rfl

/-- When the left env has nothing at l, the join returns the right env's value. -/
lemma joinMemEnvs_lookup_eq_right_of_left_none (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1[l]? = none → env2.contains l → (joinMemEnvs env1 env2).lookup l = env2.lookup l := by
  intro h1 h2
  have hmem : l ∈ env2 := (Std.ExtTreeMap.contains_iff_mem).mp h2
  have h1' : env2[l]? ≠ none := by
    intro heq
    have hnot_some : ¬Option.isSome (env2[l]?) := by simp [heq]
    exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.1 h1'
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hkeys : l ∈ env2.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem
    exact list_mem_eraseDups_of_mem (List.mem_append_right _ hkeys)
  classical
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo := combineExtTreeMaps_go_get_mem env1 env2 f
    (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfun : f l (env1.get? l) (env2.get? l) = some entry := by
    simp only [ExtTreeMap.get?_eq_getElem?, h1, hentry, f]
  rw [hfun] at hgo
  simp at hgo
  simp only [joinMemEnvs, combineExtTreeMaps, MemoryTypeEnv.lookup]
  have heq : combineExtTreeMaps.go env1 env2 (fun _ oe1 oe2 => match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none) (env1.keys ++ env2.keys).eraseDups ∅ =
    combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅ := by
    congr 2
  calc (joinMemEnvs env1 env2).lookup l
    _ = ((joinMemEnvs env1 env2).get? l).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := rfl
    _ = ((combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅).get? l).map
        (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by
        rw [joinMemEnvs, combineExtTreeMaps]
        exact congr_arg (Option.map (fun (e : MemEntry) => (⟨ETyp.int, e.poison, e.pred⟩ : QTyp)))
          (congr_arg (·.get? l) heq)
    _ = (some entry).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by rw [ExtTreeMap.get?_eq_getElem?, hgo]
    _ = some ⟨ETyp.int, entry.poison, entry.pred⟩ := rfl
    _ = (env2.get? l).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by
        have hget : env2.get? l = some entry := by rw [ExtTreeMap.get?_eq_getElem?, hentry]
        rw [hget]; simp only [Option.map]
    _ = env2.lookup l := rfl

lemma memEnv_contains_of_lookup_some (env : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (hlookup : env.lookup l = some qt) : env.contains l := by
  have hget : env.get? l = some ⟨qt.poison, qt.pred⟩ := memEnv_get_eq_of_lookup env l qt hlookup
  exact (Std.ExtTreeMap.contains_iff_mem).2
    ((Std.ExtTreeMap.mem_iff_isSome_getElem?).2 (by rw [← Std.ExtTreeMap.get?_eq_getElem?, hget]; rfl))

lemma memEnv_lookup_some_of_contains (env : MemoryTypeEnv) (l : Loc)
  (hcontains : env.contains l) : ∃ qt, env.lookup l = some qt := by
  have hmem : l ∈ env := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
  have hsome : Option.isSome env[l]? := (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
  rcases Option.isSome_iff_exists.mp hsome with ⟨entry, hentry⟩
  refine ⟨⟨ETyp.int, entry.poison, entry.pred⟩, ?_⟩
  simp [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, hentry]

lemma joinMemEnvs_lookup_some_of_left_lookup (env1 env2 : MemoryTypeEnv) (l : Loc) (qt1 : QTyp)
  (hlookup1 : env1.lookup l = some qt1) : ∃ qt, (joinMemEnvs env1 env2).lookup l = some qt := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    refine ⟨qt1, ?_⟩
    have hjoin := joinMemEnvs_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    simpa [hlookup1] using hjoin
  · have hlookup2_some : env2.lookup l ≠ none := hlookup2_none
    rcases Option.ne_none_iff_exists'.1 hlookup2_some with ⟨qt2, hlookup2⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have ht12 : t1 = t2 := by simpa using hetyp_eq
            have hfun : f l (env1.get? l) (env2.get? l) =
              some ⟨joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
              rw [he1, he2]
            rw [hfun] at hgo
            simp at hgo
            have heq : joinMemEnvs env1 env2 = combineExtTreeMaps env1 env2 f := by
              simp only [joinMemEnvs, combineExtTreeMaps]; congr 2
            refine ⟨⟨ETyp.int, joinPoison p1 p2, joinPredicates pred1 pred2⟩, ?_⟩
            rw [heq]
            simp only [MemoryTypeEnv.lookup, combineExtTreeMaps, ExtTreeMap.get?_eq_getElem?,
              Option.map, hgo]

lemma joinMemEnvs_lookup_some_of_right_lookup (env1 env2 : MemoryTypeEnv) (l : Loc) (qt2 : QTyp)
  (hlookup2 : env2.lookup l = some qt2) : ∃ qt, (joinMemEnvs env1 env2).lookup l = some qt := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    refine ⟨qt2, ?_⟩
    have hjoin := joinMemEnvs_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    simpa [hlookup2] using hjoin
  · have hlookup1_some : env1.lookup l ≠ none := hlookup1_none
    rcases Option.ne_none_iff_exists'.1 hlookup1_some with ⟨qt1, hlookup1⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have ht12 : t1 = t2 := by simpa using hetyp_eq
            have hfun : f l (env1.get? l) (env2.get? l) =
              some ⟨joinPoison p1 p2, joinPredicates pred1 pred2⟩ := by
              rw [he1, he2]
            rw [hfun] at hgo
            simp at hgo
            have heq : joinMemEnvs env1 env2 = combineExtTreeMaps env1 env2 f := by
              simp only [joinMemEnvs, combineExtTreeMaps]; congr 2
            refine ⟨⟨ETyp.int, joinPoison p1 p2, joinPredicates pred1 pred2⟩, ?_⟩
            rw [heq]
            simp only [MemoryTypeEnv.lookup, combineExtTreeMaps, ExtTreeMap.get?_eq_getElem?,
              Option.map, hgo]

lemma joinMemEnvs_lookup_guardTag_left (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp) (k : Tag)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (htag_join : qtypGuardTag qt = some k) :
  qtypGuardTag qt1 = some k := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hjoin_eq_left := joinMemEnvs_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    have hqt_eq : qt1 = qt := by
      have hqeq_opt : some qt = some qt1 := by
        calc some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env1.lookup l := hjoin_eq_left
          _ = some qt1 := hlookup1
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using htag_join
  · have hlookup2_some : env2.lookup l ≠ none := hlookup2_none
    rcases Option.ne_none_iff_exists'.1 hlookup2_some with ⟨qt2, hlookup2⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have ht12 : t1 = t2 := by simpa using hetyp_eq
            have hjoin_lookup_get :
              (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
              some ⟨qt.poison, qt.pred⟩ := by
              have hget := memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
              simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hget
            have hmatch : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) = some ⟨qt.poison, qt.pred⟩ := by
              have hgo' := hgo
              rw [Std.ExtTreeMap.get?_eq_getElem?] at hgo'
              have h : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) := by
                cases hopt : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) with
                | none => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
                | some v => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
              rw [← h]; exact hjoin_lookup_get
            have hqt_pred : qt.pred = joinPredicates pred1 pred2 := by
              rw [he1, he2] at hmatch
              simp only [f] at hmatch
              exact (MemEntry.mk.inj (Option.some.inj hmatch.symm)).2
            have hsplit := joinPredicates_guardTag_eq_some_implies_left_right (p := pred1) (q := pred2) (k := k)
              (by simpa [qtypGuardTag, hqt_pred] using htag_join)
            simpa [qtypGuardTag] using hsplit.1

lemma joinMemEnvs_lookup_guardTag_right (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp) (k : Tag)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (htag_join : qtypGuardTag qt = some k) :
  qtypGuardTag qt2 = some k := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hjoin_eq_right := joinMemEnvs_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    have hqt_eq : qt2 = qt := by
      have hqeq_opt : some qt = some qt2 := by
        calc some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env2.lookup l := hjoin_eq_right
          _ = some qt2 := hlookup2
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using htag_join
  · have hlookup1_some : env1.lookup l ≠ none := hlookup1_none
    rcases Option.ne_none_iff_exists'.1 hlookup1_some with ⟨qt1, hlookup1⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have ht12 : t1 = t2 := by simpa using hetyp_eq
            have hjoin_lookup_get :
              (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
              some ⟨qt.poison, qt.pred⟩ := by
              have hget := memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
              simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hget
            have hmatch : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) = some ⟨qt.poison, qt.pred⟩ := by
              have hgo' := hgo
              rw [Std.ExtTreeMap.get?_eq_getElem?] at hgo'
              have h : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) := by
                cases hopt : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) with
                | none => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
                | some v => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
              rw [← h]; exact hjoin_lookup_get
            have hqt_pred : qt.pred = joinPredicates pred1 pred2 := by
              rw [he1, he2] at hmatch
              simp only [f] at hmatch
              exact (MemEntry.mk.inj (Option.some.inj hmatch.symm)).2
            have hsplit := joinPredicates_guardTag_eq_some_implies_left_right (p := pred1) (q := pred2) (k := k)
              (by simpa [qtypGuardTag, hqt_pred] using htag_join)
            simpa [qtypGuardTag] using hsplit.2

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
      let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
        match oe1, oe2 with
        | some e1, none => some e1
        | none, some e2 => some e2
        | some e1, some e2 =>
          some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
        | none, none => none
      have hqt_eq : qt = ⟨ETyp.int, qt.poison, qt.pred⟩ := memEnv_lookup_toQTyp (joinMemEnvs env1 env2) l qt (by rw [hjoin])
      have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
        memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hjoin
      have hjoin' :
          (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      by_cases h_in : l ∈ (env1.keys ++ env2.keys).eraseDups
      · have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
        have h1' : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 h1
        have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
            f l (env1.get? l) (env2.get? l) := by
          cases hopt : f l (env1.get? l) (env2.get? l) with
          | none => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
          | some v => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
        have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by rw [← h_go_eq_f]; exact hjoin'
        have htp : qt1.etyp = qt.etyp ∧ qt1.poison = false := by
          cases h2 : env2.get? l with
          | none =>
              rw [h1', h2] at hmatch
              simp [f] at hmatch
              have heq := hmatch.1
              exact ⟨by rw [memEnv_lookup_etyp_int env1 l qt1 h1, hqt_eq], by rw [heq]; exact hclean⟩
          | some e2 =>
              rw [h1', h2] at hmatch
              simp [f] at hmatch
              have heq := hmatch.1
              have hpo : joinPoison qt1.poison e2.poison = false := by rw [heq]; exact hclean
              have hp1 : qt1.poison = false := ((Bool.or_eq_false_iff).1 (by simpa [joinPoison] using hpo)).1
              exact ⟨by rw [memEnv_lookup_etyp_int env1 l qt1 h1, hqt_eq], hp1⟩
        refine ⟨qt1, ⟨rfl, ⟨htp.1, htp.2⟩⟩⟩
      · have hgo := combineExtTreeMaps_go_get_not_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
        have hempty : (({} : MemoryTypeEnv)[l]?) = none := rfl
        rw [hempty] at hgo
        rw [hjoin'] at hgo
        exact Option.noConfusion hgo

/-- Symmetric companion of `joinMemEnvs_lookup_clean_left` for the right input. -/
lemma joinMemEnvs_lookup_clean_right (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (joinMemEnvs env1 env2).lookup l = some qt →
  qt.poison = false →
  env2.lookup l ≠ none →
  ∃ qt2, env2.lookup l = some qt2 ∧ qt2.etyp = qt.etyp ∧ qt2.poison = false := by
  intro hjoin hclean henv2
  classical
  cases h2 : env2.lookup l with
  | none =>
      exact (henv2 h2).elim
  | some qt2 =>
      let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
        match oe1, oe2 with
        | some e1, none => some e1
        | none, some e2 => some e2
        | some e1, some e2 =>
          some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
        | none, none => none
      have hqt_eq : qt = ⟨ETyp.int, qt.poison, qt.pred⟩ := memEnv_lookup_toQTyp (joinMemEnvs env1 env2) l qt (by rw [hjoin])
      have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
        memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hjoin
      have hjoin' :
          (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      by_cases h_in : l ∈ (env1.keys ++ env2.keys).eraseDups
      · have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
        have h2' : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 h2
        have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
            f l (env1.get? l) (env2.get? l) := by
          cases hopt : f l (env1.get? l) (env2.get? l) with
          | none => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
          | some v => have hgo'' := hgo; rw [hopt] at hgo''; exact hgo''
        have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by rw [← h_go_eq_f]; exact hjoin'
        have htp : qt2.etyp = qt.etyp ∧ qt2.poison = false := by
          cases h1 : env1.get? l with
          | none =>
              rw [h1, h2'] at hmatch
              simp [f] at hmatch
              have heq := hmatch.1
              exact ⟨by rw [memEnv_lookup_etyp_int env2 l qt2 h2, hqt_eq], by rw [heq]; exact hclean⟩
          | some e1 =>
              rw [h1, h2'] at hmatch
              simp [f] at hmatch
              have heq := hmatch.1
              have hpo : joinPoison e1.poison qt2.poison = false := by rw [heq]; exact hclean
              have hp2 : qt2.poison = false := ((Bool.or_eq_false_iff).1 (by simpa [joinPoison] using hpo)).2
              exact ⟨by rw [memEnv_lookup_etyp_int env2 l qt2 h2, hqt_eq], hp2⟩
        refine ⟨qt2, ⟨rfl, ⟨htp.1, htp.2⟩⟩⟩
      · have hgo := combineExtTreeMaps_go_get_not_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
        have hempty : (({} : MemoryTypeEnv)[l]?) = none := rfl
        rw [hempty] at hgo
        rw [hjoin'] at hgo
        exact Option.noConfusion hgo

/-- wfTypeContext property is preserved under joinMemEnvs with max nextLoc. -/
lemma typecheckVar_preserves_memEnv (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.memEnv' = ctx.memEnv := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck <;>
    (repeat (first | split at h_typecheck | simp [pure, Except.pure, throw] at h_typecheck | cases h_typecheck | rfl))

lemma typecheckVar_preserves_tagEnv (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.tagEnv' = ctx.tagEnv := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck <;>
    (repeat (first | split at h_typecheck | simp [pure, Except.pure, throw] at h_typecheck | cases h_typecheck | rfl))

lemma typecheckVar_preserves_nextLoc (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.nextLoc' = ctx.nextLoc := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck <;>
    (repeat (first | split at h_typecheck | simp [pure, Except.pure, throw] at h_typecheck | cases h_typecheck | rfl))

lemma typecheckVar_preserves_regime (ctx : TypeContext) (x : Name) (res : TypeResult) :
  typecheckVar ctx x = .ok res →
  res.regime' = ctx.regime := by
  intro h_typecheck
  simp [typecheckVar] at h_typecheck
  split at h_typecheck <;>
    (repeat (first | split at h_typecheck | simp [pure, Except.pure, throw] at h_typecheck | cases h_typecheck | rfl))

-- When typecheckVar succeeds, the variable is in the context and its value has the result's etyp

lemma joinMemEnvsStrong_contains_implies_or
    (env1 env2 : MemoryTypeEnv) (l : Loc) :
    (joinMemEnvsStrong env1 env2).contains l → env1.contains l ∨ env2.contains l := by
  intro hcontains
  by_cases h1 : env1.contains l = true
  · left
    exact h1
  · by_cases h2 : env2.contains l = true
    · right
      exact h2
    · exfalso
      have h1not : l ∉ env1 := (Std.ExtTreeMap.contains_iff_mem).not.1 h1
      have h2not : l ∉ env2 := (Std.ExtTreeMap.contains_iff_mem).not.1 h2
      have h1_none : env1[l]? = none := Std.ExtTreeMap.getElem?_eq_none h1not
      have h2_none : env2[l]? = none := Std.ExtTreeMap.getElem?_eq_none h2not
      have hjoin_none : (joinMemEnvsStrong env1 env2)[l]? = none := by
        classical
        let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
          match oe1, oe2 with
          | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
          | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
          | some e1, some e2 =>
            some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
          | none, none => none
        dsimp [joinMemEnvsStrong, f, combineExtTreeMaps]
        change
          (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv))[l]? = none
        by_cases h_in : l ∈ (env1.keys ++ env2.keys).eraseDups
        · have hgo :=
            combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv) l h_in
          have hfun : f l (env1.get? l) (env2.get? l) = none := by
            simp [ExtTreeMap.get?_eq_getElem?, h1_none, h2_none, f]
          rw [hfun] at hgo
          exact hgo
        · have hgo :=
            combineExtTreeMaps_go_get_not_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
              ({} : MemoryTypeEnv) l h_in
          have hempty : (({} : MemoryTypeEnv)[l]?) = none := by
            rfl
          rw [hempty] at hgo
          exact hgo
      have hmem : l ∈ joinMemEnvsStrong env1 env2 := (Std.ExtTreeMap.contains_iff_mem).1 hcontains
      have hsome : Option.isSome (joinMemEnvsStrong env1 env2)[l]? :=
        (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
      simp [hjoin_none] at hsome

lemma joinMemEnvsStrong_lookup_eq_left_of_right_none (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1.contains l → env2[l]? = none →
  (joinMemEnvsStrong env1 env2).lookup l =
  match env1.lookup l with
  | some qt1 => some ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩
  | none => none := by
  intro h1 h2
  have h1' : env1[l]? ≠ none := by
    intro heq
    have hnot_some : ¬Option.isSome (env1[l]?) := by simp [heq]
    have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
    exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.1 h1'
  have hmem : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).mp h1
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hkeys : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys)
  classical
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
    | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo := combineExtTreeMaps_go_get_mem env1 env2 f
    (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfun : f l (env1.get? l) (env2.get? l) = some ⟨entry.poison, Predicate.noPred⟩ := by
    simp only [ExtTreeMap.get?_eq_getElem?, hentry, h2, f]
  rw [hfun] at hgo
  simp at hgo
  have hlookup1 : env1.lookup l = some ⟨ETyp.int, entry.poison, entry.pred⟩ := by
    simp only [MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, hentry]; rfl
  simp only [joinMemEnvsStrong, combineExtTreeMaps, MemoryTypeEnv.lookup]
  calc (joinMemEnvsStrong env1 env2).lookup l
    _ = ((combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅).get? l).map
        (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := rfl
    _ = (some (⟨entry.poison, Predicate.noPred⟩ : MemEntry)).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by rw [ExtTreeMap.get?_eq_getElem?, hgo]
    _ = some ⟨ETyp.int, entry.poison, Predicate.noPred⟩ := rfl
    _ = match env1.lookup l with
        | some qt1 => some ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩
        | none => none := by rw [hlookup1]

lemma joinMemEnvsStrong_lookup_eq_right_of_left_none (env1 env2 : MemoryTypeEnv) (l : Loc) :
  env1[l]? = none → env2.contains l →
  (joinMemEnvsStrong env1 env2).lookup l =
  match env2.lookup l with
  | some qt2 => some ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩
  | none => none := by
  intro h1 h2
  have hmem : l ∈ env2 := (Std.ExtTreeMap.contains_iff_mem).mp h2
  have h2' : env2[l]? ≠ none := by
    intro heq
    have hnot_some : ¬Option.isSome (env2[l]?) := by simp [heq]
    exact hnot_some ((Std.ExtTreeMap.mem_iff_isSome_getElem?).mp hmem)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.1 h2'
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hkeys : l ∈ env2.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem
    exact List.mem_eraseDups_of_mem (List.mem_append_right _ hkeys)
  classical
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
    | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo := combineExtTreeMaps_go_get_mem env1 env2 f
    (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfun : f l (env1.get? l) (env2.get? l) = some ⟨entry.poison, Predicate.noPred⟩ := by
    simp only [ExtTreeMap.get?_eq_getElem?, h1, hentry, f]
  rw [hfun] at hgo
  simp at hgo
  have hlookup2 : env2.lookup l = some ⟨ETyp.int, entry.poison, entry.pred⟩ := by
    simp only [MemoryTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, hentry]; rfl
  simp only [joinMemEnvsStrong, combineExtTreeMaps, MemoryTypeEnv.lookup]
  calc (joinMemEnvsStrong env1 env2).lookup l
    _ = ((combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ∅).get? l).map
        (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := rfl
    _ = (some (⟨entry.poison, Predicate.noPred⟩ : MemEntry)).map (fun e => ⟨ETyp.int, e.poison, e.pred⟩) := by rw [Std.ExtTreeMap.get?_eq_getElem?, hgo]
    _ = some ⟨ETyp.int, entry.poison, Predicate.noPred⟩ := rfl
    _ = match env2.lookup l with
        | some qt2 => some ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩
        | none => none := by rw [hlookup2]

lemma joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup (env1 env2 : MemoryTypeEnv) (l : Loc) (qt1 qt2 : QTyp)
  (hlookup1 : env1.lookup l = some qt1)
  (hlookup2 : env2.lookup l = some qt2) :
  (joinMemEnvsStrong env1 env2).lookup l = (joinMemEnvs env1 env2).lookup l := by
  have hget1 : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
  have hget2 : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
  have hmem1 : l ∈ env1 := (Std.ExtTreeMap.contains_iff_mem).1 (memEnv_contains_of_lookup_some env1 l qt1 hlookup1)
  have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
  classical
  let fW : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  let fS : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
    | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgoW := combineExtTreeMaps_go_get_mem env1 env2 fW (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hgoS := combineExtTreeMaps_go_get_mem env1 env2 fS (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_in
  have hfunEq : fS l (env1.get? l) (env2.get? l) = fW l (env1.get? l) (env2.get? l) := by
    rw [hget1, hget2]
  rw [hfunEq] at hgoS
  have h_eq_go :
      (combineExtTreeMaps.go env1 env2 fS (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
      (combineExtTreeMaps.go env1 env2 fW (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? := by
    exact hgoS.trans hgoW.symm
  have heqS : combineExtTreeMaps env1 env2 fS = joinMemEnvsStrong env1 env2 := by simp only [joinMemEnvsStrong]; congr 2
  have heqW : combineExtTreeMaps env1 env2 fW = joinMemEnvs env1 env2 := by simp only [joinMemEnvs]; congr 2
  rw [← heqS, ← heqW]
  simp only [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?, combineExtTreeMaps]
  refine congr_arg (Option.map (fun (e : MemEntry) => (⟨ETyp.int, e.poison, e.pred⟩ : QTyp))) h_eq_go

lemma joinMemEnvsStrong_lookup_some_of_left_lookup (env1 env2 : MemoryTypeEnv) (l : Loc) (qt1 : QTyp)
  (hlookup1 : env1.lookup l = some qt1) : ∃ qt, (joinMemEnvsStrong env1 env2).lookup l = some qt := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    refine ⟨⟨qt1.etyp, qt1.poison, Predicate.noPred⟩, ?_⟩
    simpa [hlookup1] using joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
  · have hlookup2_some : env2.lookup l ≠ none := hlookup2_none
    rcases Option.ne_none_iff_exists'.1 hlookup2_some with ⟨qt2, hlookup2⟩
    rcases joinMemEnvs_lookup_some_of_left_lookup env1 env2 l qt1 hlookup1 with ⟨qt, hlookupW⟩
    refine ⟨qt, ?_⟩
    rw [joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
    exact hlookupW

lemma joinMemEnvsStrong_lookup_some_of_right_lookup (env1 env2 : MemoryTypeEnv) (l : Loc) (qt2 : QTyp)
  (hlookup2 : env2.lookup l = some qt2) : ∃ qt, (joinMemEnvsStrong env1 env2).lookup l = some qt := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    refine ⟨⟨qt2.etyp, qt2.poison, Predicate.noPred⟩, ?_⟩
    simpa [hlookup2] using joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
  · have hlookup1_some : env1.lookup l ≠ none := hlookup1_none
    rcases Option.ne_none_iff_exists'.1 hlookup1_some with ⟨qt1, hlookup1⟩
    rcases joinMemEnvs_lookup_some_of_right_lookup env1 env2 l qt2 hlookup2 with ⟨qt, hlookupW⟩
    refine ⟨qt, ?_⟩
    rw [joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
    exact hlookupW

lemma joinMemEnvsStrong_lookup_guardTag_left (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp) (k : Tag)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (htag_join : qtypGuardTag qt = some k) :
  qtypGuardTag qt1 = some k := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hleft := joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    rw [hlookup_join] at hleft
    have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by simpa [hlookup1] using hleft
    have : False := by simp [hq, qtypGuardTag] at htag_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact joinMemEnvs_lookup_guardTag_left env1 env2 l qt qt1 k hlookupW hlookup1 htag_join

lemma joinMemEnvsStrong_lookup_guardTag_right (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp) (k : Tag)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (htag_join : qtypGuardTag qt = some k) :
  qtypGuardTag qt2 = some k := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hright := joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    rw [hlookup_join] at hright
    have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by simpa [hlookup2] using hright
    have : False := by simp [hq, qtypGuardTag] at htag_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup1_none with ⟨qt1, hlookup1⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact joinMemEnvs_lookup_guardTag_right env1 env2 l qt qt2 k hlookupW hlookup2 htag_join

lemma joinMemEnvsStrong_lookup_clean_left (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (joinMemEnvsStrong env1 env2).lookup l = some qt →
  qt.poison = false →
  env1.lookup l ≠ none →
  ∃ qt1, env1.lookup l = some qt1 ∧ qt1.etyp = qt.etyp ∧ qt1.poison = false := by
  intro hjoin hclean henv1
  by_cases h2none : env2.lookup l = none
  · cases h1 : env1.lookup l with
    | none => exact (henv1 h1).elim
    | some qt1 =>
        have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 h1
        have h2none_get : env2[l]? = none := by
          simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h2none
        have hleft := joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 h2none_get
        rw [h1] at hleft
        rw [hjoin] at hleft
        have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by simpa using hleft
        have hclean' := hclean
        simp [hq] at hclean'
        exact ⟨qt1, ⟨by simp, ⟨by simp [hq], hclean'⟩⟩⟩
  · rcases Option.ne_none_iff_exists'.1 h2none with ⟨qt2, h2⟩
    rcases Option.ne_none_iff_exists'.1 henv1 with ⟨qt1, h1⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 h1 h2]
      exact hjoin
    exact joinMemEnvs_lookup_clean_left env1 env2 l qt hlookupW hclean henv1

lemma joinMemEnvsStrong_lookup_clean_right (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp) :
  (joinMemEnvsStrong env1 env2).lookup l = some qt →
  qt.poison = false →
  env2.lookup l ≠ none →
  ∃ qt2, env2.lookup l = some qt2 ∧ qt2.etyp = qt.etyp ∧ qt2.poison = false := by
  intro hjoin hclean henv2
  by_cases h1none : env1.lookup l = none
  · cases h2 : env2.lookup l with
    | none => exact (henv2 h2).elim
    | some qt2 =>
        have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 h2
        have h1none_get : env1[l]? = none := by
          simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h1none
        have hright := joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l h1none_get hcontains2
        rw [h2] at hright
        rw [hjoin] at hright
        have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by simpa using hright
        have hclean' := hclean
        simp [hq] at hclean'
        exact ⟨qt2, ⟨by simp, ⟨by simp [hq], hclean'⟩⟩⟩
  · rcases Option.ne_none_iff_exists'.1 h1none with ⟨qt1, h1⟩
    rcases Option.ne_none_iff_exists'.1 henv2 with ⟨qt2, h2⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 h1 h2]
      exact hjoin
    exact joinMemEnvs_lookup_clean_right env1 env2 l qt hlookupW hclean henv2

-- When the compat fold returns ok, all elements of rest are signature-compatible with etyp.
lemma joinTypeResults_compat_ok (etyp : ETyp) (rest : List TypeResult)
  (hcheck : List.foldlM (fun _ result =>
    match result.qualType with
    | { etyp := resEtyp, poison := _, pred := _ } =>
        if beqETypSignature etyp resEtyp = false then
          Except.error (toString "Closure alternatives produced incompatible result types: " ++
            toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
        else Except.ok ()) () rest = .ok ()) :
  ∀ r ∈ rest, beqETypSignature etyp r.qualType.etyp = true := by
  intro r hr
  induction rest with
  | nil => simp at hr
  | cons x xs ih =>
      rw [List.foldlM_cons] at hcheck
      simp only [bind, Except.bind] at hcheck
      cases hqx : x.qualType with
      | mk resEtyp _ _ =>
          simp only [hqx] at hcheck
          by_cases h : beqETypSignature etyp resEtyp = false
          · simp only [h] at hcheck; cases hcheck
          · simp only [h] at hcheck
            cases hr with
            | head => simpa [hqx] using h
            | tail _ htail => exact ih hcheck htail

lemma joinTypeResults_mem_contains_head_or_rest
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res) :
  ∀ l, res.memEnv'.contains l → first.memEnv'.contains l ∨ ∃ r ∈ rest, r.memEnv'.contains l := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_contains :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ l, acc'.2.1.contains l → acc.2.1.contains l ∨ ∃ r ∈ rs', r.memEnv'.contains l := by
    intro rs' acc acc' hfold
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        intro l hcontains
        exact Or.inl hcontains
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            intro l hcontains
            rcases ih (acc := acc1) hfold_tail l hcontains with hacc1 | htail
            · have hor : acc.2.1.contains l ∨ x.memEnv'.contains l := by
                by_cases h1 : acc.2.1.contains l = true
                · exact Or.inl h1
                · by_cases h2 : x.memEnv'.contains l = true
                  · exact Or.inr h2
                  · exfalso
                    have h1not : l ∉ acc.2.1 := (Std.ExtTreeMap.contains_iff_mem).not.1 h1
                    have h2not : l ∉ x.memEnv' := (Std.ExtTreeMap.contains_iff_mem).not.1 h2
                    have h1_none : acc.2.1[l]? = none := Std.ExtTreeMap.getElem?_eq_none h1not
                    have h2_none : x.memEnv'[l]? = none := Std.ExtTreeMap.getElem?_eq_none h2not
                    have hjoin_none : (joinMemEnvsStrong acc.2.1 x.memEnv')[l]? = none := by
                      classical
                      let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
                        match oe1, oe2 with
                        | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
                        | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
                        | some e1, some e2 =>
                          some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
                        | none, none => none
                      have heq : combineExtTreeMaps acc.2.1 x.memEnv' f = joinMemEnvsStrong acc.2.1 x.memEnv' := by
                        simp only [joinMemEnvsStrong]; congr 2
                      rw [← heq]
                      dsimp [combineExtTreeMaps]
                      by_cases h_in : l ∈ (acc.2.1.keys ++ x.memEnv'.keys).eraseDups
                      · have hgo :=
                          combineExtTreeMaps_go_get_mem acc.2.1 x.memEnv' f (acc.2.1.keys ++ x.memEnv'.keys).eraseDups
                            ({} : MemoryTypeEnv) l h_in
                        have hfun : f l (acc.2.1.get? l) (x.memEnv'.get? l) = none := by
                          simp [ExtTreeMap.get?_eq_getElem?, h1_none, h2_none, f]
                        rw [hfun] at hgo
                        exact hgo
                      · have hgo :=
                          combineExtTreeMaps_go_get_not_mem acc.2.1 x.memEnv' f (acc.2.1.keys ++ x.memEnv'.keys).eraseDups
                            ({} : MemoryTypeEnv) l h_in
                        have hempty : (({} : MemoryTypeEnv)[l]?) = none := by rfl
                        rw [hempty] at hgo
                        exact hgo
                    have hmem : l ∈ joinMemEnvsStrong acc.2.1 x.memEnv' := (Std.ExtTreeMap.contains_iff_mem).1 hacc1
                    have hsome : Option.isSome (joinMemEnvsStrong acc.2.1 x.memEnv')[l]? :=
                      (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                    simp [hjoin_none] at hsome
              cases hor with
              | inl hacc =>
                  exact Or.inl hacc
              | inr hx =>
                  exact Or.inr ⟨x, by simp, hx⟩
            · rcases htail with ⟨r, hr, hrcontains⟩
              exact Or.inr ⟨r, by simp [hr], hrcontains⟩
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
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
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              intro l hcontains
              exact
                h_fold_contains rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a
                  hfold l (by simpa using hcontains)


-- If the input context is well-formed (all tracked locations are below nextLoc),
-- then successful typechecking produces a well-formed result (same invariant).
-- This is purely a static bookkeeping property with no runtime semantics.

section wfTypeResult_preservation

/-- restrictMemEnv contains only keys from the base env -/
private lemma restrictMemEnv_contains_implies_base (env base : MemoryTypeEnv) (l : Loc) :
    (restrictMemEnv env base).contains l = true → base.contains l = true := by
  intro h
  by_contra h_neg
  simp at h_neg
  have h_mem : l ∈ restrictMemEnv env base := Std.ExtTreeMap.contains_iff_mem.mp h
  rw [restrictMemEnv] at h_mem
  rw [Std.ExtTreeMap.mem_filter] at h_mem
  rcases h_mem with ⟨_, h_base⟩
  simp at h_base
  exact h_neg h_base

/-- LocSet.fold for nextLoc computation is ≥ initial value -/
private lemma locset_fold_max_ge_init (ls : LocSet) (n : Nat) :
    n ≤ LocSet.fold ls n (fun acc l => max acc (l + 1)) := by
  unfold LocSet.fold; rw [ExtTreeSet.foldl_eq_foldl_toList]
  induction ls.toList generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left n (x + 1)) (ih (max n (x + 1)))

/-- typecheckNewRef preserves wfTypeResult -/
private lemma typecheckNewRef_wfTypeResult
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckNewRef ctx e fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => unfold typecheckNewRef at htc; simp at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckNewRef_structure ctx e fuel'.succ res htc
    rcases hstruct with ⟨result1, l, htc1, hl, _, _, _, _, hmem, _, hnextloc, _, _⟩
    have htc1' : typecheck ctx e fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e ctx result1 hwf htc1'
    intro l' hcontains
    rw [hmem] at hcontains
    have hor := updateMemEnv_contains_eq_or_old result1.memEnv' l l' _ hcontains
    rw [hnextloc]
    cases hor with
    | inl hEq => rw [hEq, hl]; exact Nat.lt_succ_self result1.nextLoc'
    | inr hOld => exact Nat.lt_of_lt_of_le (hwf1 l' hOld) (Nat.le_succ _)

/-- typecheckAssign preserves wfTypeResult -/
private lemma typecheckAssign_wfTypeResult
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckAssign ctx e1 e2 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => unfold typecheckAssign at htc; simp at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    unfold typecheckAssign at htc
    simp only [bind, Except.bind] at htc
    cases h_tc1 : typecheckExpr ctx e1 fuel' with
    | error _ => simp [h_tc1] at htc
    | ok result1 =>
      simp only [h_tc1] at htc
      have htc1' : typecheck ctx e1 fuel' = .ok result1 := by simpa using h_tc1
      have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e1 ctx result1 hwf htc1'
      cases h_qt1 : result1.qualType with
      | mk etyp1 p1 pred1 =>
        rw [h_qt1] at htc; simp at htc
        cases etyp1 with
        | ref ls =>
          simp at htc
          set ctx2 : TypeContext := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', regime := result1.regime' }
          have hwf2_ctx : wfTypeContext ctx2 := wfTypeContext_of_wfTypeResult ctx result1 hwf1
          cases h_tc2 : typecheckExpr ctx2 e2 fuel' with
          | error _ => simp [h_tc2] at htc
          | ok result2 =>
            simp only [h_tc2] at htc
            have htc2' : typecheck ctx2 e2 fuel' = .ok result2 := by simpa using h_tc2
            have hwf2 : wfTypeResult result2 := IH fuel' h_fuel e2 ctx2 result2 hwf2_ctx htc2'
            cases h_qt2 : result2.qualType with
            | mk etyp2 p2 pred2 =>
              rw [h_qt2] at htc; simp at htc
              by_cases h_etyp2_int : etyp2 = ETyp.int
              · subst h_etyp2_int; simp at htc; cases htc
                intro l' hcontains
                have hor := assign_memEnv_formula_contains_eq_or_mem result2.memEnv' ls
                  (joinPoison ctx.pc (joinPoison p1 p2))
                  (if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2) l' hcontains
                cases hor with
                | inl hOld =>
                  exact Nat.lt_of_lt_of_le (hwf2 l' hOld) (locset_fold_max_ge_init ls result2.nextLoc')
                | inr hMem =>
                  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self l')
                    (locset_fold_max_succ_ge_of_mem ls result2.nextLoc' l' hMem)
              · simp [h_etyp2_int] at htc
        | _ => simp at htc

/-- typecheckDeref preserves wfTypeResult -/
private lemma typecheckDeref_wfTypeResult
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckDeref ctx e fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => unfold typecheckDeref at htc; simp at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckDeref_structure ctx e fuel'.succ res htc
    rcases hstruct with ⟨result1, htc1, hmem, _, hnextloc, _, _⟩
    have htc1' : typecheck ctx e fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e ctx result1 hwf htc1'
    intro l' hcontains
    rw [hmem] at hcontains; rw [hnextloc]
    exact hwf1 l' hcontains

/-- typecheckSeq preserves wfTypeResult -/
private lemma typecheckSeq_wfTypeResult
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckSeq ctx e1 e2 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckSeq] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckSeq_structure ctx e1 e2 fuel'.succ res htc
    rcases hstruct with ⟨result1, ctx', htc1, hctx', htc2⟩
    have htc1' : typecheck ctx e1 fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e1 ctx result1 hwf htc1'
    have hwf_ctx' : wfTypeContext ctx' := by
      rw [hctx']; simp only [updateCtxFromResult, wfTypeContext]; exact hwf1
    have htc2' : typecheck ctx' e2 fuel' = .ok res := by simpa using htc2
    exact IH fuel' h_fuel e2 ctx' res hwf_ctx' htc2'

/-- typecheckVlet preserves wfTypeResult -/
private lemma typecheckVlet_wfTypeResult
    (ctx : TypeContext) (x : Name) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckVlet ctx x e1 e2 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckVlet] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckVlet_structure ctx x e1 e2 fuel'.succ res htc
    rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, hmem, _, hnextloc, _, _, _, _⟩
    have htc1' : typecheck ctx e1 fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e1 ctx result1 hwf htc1'
    have hwf_ctx' : wfTypeContext ctx' := by
      rw [hctx']; simp only [wfTypeContext]; exact hwf1
    have htc2' : typecheck ctx' e2 fuel' = .ok result2 := by simpa using htc2
    have hwf2 : wfTypeResult result2 := IH fuel' h_fuel e2 ctx' result2 hwf_ctx' htc2'
    -- res inherits memEnv'/nextLoc' from result2
    intro l' hcontains
    rw [hmem] at hcontains; rw [hnextloc]
    exact hwf2 l' hcontains

/-- typecheckOp preserves wfTypeResult -/
private lemma typecheckOp_wfTypeResult
    (ctx : TypeContext) (e1 e2 : Expr) (op : Op) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckOp ctx e1 e2 fuel op = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckOp] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckOp_structure ctx e1 e2 op fuel'.succ res htc
    rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, hmem, _, hnextloc, _, _, _, _, _⟩
    have htc1' : typecheck ctx e1 fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e1 ctx result1 hwf htc1'
    have hwf_ctx2 : wfTypeContext (updateCtxFromResult ctx result1) := by
      simp only [updateCtxFromResult, wfTypeContext]; exact hwf1
    have htc2' : typecheck (updateCtxFromResult ctx result1) e2 fuel' = .ok result2 := by simpa using htc2
    have hwf2 : wfTypeResult result2 := IH fuel' h_fuel e2 (updateCtxFromResult ctx result1) result2 hwf_ctx2 htc2'
    intro l' hcontains
    rw [hmem] at hcontains; rw [hnextloc]
    exact hwf2 l' hcontains

/-- typecheckUnaryOp preserves wfTypeResult -/
private lemma typecheckUnaryOp_wfTypeResult
    (ctx : TypeContext) (op : UnaryOp) (e1 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckUnaryOp ctx op e1 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckUnaryOp] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckUnaryOp_structure ctx op e1 fuel'.succ res htc
    rcases hstruct with ⟨result1, _, htc1, _, hmem, _, hnextloc, _, _, _, _, _⟩
    have htc1' : typecheck ctx e1 fuel' = .ok result1 := by simpa using htc1
    have hwf1 : wfTypeResult result1 := IH fuel' h_fuel e1 ctx result1 hwf htc1'
    intro l' hcontains
    rw [hmem] at hcontains; rw [hnextloc]
    exact hwf1 l' hcontains

/-- typecheckIf preserves wfTypeResult -/
private lemma typecheckIf_wfTypeResult
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckIf ctx e1 e2 e3 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckIf] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel'.succ res htc
    rcases hstruct with h1 | h2 | hstd
    · -- Mode 1: Depoison, R(k) = true
      rcases h1 with ⟨k, deps, _, _, _, _, _, res2, res3, htc2, _htc3, hmem, _, hnextloc, _, _, _, _⟩
      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by simpa [ctxTrue] using htc2
      have hwf_ctxT : wfTypeContext ctxTrue := by simp only [ctxTrue, wfTypeContext]; exact hwf
      have hwf2 : wfTypeResult res2 := IH fuel' h_fuel e2 ctxTrue res2 hwf_ctxT htc2'
      intro l' hcontains
      rw [hmem] at hcontains
      exact Nat.lt_of_lt_of_le (hwf2 l' hcontains) (hnextloc ▸ le_max_left _ _)
    · -- Mode 2: Depoison, R(k) = false
      rcases h2 with ⟨k, deps, _, _, _, _, _, res2, res3, htc2, htc3, hmem, _, hnextloc, _, _, _, _⟩
      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                               nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
      have htc2' : typecheck ctxTrue e2 fuel' = .ok res2 := by simpa [ctxTrue] using htc2
      have hmono2 : ctxTrue.nextLoc ≤ res2.nextLoc' := by
        have := typecheck_nextLoc_mono ctxTrue e2 fuel' res2 htc2'; simpa [ctxTrue] using this
      have htc3' : typecheck ctxFalse e3 fuel' = .ok res3 := by simpa [ctxFalse] using htc3
      have hwf_ctxF : wfTypeContext ctxFalse := by
        intro l' hl'
        simp only [ctxFalse] at hl'
        exact Nat.lt_of_lt_of_le (hwf l' hl') hmono2
      have hwf3 : wfTypeResult res3 := IH fuel' h_fuel e3 ctxFalse res3 hwf_ctxF htc3'
      intro l' hcontains
      rw [hmem] at hcontains
      exact Nat.lt_of_lt_of_le (hwf3 l' hcontains) (hnextloc ▸ le_max_right _ _)
    · -- Standard conservative branch
      rcases hstd with ⟨_h_std_case, res1, htc1, _, res2, htc2, res3, htc3, hmem, _, hnextloc, _, _, _, _⟩
      have htc1' : typecheck ctx e1 fuel' = .ok res1 := by simpa using htc1
      have hwf1 : wfTypeResult res1 := IH fuel' h_fuel e1 ctx res1 hwf htc1'
      let ctx' : TypeContext := ctxAfter ctx res1
      let pc' := joinPoison ctx.pc res1.qualType.poison
      let ctx'' : TypeContext := { ctx' with pc := pc' }
      have hwf_ctx' : wfTypeContext ctx' := wfTypeContext_of_wfTypeResult ctx res1 hwf1
      have hwf_ctx'' : wfTypeContext ctx'' := by simp only [ctx'', wfTypeContext]; exact hwf_ctx'
      have htc2' : typecheck ctx'' e2 fuel' = .ok res2 := by simpa [ctx'', ctx', pc', ctxAfter] using htc2
      have hwf2 : wfTypeResult res2 := IH fuel' h_fuel e2 ctx'' res2 hwf_ctx'' htc2'
      have h_mono2 : res1.nextLoc' ≤ res2.nextLoc' := by
        have := typecheck_nextLoc_mono ctx'' e2 fuel' res2 htc2'
        simp [ctx'', ctx', ctxAfter] at this; exact this
      let ctxForE3 : TypeContext := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
      have hwf_ctxE3 : wfTypeContext ctxForE3 := by
        intro l hl
        simp only [ctxForE3, ctx'', ctx', ctxAfter] at hl ⊢
        exact Nat.lt_of_lt_of_le (hwf_ctx' l hl) h_mono2
      have htc3' : typecheck ctxForE3 e3 fuel' = .ok res3 := by
        simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using htc3
      have hwf3 : wfTypeResult res3 := IH fuel' h_fuel e3 ctxForE3 res3 hwf_ctxE3 htc3'
      intro l' hcontains; rw [hmem] at hcontains; rw [hnextloc]
      rcases joinMemEnvsStrong_contains_implies_or res2.memEnv' res3.memEnv' l' hcontains with h | h
      · exact Nat.lt_of_lt_of_le (hwf2 l' h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (hwf3 l' h) (Nat.le_max_right _ _)

/-- joinTypeResults preserves wfTypeResult -/
private lemma joinTypeResults_wfTypeResult
    (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (h_join : joinTypeResults ctx first rest = .ok res)
    (hwf_first : wfTypeResult first)
    (hwf_rest : ∀ r ∈ rest, wfTypeResult r) :
    wfTypeResult res := by
  have h_mem := joinTypeResults_mem_contains_head_or_rest ctx first rest res h_join
  have h_nextloc := joinTypeResults_nextLoc_eq_max ctx first rest res h_join
  intro l' hcontains
  rcases h_mem l' hcontains with hfirst | ⟨r, hr_mem, h_in⟩
  · rw [h_nextloc]
    have hle : first.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem; simp
    exact Nat.lt_of_lt_of_le (hwf_first l' hfirst) hle
  · rw [h_nextloc]
    have hle : r.nextLoc' ≤ List.max (first.nextLoc' :: rest.map TypeResult.nextLoc') (by intro h; cases h) := by
      apply List.le_max_of_mem; simp only [List.mem_cons, List.mem_map]; right; exact ⟨r, hr_mem, rfl⟩
    exact Nat.lt_of_lt_of_le ((hwf_rest r hr_mem) l' h_in) hle

-- ==========================================================================
-- Extern behavioral contract axioms for TypeSafety
-- These are irreducible assumptions about extern type-checking behavior.
-- ==========================================================================

/-- Extern contract: FnTClosure.extern preserves wfTypeResult.
    Remains an axiom: the proof would require a well-formedness invariant on the
    captured environment (i.e., all LocSet locations in `ETyp.ref ls` types in
    `capturedEnv` are already keys in `result2.memEnv'`, hence bounded by
    `result2.nextLoc'`). This invariant is maintained by the type system but not
    captured by `wfTypeResult result2` alone, which only bounds keys in `memEnv'`
    without relating them to LocSets appearing in type annotations. -/
axiom applyFnTClosure_extern_wfTypeResult
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult)
  (hwf2 : wfTypeResult result2)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  wfTypeResult r

/-- Extern contract: FnTClosure.extern preserves mem_contains (existing locations are kept).
    Proved: the effects loop applies `LocSet.fold ... updateMemEnv` which only inserts/updates
    entries (never removes), so containment is monotone. -/
lemma applyFnTClosure_extern_mem_contains_preserved
  (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
  (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
  (result2 : TypeResult) (fuel : Nat)
  (x : Name) (retSpec : ExternReturn) (effects : List Effect) (capturedEnv : CapturedVarEnv)
  (r : TypeResult)
  (happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
    argEtyp argPoison argPred ctx result2 fuel = .ok r) :
  ∀ l, result2.memEnv'.contains l → r.memEnv'.contains l := by
  cases fuel with
  | zero => unfold applyFnTClosure at happly; simp at happly
  | succ fuel =>
    intro l hl
    unfold applyFnTClosure at happly
    simp only [bind, Except.bind] at happly
    split at happly
    · simp at happly
    · rename_i tagInfo _
      rw [List.forIn_eq_foldlM] at happly
      simp only [Functor.map, Except.map] at happly
      split at happly
      · simp at happly
      · rename_i foldResult _hfoldOuter
        split at _hfoldOuter
        · simp at _hfoldOuter
        · rename_i foldStep hfoldStep
          simp only [Except.ok.injEq] at _hfoldOuter
          -- The effects loop preserves containment: foldResult.contains l
          have hContains : foldResult.contains l = true := by
            rw [← _hfoldOuter]
            apply List.foldlM_Except_preserves_property effects (ForInStep.yield result2.memEnv') _
              (fun s => (ForInStep.value s).contains l = true) hl ?_ foldStep hfoldStep
            intro acc effect hP
            cases acc with
            | done b =>
              intro acc' hg
              simp only [pure, Except.pure, Except.ok.injEq] at hg
              exact hg ▸ hP
            | yield b =>
              intro acc' hg
              split at hg
              · -- yield = yield b' case
                rename_i b' _heq
                have hbeq : b = b' := ForInStep.yield.inj _heq; subst hbeq
                split at hg
                · -- lookup = some qt
                  rename_i qt _hlookup
                  split at hg
                  · -- etyp = ETyp.ref ls: apply LocSet.fold contains preservation
                    rename_i ls _hls
                    split at hg
                    · -- resolveSyntaxPred error
                      exact absurd hg (by simp)
                    · -- resolveSyntaxPred ok v'
                      rename_i v' _hresolve
                      simp only [pure, Except.pure, Except.ok.injEq] at hg
                      cases hg; simp only [ForInStep.value]
                      unfold LocSet.fold; rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
                      exact list_fold_updateMemEnv_contains_of_contains _ b l _ hP
                  · -- non-ref etyp: error
                    exact absurd hg (by simp)
                · -- lookup = none: error
                  exact absurd hg (by simp)
              · -- yield = done: impossible
                rename_i b' _hdone
                exact absurd _hdone (by simp)
          -- r.memEnv' = foldResult in all retSpec cases
          split at happly
          · split at happly
            · simp at happly
            · split at happly
              · simp at happly
              · simp only [pure, Except.pure, Except.ok.injEq] at happly
                cases happly; exact hContains
          · simp only [pure, Except.pure, Except.ok.injEq] at happly
            cases happly; exact hContains
          · simp only [pure, Except.pure, Except.ok.injEq] at happly
            cases happly; exact hContains

/-- applyFnTClosure in ioFree mode preserves wfTypeResult -/
private lemma applyFnTClosure_ioFree_wfTypeResult
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res')
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top)
    (tcl : FnTClosure) (res : TypeResult)
    (hwf_fn : wfTypeResult result_fn)
    (htc : applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call = .ok res) :
    wfTypeResult res := by
  cases fuel_call with
  | zero => unfold applyFnTClosure at htc; simp at htc
  | succ fuelBody =>
    cases tcl with
    | regular x body tenv =>
      unfold applyFnTClosure at htc
      simp only [bind, Except.bind] at htc
      let ctx'' : TypeContext := { ctx with
        pc := joinPoison p (joinPoison p1 ctx.pc),
        memEnv := result_fn.memEnv',
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
        tagEnv := result_fn.tagEnv',
        nextTag := result_fn.nextTag',
        nextLoc := result_fn.nextLoc',
        regime := result_fn.regime' }
      cases htc_body : typecheckExpr ctx'' body fuelBody with
      | error _ => dsimp only [ctx''] at htc_body; simp [htc_body] at htc
      | ok result3 =>
        dsimp only [ctx''] at htc_body
        simp only [htc_body] at htc
        have hwf_ctx'' : wfTypeContext ctx'' := by simp only [ctx'', wfTypeContext]; exact hwf_fn
        have h_body_lt : fuelBody < fuel_top :=
          Nat.lt_trans (Nat.lt_succ_self fuelBody) h_call_lt
        have htc_body' : typecheck ctx'' body fuelBody = .ok result3 := by simpa [ctx''] using htc_body
        have hwf3 : wfTypeResult result3 := IH fuelBody h_body_lt body ctx'' result3 hwf_ctx'' htc_body'
        -- res = { result3 with qualType := ... }, so memEnv'/nextLoc' unchanged
        cases h_qt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
          simp [h_qt3] at htc
          cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
          | false => simp [hsub] at htc
          | true =>
            simp [hsub, pure, Except.pure] at htc
            cases htc; exact hwf3
    | extern x retSpec effects capturedEnv =>
      unfold applyFnTClosure at htc
      simp only [bind, Except.bind] at htc
      have happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
          argEtyp argPoison argPred ctx result_fn (fuelBody + 1) = .ok res := by
        unfold applyFnTClosure; simp only [bind, Except.bind]; exact htc
      exact applyFnTClosure_extern_wfTypeResult ctx st1 st2 p p1 argEtyp argPoison argPred
        result_fn (fuelBody + 1) x retSpec effects capturedEnv res hwf_fn happly

/-- applyPFnTClosure in ioFree mode preserves wfTypeResult -/
private lemma applyPFnTClosure_ioFree_wfTypeResult
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res')
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top)
    (tcl : PFnTClosure) (res : TypeResult)
    (hwf_fn : wfTypeResult result_fn)
    (htc : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call = .ok res) :
    wfTypeResult res := by
  cases fuel_call with
  | zero => unfold applyPFnTClosure at htc; simp at htc
  | succ fuelBody =>
    cases tcl with
    | regular x body tenv =>
      unfold applyPFnTClosure at htc
      simp only [bind, Except.bind] at htc
      let ctx'' : TypeContext := { ctx with
        pc := joinPoison p (joinPoison ctx.pc p1),
        memEnv := result_fn.memEnv',
        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
        tagEnv := result_fn.tagEnv',
        pureCtx := true,
        nextLoc := result_fn.nextLoc',
        nextTag := result_fn.nextTag',
        regime := result_fn.regime' }
      cases htc_body : typecheckExpr ctx'' (PExpr.toExpr body) fuelBody with
      | error _ => dsimp only [ctx''] at htc_body; simp [htc_body] at htc
      | ok result3 =>
        dsimp only [ctx''] at htc_body
        simp only [htc_body] at htc
        have hwf_ctx'' : wfTypeContext ctx'' := by simp only [ctx'', wfTypeContext]; exact hwf_fn
        have h_body_lt : fuelBody < fuel_top := Nat.lt_trans (Nat.lt_succ_self fuelBody) h_call_lt
        have htc_body' : typecheck ctx'' (PExpr.toExpr body) fuelBody = .ok result3 := by simpa [ctx''] using htc_body
        have hwf3 : wfTypeResult result3 := IH fuelBody h_body_lt (PExpr.toExpr body) ctx'' result3 hwf_ctx'' htc_body'
        cases h_qt3 : result3.qualType with
        | mk etyp3 p3 pred3 =>
          simp [h_qt3] at htc
          cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
          | false => simp [hsub] at htc
          | true =>
            simp [hsub, pure, Except.pure] at htc
            cases htc; exact hwf3
    | extern x retSpec capturedEnv =>
      unfold applyPFnTClosure at htc
      simp only [bind, Except.bind] at htc
      split at htc
      · split at htc <;> simp (config := { failIfUnchanged := false }) at htc
        split at htc <;> simp (config := { failIfUnchanged := false }) at htc
        split at htc <;> simp (config := { failIfUnchanged := false }) at htc
        rename_i hret
        simp only [pure, Except.pure, Except.ok.injEq] at htc
        have hnl := returnSpecToQTyp_preserves_nextLoc _ _ _ _ _ hret
        cases htc
        intro l hl; exact hnl ▸ hwf_fn l hl
      · simp [pure, Except.pure] at htc
        subst htc; exact hwf_fn
      · simp [pure, Except.pure] at htc
        subst htc; exact hwf_fn

/-- mapM of applyFnTClosure gives wfTypeResult for all results -/
lemma mapM_applyFnTClosure_forall_wfTypeResult
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res')
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top) (hwf_fn : wfTypeResult result_fn)
    (tcls : List FnTClosure) (results : List TypeResult)
    (hmapM : List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call) tcls = .ok results) :
    ∀ r ∈ results, wfTypeResult r := by
  induction tcls generalizing results with
  | nil =>
    simp [List.mapM_nil, pure, Except.pure] at hmapM
    cases hmapM; intro r hr; cases hr
  | cons tcl tcls' ih =>
    simp [List.mapM_cons, bind, Except.bind] at hmapM
    cases h1 : applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call with
    | error _ => simp [h1] at hmapM
    | ok r1 =>
      simp [h1] at hmapM
      cases h2 : List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call) tcls' with
      | error _ => simp [h2] at hmapM
      | ok rs' =>
        simp [h2, pure, Except.pure] at hmapM
        cases hmapM
        intro r hr
        simp at hr
        cases hr with
        | inl heq =>
          subst heq
          exact applyFnTClosure_ioFree_wfTypeResult fuel_top IH st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call h_call_lt tcl _ hwf_fn h1
        | inr htail =>
          exact ih rs' h2 r htail

/-- mapM of applyPFnTClosure gives wfTypeResult for all results -/
private lemma mapM_applyPFnTClosure_forall_wfTypeResult
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res')
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top) (hwf_fn : wfTypeResult result_fn)
    (tcls : List PFnTClosure) (results : List TypeResult)
    (hmapM : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call) tcls = .ok results) :
    ∀ r ∈ results, wfTypeResult r := by
  induction tcls generalizing results with
  | nil =>
    simp [List.mapM_nil, pure, Except.pure] at hmapM
    cases hmapM; intro r hr; cases hr
  | cons tcl tcls' ih =>
    simp [List.mapM_cons, bind, Except.bind] at hmapM
    cases h1 : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call with
    | error _ => simp [h1] at hmapM
    | ok r1 =>
      simp [h1] at hmapM
      cases h2 : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call) tcls' with
      | error _ => simp [h2] at hmapM
      | ok rs' =>
        simp [h2, pure, Except.pure] at hmapM
        cases hmapM
        intro r hr
        simp at hr
        cases hr with
        | inl heq =>
          subst heq
          exact applyPFnTClosure_ioFree_wfTypeResult fuel_top IH st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call h_call_lt tcl _ hwf_fn h1
        | inr htail =>
          exact ih rs' h2 r htail

/-- typecheckApp preserves wfTypeResult.
    Uses sorry for arrow/parrow mapM + joinTypeResults inline unfolding. -/
private lemma typecheckApp_wfTypeResult
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' →
        typecheck ctx' e m = .ok res' → wfTypeResult res') :
    typecheckApp ctx e1 e2 fuel = .ok res → wfTypeResult res := by
  intro htc
  cases fuel with
  | zero => simp [typecheckApp] at htc
  | succ fuel' =>
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    unfold typecheckApp at htc
    simp only [bind, Except.bind] at htc
    cases htc2 : typecheckExpr ctx e2 fuel' with
    | error _ => simp [htc2] at htc
    | ok result2 =>
      simp [htc2] at htc
      have hwf2 : wfTypeResult result2 :=
        IH fuel' h_fuel e2 ctx result2 hwf (by simpa [typecheck] using htc2)
      cases hqt2 : result2.qualType with
      | mk etyp2 p2 pred2 =>
        simp [hqt2] at htc
        cases htc1 : typecheckExpr { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' } e1 fuel' with
        | error _ => simp [htc1] at htc
        | ok result1 =>
          simp [htc1] at htc
          have hwf_ctx' : wfTypeContext { ctx with memEnv := result2.memEnv', tagEnv := result2.tagEnv', nextLoc := result2.nextLoc', nextTag := result2.nextTag', regime := result2.regime' } := by
            simp only [wfTypeContext]; exact hwf2
          have hwf1 : wfTypeResult result1 :=
            IH fuel' h_fuel e1 _ result1 hwf_ctx' (by simpa [typecheck] using htc1)
          cases hqt1 : result1.qualType with
          | mk etyp1 p1_val pred1 =>
            simp [hqt1] at htc
            cases etyp1 with
            | arrow st1 st2 p tcls =>
              simp at htc
              by_cases hpure : ctx.pureCtx = true
              · simp [hpure] at htc
              · simp [hpure] at htc
                simp [pure, Except.pure] at htc
                by_cases hempty : tcls = []
                · simp [hempty] at htc
                · simp [hempty] at htc
                  by_cases hsub : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = false
                  · simp [hsub] at htc
                  · push_neg at hsub
                    simp [hsub] at htc
                    cases hmap : List.mapM (fun tcl => applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2 ctx result1 fuel') tcls with
                    | error _ => simp [hmap] at htc
                    | ok results =>
                      simp [hmap] at htc
                      cases hresults : results with
                      | nil => subst hresults; simp at htc
                      | cons firstResult restResults =>
                        subst hresults; simp at htc
                        have hwf_all : ∀ r ∈ firstResult :: restResults, wfTypeResult r :=
                          mapM_applyFnTClosure_forall_wfTypeResult
                            fuel'.succ IH st1 st2 p p1_val etyp2 p2 pred2
                            ctx result1 fuel' h_fuel hwf1 tcls _ hmap
                        exact joinTypeResults_wfTypeResult ctx firstResult restResults res htc
                          (hwf_all firstResult (by simp))
                          (fun r hr => hwf_all r (by simp [hr]))
            | parrow st1 st2 p tcls_p =>
              simp at htc
              by_cases hempty : tcls_p = []
              · simp [hempty] at htc
              · simp [hempty] at htc
                simp [pure, Except.pure] at htc
                by_cases hsub : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = false
                · simp [hsub] at htc
                · push_neg at hsub
                  simp [hsub] at htc
                  cases hmap : List.mapM (fun tcl => applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2 ctx result1 fuel') tcls_p with
                  | error _ => simp [hmap] at htc
                  | ok results =>
                    simp [hmap] at htc
                    cases hresults : results with
                    | nil => subst hresults; simp at htc
                    | cons firstResult restResults =>
                      subst hresults; simp at htc
                      have hwf_all : ∀ r ∈ firstResult :: restResults, wfTypeResult r :=
                        mapM_applyPFnTClosure_forall_wfTypeResult
                          fuel'.succ IH st1 st2 p p1_val etyp2 p2 pred2
                          ctx result1 fuel' h_fuel hwf1 tcls_p _ hmap
                      exact joinTypeResults_wfTypeResult ctx firstResult restResults res htc
                        (hwf_all firstResult (by simp))
                        (fun r hr => hwf_all r (by simp [hr]))
            | _ => simp at htc

/-- Main lemma: typecheckExpr preserves wfTypeResult (strong induction on fuel) -/
private lemma typecheckExpr_preserves_wfTypeResult_main :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    wfTypeContext ctx → typecheck ctx e fuel = .ok res → wfTypeResult res := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res hwf htc
    -- IH from strong induction has order (ctx) (e) (res), but case lemmas expect (e) (ctx) (res)
    have IH' : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res' := by
      intro m hm e' ctx' res'; exact IH m hm ctx' e' res'
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
            wfTypeContext ctx' → typecheck ctx' e m = .ok res' → wfTypeResult res' := by
          intro m hm; exact IH' m (Nat.lt_trans hm h_fuel)
        cases e with
        | num _n =>
            unfold typecheckInt at htc; simp [pure, Except.pure] at htc; cases htc; exact hwf
        | bool _b =>
            unfold typecheckBool at htc; simp [pure, Except.pure] at htc; cases htc; exact hwf
        | unit =>
            unfold typecheckUnit at htc; simp [pure, Except.pure] at htc; cases htc; exact hwf
        | str _s =>
            unfold typecheckString at htc; simp [pure, Except.pure] at htc; cases htc; exact hwf
        | var x =>
            -- All typecheckVar paths return memEnv' = ctx.memEnv, nextLoc' = ctx.nextLoc
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                cases pred with
                | noPred =>
                  simp [pure, Except.pure] at htc; cases htc; exact hwf
                | guardOnly k =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    -- All tag lookup outcomes return memEnv' = ctx.memEnv, nextLoc' = ctx.nextLoc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; exact hwf
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;> exact hwf
                | guardClosure k tcls ptcls body_t =>
                  simp at htc
                  by_cases hfn : etyp.isFunctionType
                  · simp [hfn] at htc
                  · simp [hfn] at htc
                    -- All tag lookup outcomes return memEnv' = ctx.memEnv, nextLoc' = ctx.nextLoc
                    revert htc; generalize ctx.tagEnv[k]? = tv
                    cases tv with
                    | none => intro htc; simp at htc; cases htc; exact hwf
                    | some tv => cases tv with | mk val deps =>
                      cases val <;> intro htc <;> simp at htc <;> cases htc <;> exact hwf
        | fn x st1 body st2 =>
            unfold typecheckFn at htc; simp [pure, Except.pure] at htc; cases htc; exact hwf
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ => simp [h_topexpr, pure, Except.pure] at htc; cases htc; exact hwf
        | externVal _ _ _ =>
            simp only [typecheckExternVal] at htc
            simp [Bind.bind, Except.bind, pure, Except.pure] at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            cases htc
            rename_i _surf _heqSurf
            unfold wfTypeResult
            unfold surfaceSpecToQTyp at _heqSurf
            split at _heqSurf <;> simp [freshTLoc, bind, Except.bind, pure, Except.pure] at _heqSurf
            · intro l hl; cases _heqSurf; exact hwf l hl
            · intro l hl; cases _heqSurf; exact hwf l hl
            · intro l hl; cases _heqSurf; exact hwf l hl
            · intro l hl; cases _heqSurf; exact hwf l hl
            · split at _heqSurf <;> simp (config := { failIfUnchanged := false }) at _heqSurf
              subst _heqSurf
              rename_i _v _hcond
              split at _hcond
              · simp only [Except.ok.injEq] at _hcond
                cases _hcond
                intro l' hl
                have hor := updateMemEnv_contains_eq_or_old ctx.memEnv ctx.nextLoc l' _ hl
                cases hor with
                | inl hEq => rw [hEq]; exact Nat.lt_succ_self ctx.nextLoc
                | inr hOld => exact Nat.lt_of_lt_of_le (hwf l' hOld) (Nat.le_succ _)
              · simp at _hcond
        | externFn _ _ _ _ =>
            simp only [typecheckExternFn, pure, Except.pure] at htc
            cases htc
            exact hwf
        | externPfn _ _ _ =>
            simp only [typecheckExternPfn, pure, Except.pure] at htc
            cases htc
            exact hwf
        | op e1 op e2 =>
            simp at htc
            exact typecheckOp_wfTypeResult ctx e1 e2 op fuel' res hwf IH_fuel' htc
        | unaryop op e1 =>
            simp at htc
            exact typecheckUnaryOp_wfTypeResult ctx op e1 fuel' res hwf IH_fuel' htc
        | ite e1 e2 e3 =>
            simp at htc
            exact typecheckIf_wfTypeResult ctx e1 e2 e3 fuel' res hwf IH_fuel' htc
        | newRef e1 =>
            simp at htc
            exact typecheckNewRef_wfTypeResult ctx e1 fuel' res hwf IH_fuel' htc
        | assign e1 e2 =>
            simp at htc
            exact typecheckAssign_wfTypeResult ctx e1 e2 fuel' res hwf IH_fuel' htc
        | deref e1 =>
            simp at htc
            exact typecheckDeref_wfTypeResult ctx e1 fuel' res hwf IH_fuel' htc
        | seq e1 e2 =>
            simp at htc
            exact typecheckSeq_wfTypeResult ctx e1 e2 fuel' res hwf IH_fuel' htc
        | vlet x e1 e2 =>
            simp at htc
            exact typecheckVlet_wfTypeResult ctx x e1 e2 fuel' res hwf IH_fuel' htc
        | app e1 e2 =>
            simp at htc
            exact typecheckApp_wfTypeResult ctx e1 e2 fuel' res hwf IH_fuel' htc

/-- Public API: successful typechecking preserves wfTypeResult. -/
lemma typecheckExpr_preserves_wfTypeResult (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (hwf : wfTypeContext ctx) (htc : typecheck ctx e fuel = .ok res) :
    wfTypeResult res :=
  typecheckExpr_preserves_wfTypeResult_main fuel ctx e res hwf htc

end wfTypeResult_preservation

section memEnv_contains_preservation

lemma joinTypeResults_mem_contains_of_member
    (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (_h_join : joinTypeResults ctx first rest = .ok res)
    (_hmem_src : src ∈ first :: rest) :
    ∀ l, src.memEnv'.contains l → res.memEnv'.contains l := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_acc_contains :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ l, acc.2.1.contains l → acc'.2.1.contains l := by
    intro rs' acc acc' hfold
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        intro l hcontains
        exact hcontains
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            intro l hcontains_acc
            rcases memEnv_lookup_some_of_contains acc.2.1 l hcontains_acc with ⟨qt_acc, hlookup_acc⟩
            rcases joinMemEnvsStrong_lookup_some_of_left_lookup
                (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt1 := qt_acc) hlookup_acc with
              ⟨qt_acc1, hlookup_acc1⟩
            have hcontains_acc1 : acc1.2.1.contains l := by
              apply memEnv_contains_of_lookup_some (env := acc1.2.1) (l := l) (qt := qt_acc1)
              simpa [acc1] using hlookup_acc1
            exact ih (acc := acc1) hfold_tail l hcontains_acc1
  have h_fold_member_contains :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ r ∈ rs', ∀ l, r.memEnv'.contains l → acc'.2.1.contains l := by
    intro rs' acc acc' hfold
    induction rs' generalizing acc with
    | nil =>
        intro r hr
        cases hr
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            intro r hr l hcontains_r
            rcases List.mem_cons.mp hr with hrx | hrxs
            · subst r
              rcases memEnv_lookup_some_of_contains x.memEnv' l hcontains_r with ⟨qt_x, hlookup_x⟩
              rcases joinMemEnvsStrong_lookup_some_of_right_lookup
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt2 := qt_x) hlookup_x with
                ⟨qt_acc1, hlookup_acc1⟩
              have hcontains_acc1 : acc1.2.1.contains l := by
                apply memEnv_contains_of_lookup_some (env := acc1.2.1) (l := l) (qt := qt_acc1)
                simpa [acc1] using hlookup_acc1
              exact h_fold_acc_contains xs acc1 acc' hfold_tail l hcontains_acc1
            · exact ih (acc := acc1) hfold_tail r hrxs l hcontains_r
  have hsrc_sum : src = first ∨ src ∈ rest := List.mem_cons.mp _hmem_src
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              intro l hcontains_src
              cases hsrc_sum with
              | inl hsrc_eq =>
                  subst src
                  exact h_fold_acc_contains
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold l hcontains_src
              | inr hsrc_rest =>
                  exact h_fold_member_contains
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a
                    hfold src hsrc_rest l hcontains_src

private lemma applyFnTClosure_ioFree_mem_contains_preserved
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' →
        ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l)
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top)
    (tcl : FnTClosure) (res : TypeResult)
    (htc : applyFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call = .ok res) :
    ∀ l, result_fn.memEnv'.contains l → res.memEnv'.contains l := by
  cases fuel_call with
  | zero =>
      unfold applyFnTClosure at htc
      simp at htc
  | succ fuelBody =>
      cases tcl with
      | regular x body tenv =>
          unfold applyFnTClosure at htc
          simp only [bind, Except.bind] at htc
          let ctx'' : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison p1 ctx.pc),
              memEnv := result_fn.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result_fn.tagEnv',
              nextTag := result_fn.nextTag',
              nextLoc := result_fn.nextLoc',
              regime := result_fn.regime' }
          cases htc_body : typecheckExpr ctx'' body fuelBody with
          | error _ =>
              dsimp only [ctx''] at htc_body
              simp [htc_body] at htc
          | ok result3 =>
              dsimp only [ctx''] at htc_body
              simp only [htc_body] at htc
              have h_body_lt : fuelBody < fuel_top := Nat.lt_trans (Nat.lt_succ_self fuelBody) h_call_lt
              have hpres3 :
                  ∀ l, ctx''.memEnv.contains l → result3.memEnv'.contains l :=
                IH fuelBody h_body_lt body ctx'' result3
                  (by simpa [typecheck, ctx''] using htc_body)
              cases h_qt3 : result3.qualType with
              | mk etyp3 p3 pred3 =>
                  simp [h_qt3] at htc
                  cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                  | false =>
                      simp [hsub] at htc
                  | true =>
                      simp [hsub, pure, Except.pure] at htc
                      cases htc
                      intro l hcontains
                      exact hpres3 l (by simpa [ctx''] using hcontains)
      | extern x retSpec effects capturedEnv =>
          unfold applyFnTClosure at htc
          simp only [bind, Except.bind] at htc
          have happly : applyFnTClosure (FnTClosure.extern x retSpec effects capturedEnv) st1 st2 p p1
              argEtyp argPoison argPred ctx result_fn (fuelBody + 1) = .ok res := by
            unfold applyFnTClosure; simp only [bind, Except.bind]; exact htc
          exact applyFnTClosure_extern_mem_contains_preserved ctx st1 st2 p p1 argEtyp argPoison
            argPred result_fn (fuelBody + 1) x retSpec effects capturedEnv res happly

private lemma applyPFnTClosure_ioFree_mem_contains_preserved
    (fuel_top : Nat)
    (IH : ∀ m < fuel_top, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' →
        ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l)
    (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result_fn : TypeResult) (fuel_call : Nat)
    (h_call_lt : fuel_call < fuel_top)
    (tcl : PFnTClosure) (res : TypeResult)
    (htc : applyPFnTClosure tcl st1 st2 p p1 argEtyp argPoison argPred ctx result_fn fuel_call = .ok res) :
    ∀ l, result_fn.memEnv'.contains l → res.memEnv'.contains l := by
  cases fuel_call with
  | zero =>
      unfold applyPFnTClosure at htc
      simp at htc
  | succ fuelBody =>
      cases tcl with
      | regular x body tenv =>
          unfold applyPFnTClosure at htc
          simp only [bind, Except.bind] at htc
          let ctx'' : TypeContext :=
            { ctx with
              pc := joinPoison p (joinPoison ctx.pc p1),
              memEnv := result_fn.memEnv',
              varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
                ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩,
              tagEnv := result_fn.tagEnv',
              pureCtx := true,
              nextLoc := result_fn.nextLoc',
              nextTag := result_fn.nextTag',
              regime := result_fn.regime' }
          cases htc_body : typecheckExpr ctx'' (PExpr.toExpr body) fuelBody with
          | error _ =>
              dsimp only [ctx''] at htc_body
              simp [htc_body] at htc
          | ok result3 =>
              dsimp only [ctx''] at htc_body
              simp only [htc_body] at htc
              have h_body_lt : fuelBody < fuel_top := Nat.lt_trans (Nat.lt_succ_self fuelBody) h_call_lt
              have hpres3 :
                  ∀ l, ctx''.memEnv.contains l → result3.memEnv'.contains l :=
                IH fuelBody h_body_lt (PExpr.toExpr body) ctx'' result3
                  (by simpa [typecheck, ctx''] using htc_body)
              cases h_qt3 : result3.qualType with
              | mk etyp3 p3 pred3 =>
                  simp [h_qt3] at htc
                  cases hsub : isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                  | false =>
                      simp [hsub] at htc
                  | true =>
                      simp [hsub, pure, Except.pure] at htc
                      cases htc
                      intro l hcontains
                      exact hpres3 l (by simpa [ctx''] using hcontains)
      | extern x retSpec capturedEnv =>
          unfold applyPFnTClosure at htc
          simp only [bind, Except.bind] at htc
          split at htc
          · split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            simp [pure, Except.pure, Except.ok.injEq] at htc
            cases htc; intro l hl; exact hl
          · simp [pure, Except.pure] at htc
            subst htc; intro l hl; exact hl
          · simp [pure, Except.pure] at htc
            subst htc; intro l hl; exact hl

private lemma typecheckApp_mem_contains_preserved
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' →
        ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l) :
    typecheckApp ctx e1 e2 fuel = .ok res →
    ∀ l, ctx.memEnv.contains l → res.memEnv'.contains l := by
  intro htc l hcontains
  cases fuel with
  | zero =>
      simp [typecheckApp] at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      unfold typecheckApp at htc
      simp only [bind, Except.bind] at htc
      cases htc2 : typecheckExpr ctx e2 fuel' with
      | error _ =>
          simp [htc2] at htc
      | ok result2 =>
          simp [htc2] at htc
          have hcontains2 : result2.memEnv'.contains l :=
            IH fuel' h_fuel e2 ctx result2 (by simpa [typecheck] using htc2) l hcontains
          cases hqt2 : result2.qualType with
          | mk etyp2 p2 pred2 =>
              simp [hqt2] at htc
              let ctxFun : TypeContext :=
                { ctx with
                  memEnv := result2.memEnv'
                  tagEnv := result2.tagEnv'
                  nextLoc := result2.nextLoc'
                  nextTag := result2.nextTag'
                  regime := result2.regime' }
              have hctxFun : ctxFun.memEnv.contains l := by
                simpa [ctxFun] using hcontains2
              cases htc1 : typecheckExpr ctxFun e1 fuel' with
              | error _ =>
                  simp [ctxFun, htc1] at htc
              | ok result1 =>
                  simp [ctxFun, htc1] at htc
                  have hcontains1 : result1.memEnv'.contains l :=
                    IH fuel' h_fuel e1 ctxFun result1
                      (by simpa [typecheck, ctxFun] using htc1) l hctxFun
                  cases hqt1 : result1.qualType with
                  | mk etyp1 p1_val pred1 =>
                      simp [hqt1] at htc
                      cases etyp1 with
                      | arrow st1 st2 p tcls =>
                          simp at htc
                          by_cases hpure : ctx.pureCtx = true
                          · simp [hpure] at htc
                          · simp [hpure] at htc
                            simp [pure, Except.pure] at htc
                            by_cases hempty : tcls = []
                            · simp [hempty] at htc
                            · simp [hempty] at htc
                              by_cases hsub : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = false
                              · simp [hsub] at htc
                              · push_neg at hsub
                                simp [hsub] at htc
                                cases hmap :
                                    List.mapM
                                      (fun tcl =>
                                        applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                          ctx result1 fuel') tcls with
                                | error _ =>
                                    simp [hmap] at htc
                                | ok results =>
                                    simp [hmap] at htc
                                    cases hresults : results with
                                    | nil =>
                                        subst hresults
                                        simp at htc
                                    | cons firstResult restResults =>
                                        subst hresults
                                        simp at htc
                                        have hforall2 :
                                            List.Forall₂
                                              (fun tcl r =>
                                                applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                  ctx result1 fuel' = .ok r)
                                              tcls (firstResult :: restResults) := by
                                          exact
                                            List.mapM_Except_ok_implies_forall2 tcls
                                              (fun tcl =>
                                                applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                  ctx result1 fuel')
                                              (firstResult :: restResults)
                                              (by simp [hmap])
                                        have hflip :
                                            List.Forall₂
                                              (fun r tcl =>
                                                applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                  ctx result1 fuel' = .ok r)
                                              (firstResult :: restResults) tcls :=
                                          List.Forall₂.flip hforall2
                                        rcases List.Forall2.exists_of_mem_left
                                            (R := fun r tcl =>
                                              applyFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                ctx result1 fuel' = .ok r)
                                            hflip firstResult (by simp) with
                                          ⟨tcl0, _htclMem, happly⟩
                                        have hcontains_first : firstResult.memEnv'.contains l :=
                                          applyFnTClosure_ioFree_mem_contains_preserved
                                            fuel'.succ IH st1 st2 p p1_val etyp2 p2 pred2
                                            ctx result1 fuel' h_fuel tcl0 firstResult happly l hcontains1
                                        exact
                                          joinTypeResults_mem_contains_of_member
                                            ctx firstResult firstResult restResults res htc
                                            (by simp) l hcontains_first
                      | parrow st1 st2 p tcls_p =>
                          simp at htc
                          by_cases hempty : tcls_p = []
                          · simp [hempty] at htc
                          · simp [hempty] at htc
                            simp [pure, Except.pure] at htc
                            by_cases hsub : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = false
                            · simp [hsub] at htc
                            · push_neg at hsub
                              simp [hsub] at htc
                              cases hmap :
                                  List.mapM
                                    (fun tcl =>
                                      applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                        ctx result1 fuel') tcls_p with
                              | error _ =>
                                  simp [hmap] at htc
                              | ok results =>
                                  simp [hmap] at htc
                                  cases hresults : results with
                                  | nil =>
                                      subst hresults
                                      simp at htc
                                  | cons firstResult restResults =>
                                      subst hresults
                                      simp at htc
                                      have hforall2 :
                                          List.Forall₂
                                            (fun tcl r =>
                                              applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                ctx result1 fuel' = .ok r)
                                            tcls_p (firstResult :: restResults) := by
                                        exact
                                          List.mapM_Except_ok_implies_forall2 tcls_p
                                            (fun tcl =>
                                              applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                ctx result1 fuel')
                                            (firstResult :: restResults)
                                            (by simp [hmap])
                                      have hflip :
                                          List.Forall₂
                                            (fun r tcl =>
                                              applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                                ctx result1 fuel' = .ok r)
                                            (firstResult :: restResults) tcls_p :=
                                        List.Forall₂.flip hforall2
                                      rcases List.Forall2.exists_of_mem_left
                                          (R := fun r tcl =>
                                            applyPFnTClosure tcl st1 st2 p p1_val etyp2 p2 pred2
                                              ctx result1 fuel' = .ok r)
                                          hflip firstResult (by simp) with
                                        ⟨tcl0, _htclMem, happly⟩
                                      have hcontains_first : firstResult.memEnv'.contains l :=
                                        applyPFnTClosure_ioFree_mem_contains_preserved
                                          fuel'.succ IH st1 st2 p p1_val etyp2 p2 pred2
                                          ctx result1 fuel' h_fuel tcl0 firstResult happly l hcontains1
                                      exact
                                        joinTypeResults_mem_contains_of_member
                                          ctx firstResult firstResult restResults res htc
                                          (by simp) l hcontains_first
                      | _ =>
                          simp at htc

private lemma typecheckAssign_mem_contains_preserved
    (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' →
        ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l) :
    typecheckAssign ctx e1 e2 fuel = .ok res →
    ∀ l, ctx.memEnv.contains l → res.memEnv'.contains l := by
  intro htc l hcontains
  cases fuel with
  | zero =>
      unfold typecheckAssign at htc
      simp at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      unfold typecheckAssign at htc
      simp only [bind, Except.bind] at htc
      cases h_tc1 : typecheckExpr ctx e1 fuel' with
      | error _ =>
          simp [h_tc1] at htc
      | ok result1 =>
          simp only [h_tc1] at htc
          have hcontains1 : result1.memEnv'.contains l :=
            IH fuel' h_fuel e1 ctx result1 (by simpa [typecheck] using h_tc1) l hcontains
          cases h_qt1 : result1.qualType with
          | mk etyp1 p1 pred1 =>
              rw [h_qt1] at htc
              simp at htc
              cases etyp1 with
              | ref ls =>
                  simp at htc
                  let ctx2 : TypeContext :=
                    { ctx with
                      memEnv := result1.memEnv'
                      tagEnv := result1.tagEnv'
                      nextLoc := result1.nextLoc'
                      nextTag := result1.nextTag'
                      regime := result1.regime' }
                  have hctx2 : ctx2.memEnv.contains l := by
                    simpa [ctx2] using hcontains1
                  cases h_tc2 : typecheckExpr ctx2 e2 fuel' with
                  | error _ =>
                      simp [ctx2, h_tc2] at htc
                  | ok result2 =>
                      simp [ctx2, h_tc2] at htc
                      have hcontains2 : result2.memEnv'.contains l :=
                        IH fuel' h_fuel e2 ctx2 result2
                          (by simpa [typecheck, ctx2] using h_tc2) l hctx2
                      cases h_qt2 : result2.qualType with
                      | mk etyp2 p2 pred2 =>
                          rw [h_qt2] at htc
                          simp at htc
                          by_cases h_etyp2_int : etyp2 = ETyp.int
                          · subst h_etyp2_int
                            simp at htc
                            cases htc
                            exact
                              assign_memEnv_formula_contains_of_contains
                                result2.memEnv' ls
                                (joinPoison ctx.pc (joinPoison p1 p2))
                                (if p1 = true ∨ ctx.pc = true then Predicate.noPred else pred2)
                                l hcontains2
                          · simp [h_etyp2_int] at htc
              | _ =>
                  simp at htc

private lemma typecheckIf_mem_contains_preserved
    (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) (res : TypeResult)
    (IH : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
        typecheck ctx' e m = .ok res' →
        ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l) :
    typecheckIf ctx e1 e2 e3 fuel = .ok res →
    ∀ l, ctx.memEnv.contains l → res.memEnv'.contains l := by
  intro htc l hcontains
  cases fuel with
  | zero =>
      simp [typecheckIf] at htc
  | succ fuel' =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      rcases typecheckIf_structure ctx e1 e2 e3 (fuel' + 1) res htc with
        htrue | hfalse | hstd
      · rcases htrue with
          ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool, res2, _res3, htc2, _htc3, h_mem,
           _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
        let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
        have hcontains2 : res2.memEnv'.contains l :=
          IH fuel' h_fuel e2 ctxTrue res2
            (by simpa [typecheck, ctxTrue] using htc2) l
            (by simpa [ctxTrue] using hcontains)
        simpa [h_mem] using hcontains2
      · rcases hfalse with
          ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool, _res2, res3, _htc2, htc3, h_mem,
           _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
        let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                                 nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
        have hcontains3 : res3.memEnv'.contains l :=
          IH fuel' h_fuel e3 ctxFalse res3
            (by simpa [typecheck, ctxFalse] using htc3) l
            (by simpa [ctxFalse] using hcontains)
        simpa [h_mem] using hcontains3
      · rcases hstd with
          ⟨_h_std_case, res1, htc1, _hbool, res2, hstd_tail⟩
        simp at hstd_tail
        rcases hstd_tail with ⟨htc2, res3, hstd_tail'⟩
        rcases hstd_tail' with
          ⟨htc3, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp, _h_pred⟩
        let ctx2 : TypeContext :=
          { ctx with
            memEnv := res1.memEnv'
            tagEnv := res1.tagEnv'
            nextLoc := res1.nextLoc'
            nextTag := res1.nextTag'
            regime := res1.regime'
            pc := joinPoison ctx.pc res1.qualType.poison }
        let ctx3 : TypeContext :=
          { ctx with
            memEnv := res1.memEnv'
            tagEnv := res1.tagEnv'
            nextLoc := res2.nextLoc'
            nextTag := res2.nextTag'
            regime := res1.regime'
            pc := joinPoison ctx.pc res1.qualType.poison }
        have hcontains1 : res1.memEnv'.contains l :=
          IH fuel' h_fuel e1 ctx res1
            (by simpa [typecheck] using htc1) l hcontains
        have hcontains2 : res2.memEnv'.contains l :=
          IH fuel' h_fuel e2 ctx2 res2
            (by simpa [typecheck, ctx2] using htc2) l
            (by simpa [ctx2] using hcontains1)
        rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
        rcases joinMemEnvsStrong_lookup_some_of_left_lookup res2.memEnv' res3.memEnv' l qt2 hlookup2 with
          ⟨qt, hlookup_join⟩
        have hcontains_join : (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
          exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
        simpa [h_mem] using hcontains_join

private lemma typecheckExpr_ioFree_mem_contains_preserved_main :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
      typecheck ctx e fuel = .ok res →
      ∀ l, ctx.memEnv.contains l → res.memEnv'.contains l := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro ctx e res htc l hcontains
      have IH' : ∀ m < fuel, ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
          typecheck ctx' e m = .ok res' →
          ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l := by
        intro m hm e' ctx' res' htc' l hcontains
        exact IH m hm ctx' e' res' htc' l hcontains
      unfold typecheck at htc
      cases fuel with
      | zero =>
          unfold typecheckExpr at htc
          simp at htc
      | succ fuel' =>
          unfold typecheckExpr at htc
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have hltSub : fuel' - 1 < fuel'.succ := by
            exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
          have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
              typecheck ctx' e m = .ok res' →
              ∀ l, ctx'.memEnv.contains l → res'.memEnv'.contains l := by
            intro m hm
            exact IH' m (Nat.lt_trans hm h_fuel)
          cases e with
          | num _ =>
              unfold typecheckInt at htc
              simp [pure, Except.pure] at htc
              cases htc
              simpa using hcontains
          | bool _ =>
              unfold typecheckBool at htc
              simp [pure, Except.pure] at htc
              cases htc
              simpa using hcontains
          | unit =>
              unfold typecheckUnit at htc
              simp [pure, Except.pure] at htc
              cases htc
              simpa using hcontains
          | str _ =>
              unfold typecheckString at htc
              simp [pure, Except.pure] at htc
              cases htc
              simpa using hcontains
          | var x =>
              have htcVar : typecheckVar ctx x = .ok res := by
                simpa [typecheckExpr] using htc
              have hmem : res.memEnv' = ctx.memEnv := typecheckVar_preserves_memEnv ctx x res htcVar
              simpa [hmem] using hcontains
          | fn x st1 body st2 =>
              unfold typecheckFn at htc
              simp [pure, Except.pure] at htc
              cases htc
              simpa using hcontains
          | pfn x st1 body st2 =>
              unfold typecheckPfn at htc
              simp [bind, Except.bind] at htc
              cases h_topexpr : body.toPExpr with
              | error _ =>
                  simp [h_topexpr] at htc
              | ok _ =>
                  simp [h_topexpr, pure, Except.pure] at htc
                  cases htc
                  simpa using hcontains
          | externVal typ poison pred =>
              simp only [typecheckExternVal] at htc
              simp [Bind.bind, Except.bind, pure, Except.pure] at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              split at htc <;> simp (config := { failIfUnchanged := false }) at htc
              cases htc
              rename_i _surf _heqSurf
              unfold surfaceSpecToQTyp at _heqSurf
              split at _heqSurf <;> simp [freshTLoc, bind, Except.bind, pure, Except.pure] at _heqSurf
              · cases _heqSurf; exact hcontains
              · cases _heqSurf; exact hcontains
              · cases _heqSurf; exact hcontains
              · cases _heqSurf; exact hcontains
              · split at _heqSurf <;> simp (config := { failIfUnchanged := false }) at _heqSurf
                subst _heqSurf
                rename_i _v _hcond
                split at _hcond
                · simp only [Except.ok.injEq] at _hcond
                  cases _hcond
                  exact updateMemEnv_contains_of_contains ctx.memEnv ctx.nextLoc l _ hcontains
                · simp at _hcond
          | externFn arg argTyp retSpec effects =>
              simp only [typecheckExternFn, pure, Except.pure] at htc
              cases htc
              exact hcontains
          | externPfn arg argTyp retSpec =>
              simp only [typecheckExternPfn, pure, Except.pure] at htc
              cases htc
              exact hcontains
          | op e1 bop e2 =>
              have htcOp : typecheckOp ctx e1 e2 fuel' bop = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckOp_structure ctx e1 e2 bop fuel' res htcOp with
                ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
                  _h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              have hctx2 : (updateCtxFromResult ctx result1).memEnv.contains l := by
                simpa [updateCtxFromResult] using hcontains1
              have hcontains2 : result2.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e2 (updateCtxFromResult ctx result1) result2
                  (by simpa [typecheck, updateCtxFromResult] using htc2) l hctx2
              simpa [h_mem] using hcontains2
          | unaryop uop e1 =>
              have htcUnary : typecheckUnaryOp ctx uop e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckUnaryOp_structure ctx uop e1 fuel' res htcUnary with
                ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime,
                  _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              simpa [h_mem] using hcontains1
          | ite e1 e2 e3 =>
              have htcIf : typecheckIf ctx e1 e2 e3 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              exact typecheckIf_mem_contains_preserved ctx e1 e2 e3 fuel' res IH_fuel' htcIf l hcontains
          | newRef e1 =>
              have htcNew : typecheckNewRef ctx e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckNewRef_structure ctx e1 fuel' res htcNew with
                ⟨result1, l0, htc1, _hl0, _hInt, _hRetEtyp, _hRetPoison, _hRetPred, h_mem,
                  _h_tag, _h_loc, _h_ntag, _h_regime⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              rw [h_mem]
              exact
                updateMemEnv_contains_of_contains result1.memEnv' l0 l
                  ⟨ETyp.int, joinPoison ctx.pc result1.qualType.poison,
                    if ctx.pc then Predicate.noPred else result1.qualType.pred⟩
                  hcontains1
          | assign e1 e2 =>
              have htcAssign : typecheckAssign ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              exact typecheckAssign_mem_contains_preserved ctx e1 e2 fuel' res IH_fuel' htcAssign l hcontains
          | deref e1 =>
              have htcDeref : typecheckDeref ctx e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckDeref_structure ctx e1 fuel' res htcDeref with
                ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              simpa [h_mem] using hcontains1
          | seq e1 e2 =>
              have htcSeq : typecheckSeq ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
                ⟨result1, ctx', htc1, hctx', htc2⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              have hctx' : ctx'.memEnv.contains l := by
                simpa [hctx'] using hcontains1
              exact
                IH' (fuel' - 1) hltSub e2 ctx' res
                  (by simpa [typecheck, hctx'] using htc2) l hctx'
          | vlet x e1 e2 =>
              have htcVlet : typecheckVlet ctx x e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
                ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc,
                  _h_ntag, _h_regime, _h_ret_poison, _h_ret_pred⟩
              have hcontains1 : result1.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e1 ctx result1
                  (by simpa [typecheck] using htc1) l hcontains
              have hctx' : ctx'.memEnv.contains l := by
                simpa [hctx'] using hcontains1
              have hcontains2 : result2.memEnv'.contains l :=
                IH' (fuel' - 1) hltSub e2 ctx' result2
                  (by simpa [typecheck, hctx'] using htc2) l hctx'
              simpa [h_mem] using hcontains2
          | app e1 e2 =>
              have htcApp : typecheckApp ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              exact typecheckApp_mem_contains_preserved ctx e1 e2 fuel' res IH_fuel' htcApp l hcontains

/-- Successful ioFree typing preserves membership of every pre-existing memory location. -/
lemma typecheckExpr_ioFree_mem_contains_preserved
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) (l : Loc)
    (htc : typecheckExpr ctx e fuel = .ok res)
    (hcontains : ctx.memEnv.contains l) :
    res.memEnv'.contains l :=
  typecheckExpr_ioFree_mem_contains_preserved_main fuel ctx e res (by simpa [typecheck] using htc) l hcontains

end memEnv_contains_preservation

lemma joinTypeResults_transport_valueHasETyp_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : valueHasETyp θ v src.qualType.etyp) :
  valueHasETyp θ v res.qualType.etyp := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_val :
      ∀ (rs' : List TypeResult) (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        valueHasETyp θ v acc.1 →
        valueHasETyp θ v acc'.1 := by
    intro rs' acc acc' hcompat hfold hval_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        simpa using hval_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hval_acc1 : valueHasETyp θ v acc1.1 := by
              have hjoin : valueHasETyp θ v (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) :=
                valueHasETyp_joinETyps_left
                  (θ := θ) (v := v) (t1 := acc.1) (t2 := resEtyp)
                  (p1 := acc.2.2.1) (p2 := resPoison) hval_acc
              simpa [acc1] using hjoin
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            exact ih (acc := acc1) hcompat_tail hfold_tail hval_acc1
  have h_fold_member_val :
      ∀ (rs' : List TypeResult) (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        valueHasETyp θ v src'.qualType.etyp →
        valueHasETyp θ v acc'.1 := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hval_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hval_x : valueHasETyp θ v resEtyp := by
                simpa [hqx] using hval_src'
              have hval_acc1 : valueHasETyp θ v acc1.1 := by
                have hjoin :
                    valueHasETyp θ v (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) :=
                  valueHasETyp_joinETyps_right
                    (θ := θ) (v := v) (t1 := acc.1) (t2 := resEtyp)
                    (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x hval_x
                simpa [acc1] using hjoin
              exact h_fold_left_val xs acc1 acc' hcompat_tail hfold_tail hval_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hval_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at _h_join
          contradiction
      | ok _ =>
          erw [hcheck] at _h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at _h_join
              contradiction
          | ok a =>
              erw [hfold] at _h_join
              have heq := Except.ok.inj _h_join
              have hetyp_res : a.1 = res.qualType.etyp := by
                exact congrArg (fun tr => tr.qualType.etyp) heq
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hval_a : valueHasETyp θ v a.1 :=
                  h_fold_left_val rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a hcompat hfold (by simpa [hqt] using h_src)
                simpa [hetyp_res] using hval_a
              · have hval_a : valueHasETyp θ v a.1 :=
                  h_fold_member_val rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a src hcompat hfold hsrc_tail h_src
                simpa [hetyp_res] using hval_a

lemma joinTypeResults_mem_subset
    (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (hjoin : joinTypeResults ctx first rest = .ok res)
    (hfirst : ∀ l, first.memEnv'.contains l → ctx.memEnv.contains l)
    (hrest : ∀ r ∈ rest, ∀ l, r.memEnv'.contains l → ctx.memEnv.contains l) :
    ∀ l, res.memEnv'.contains l → ctx.memEnv.contains l := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_subset :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        (∀ l, acc.2.1.contains l → ctx.memEnv.contains l) →
        (∀ r ∈ rs', ∀ l, r.memEnv'.contains l → ctx.memEnv.contains l) →
        (∀ l, acc'.2.1.contains l → ctx.memEnv.contains l) := by
    intro rs' acc acc' hfold hacc hsubs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons r rs ih =>
        cases hqr : r.qualType with
        | mk etyp_r poison_r pred_r =>
            simp [List.foldlM_cons, joinStep, hqr, bind, Except.bind] at hfold
            let acc1 : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 etyp_r acc.2.2.1 poison_r,
                joinMemEnvsStrong acc.2.1 r.memEnv',
                joinPoison acc.2.2.1 poison_r,
                joinPredicates acc.2.2.2.1 pred_r,
                joinTagEnvs acc.2.2.2.2.1 r.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 r.regime',
                max acc.2.2.2.2.2.2.1 r.nextLoc',
                max acc.2.2.2.2.2.2.2 r.nextTag')
            have hacc1 : ∀ l, acc1.2.1.contains l → ctx.memEnv.contains l := by
              intro l hl
              have hor := joinMemEnvsStrong_contains_implies_or acc.2.1 r.memEnv' l hl
              cases hor with
              | inl hleft =>
                  exact hacc l hleft
              | inr hright =>
                  exact hsubs r (by simp) l hright
            have hsubs_tail : ∀ r' ∈ rs, ∀ l, r'.memEnv'.contains l → ctx.memEnv.contains l := by
              intro r' hr' l hl
              exact hsubs r' (by simp [hr']) l hl
            exact ih acc1 hfold hacc1 hsubs_tail
  cases hqf : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqf, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at hjoin
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
            () rest : Except String Unit) with
      | error _err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error _err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok acc =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              have hacc0 : ∀ l, first.memEnv'.contains l → ctx.memEnv.contains l := hfirst
              exact h_fold_subset rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag')
                acc hfold hacc0 hrest

lemma joinMemEnvs_lookup_of_some_some
    (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (h1 : env1.lookup l = some qt)
    (h2 : env2.lookup l = some qt) :
    (joinMemEnvs env1 env2).lookup l = some qt := by
  have h1_get : env1.get? l = some ⟨qt.poison, qt.pred⟩ := memEnv_get_eq_of_lookup env1 l qt h1
  have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt h1
  have h_in_keys : l ∈ env1.keys := ExtTreeMap.mem_keys.2 hcontains1
  have h_mem : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ h_in_keys)
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some e1
    | none, some e2 => some e2
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo :=
    combineExtTreeMaps_go_get_mem env1 env2 f
      (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_mem
  have h2_get : env2.get? l = some ⟨qt.poison, qt.pred⟩ := memEnv_get_eq_of_lookup env2 l qt h2
  have hgo' :
      (combineExtTreeMaps.go env1 env2 f
        (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
    erw [h1_get, h2_get] at hgo
    simp [f, joinPoison_idempotent, joinPredicates_idempotent] at hgo
    simpa [f] using hgo
  have hcombine : (combineExtTreeMaps env1 env2 f).get? l = some ⟨qt.poison, qt.pred⟩ := by
    simpa [combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hgo'
  have heq : combineExtTreeMaps env1 env2 f = joinMemEnvs env1 env2 := by
    simp only [joinMemEnvs]; congr 2
  rw [← heq, MemoryTypeEnv.lookup, hcombine, Option.map, memEnv_lookup_toQTyp env1 l qt h1]

lemma joinMemEnvsStrong_lookup_of_some_some
    (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
    (h1 : env1.lookup l = some qt)
    (h2 : env2.lookup l = some qt) :
    (joinMemEnvsStrong env1 env2).lookup l = some qt := by
  have h1_get : env1.get? l = some ⟨qt.poison, qt.pred⟩ := memEnv_get_eq_of_lookup env1 l qt h1
  have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt h1
  have h_in_keys : l ∈ env1.keys := ExtTreeMap.mem_keys.2 hcontains1
  have h_mem : l ∈ (env1.keys ++ env2.keys).eraseDups := by
    exact List.mem_eraseDups_of_mem (List.mem_append_left _ h_in_keys)
  let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
    match oe1, oe2 with
    | some e1, none => some ⟨e1.poison, Predicate.noPred⟩
    | none, some e2 => some ⟨e2.poison, Predicate.noPred⟩
    | some e1, some e2 =>
      some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
    | none, none => none
  have hgo :=
    combineExtTreeMaps_go_get_mem env1 env2 f
      (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv) l h_mem
  have h2_get : env2.get? l = some ⟨qt.poison, qt.pred⟩ := memEnv_get_eq_of_lookup env2 l qt h2
  have hgo' :
      (combineExtTreeMaps.go env1 env2 f
        (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
    erw [h1_get, h2_get] at hgo
    simp [f, joinPoison_idempotent, joinPredicates_idempotent] at hgo
    simpa [f] using hgo
  have hcombine : (combineExtTreeMaps env1 env2 f).get? l = some ⟨qt.poison, qt.pred⟩ := by
    simpa [combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hgo'
  have heq : combineExtTreeMaps env1 env2 f = joinMemEnvsStrong env1 env2 := by
    simp only [joinMemEnvsStrong]; congr 2
  rw [← heq, MemoryTypeEnv.lookup, hcombine, Option.map, memEnv_lookup_toQTyp env1 l qt h1]

lemma joinTypeResults_mem_lookup_of_all
    (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (hjoin : joinTypeResults ctx first rest = .ok res)
    (l : Loc) (qt : QTyp)
    (hfirst : first.memEnv'.lookup l = some qt)
    (hrest : ∀ r ∈ rest, r.memEnv'.lookup l = some qt) :
    res.memEnv'.lookup l = some qt := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_mem :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.2.1.lookup l = some qt →
        (∀ r ∈ rs', r.memEnv'.lookup l = some qt) →
        acc'.2.1.lookup l = some qt := by
    intro rs' acc acc' hfold hacc hsubs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons r rs ih =>
        cases hqr : r.qualType with
        | mk etyp_r poison_r pred_r =>
            simp [List.foldlM_cons, joinStep, hqr, bind, Except.bind] at hfold
            let acc1 : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 etyp_r acc.2.2.1 poison_r,
                joinMemEnvsStrong acc.2.1 r.memEnv',
                joinPoison acc.2.2.1 poison_r,
                joinPredicates acc.2.2.2.1 pred_r,
                joinTagEnvs acc.2.2.2.2.1 r.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 r.regime',
                max acc.2.2.2.2.2.2.1 r.nextLoc',
                max acc.2.2.2.2.2.2.2 r.nextTag')
            have hacc1 : acc1.2.1.lookup l = some qt := by
              exact joinMemEnvsStrong_lookup_of_some_some acc.2.1 r.memEnv' l qt hacc (hsubs r (by simp))
            have hsubs_tail : ∀ r' ∈ rs, r'.memEnv'.lookup l = some qt := by
              intro r' hr'
              exact hsubs r' (by simp [hr'])
            exact ih acc1 hfold hacc1 hsubs_tail
  cases hqf : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqf, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at hjoin
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
            () rest : Except String Unit) with
      | error _err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error _err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok acc =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              exact h_fold_mem rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag')
                acc hfold hfirst hrest

lemma joinTypeResults_regime_lookup_of_all
    (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (hjoin : joinTypeResults ctx first rest = .ok res)
    (k : Tag) (b : Bool)
    (hfirst : first.regime'.lookup? k = some b)
    (hrest : ∀ r ∈ rest, r.regime'.lookup? k = some b) :
    res.regime'.lookup? k = some b := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
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
        acc.2.2.2.2.2.1.lookup? k = some b →
        (∀ r ∈ rs', r.regime'.lookup? k = some b) →
        acc'.2.2.2.2.2.1.lookup? k = some b := by
    intro rs' acc acc' hfold hacc hsubs
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons r rs ih =>
        cases hqr : r.qualType with
        | mk etyp_r poison_r pred_r =>
            simp [List.foldlM_cons, joinStep, hqr, bind, Except.bind] at hfold
            let acc1 : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 etyp_r acc.2.2.1 poison_r,
                joinMemEnvsStrong acc.2.1 r.memEnv',
                joinPoison acc.2.2.1 poison_r,
                joinPredicates acc.2.2.2.1 pred_r,
                joinTagEnvs acc.2.2.2.2.1 r.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 r.regime',
                max acc.2.2.2.2.2.2.1 r.nextLoc',
                max acc.2.2.2.2.2.2.2 r.nextTag')
            have hacc1 : acc1.2.2.2.2.2.1.lookup? k = some b := by
              exact joinRegimes_lookup_of_some_some acc.2.2.2.2.2.1 r.regime' k b hacc (hsubs r (by simp))
            have hsubs_tail : ∀ r' ∈ rs, r'.regime'.lookup? k = some b := by
              intro r' hr'
              exact hsubs r' (by simp [hr'])
            exact ih acc1 hfold hacc1 hsubs_tail
  cases hqf : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqf, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, TypecheckM] at hjoin
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
            () rest : Except String Unit) with
      | error _err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag') rest with
          | error _err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok acc =>
              erw [hfold] at hjoin
              simp at hjoin
              subst res
              exact h_fold_regime rest
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc', first.nextTag')
                acc hfold hfirst hrest

lemma typecheckExpr_mem_contains_preserved
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (htc : typecheckExpr ctx e fuel = .ok res) :
    ∀ l, ctx.memEnv.contains l → res.memEnv'.contains l := by
  intro l hcontains
  exact typecheckExpr_ioFree_mem_contains_preserved ctx e fuel res l htc hcontains

lemma typecheckExpr_pure_mem_subset_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ l, res.memEnv'.contains l → ctx.memEnv.contains l := by
  classical
  revert ctx e pe res hpe htc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e pe res hpe htc l hl
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e <;> try (simp [Expr.toPExpr?] at hpe)
      case num n =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hl
      case bool b =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hl
      case unit =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hl
      case str s =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hl
      case var x =>
        have htcVar : typecheckVar { ctx with pureCtx := true } x = .ok res := by
          simpa [typecheckExpr] using htc
        have hmem :
            res.memEnv' = ({ ctx with pureCtx := true }).memEnv :=
          typecheckVar_preserves_memEnv { ctx with pureCtx := true } x res htcVar
        have hl' : ({ ctx with pureCtx := true }).memEnv.contains l := by
          simpa [hmem] using hl
        simpa using hl'
      case op e1 op e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcOp :
                    typecheckOp { ctx with pureCtx := true } e1 e2 fuel' op = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckOp_structure { ctx with pureCtx := true } e1 e2 op fuel' res htcOp with
                  ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
                have hsub1 :
                    ∀ l, result1.memEnv'.contains l → ctx.memEnv.contains l :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1
                have htc2' :
                    typecheckExpr
                        { updateCtxFromResult { ctx with pureCtx := true } result1 with pureCtx := true }
                        e2 (fuel' - 1) = .ok result2 := by
                  simpa [updateCtxFromResult] using htc2
                have hsub2 :
                    ∀ l,
                      result2.memEnv'.contains l →
                        (updateCtxFromResult { ctx with pureCtx := true } result1).memEnv.contains l :=
                  ih (fuel' - 1) hltSub (updateCtxFromResult { ctx with pureCtx := true } result1)
                    e2 pe2 result2 hpe2 htc2'
                have hl2 : result2.memEnv'.contains l := by
                  simpa [h_mem] using hl
                have hctx2 :
                    (updateCtxFromResult { ctx with pureCtx := true } result1).memEnv.contains l :=
                  hsub2 l hl2
                have hl1 : result1.memEnv'.contains l := by
                  simpa [updateCtxFromResult] using hctx2
                exact hsub1 l hl1
      case deref e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcD :
                typecheckDeref { ctx with pureCtx := true } e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckDeref_structure { ctx with pureCtx := true } e1 fuel' res htcD with
              ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime⟩
            have hsub1 :
                ∀ l, result1.memEnv'.contains l → ctx.memEnv.contains l :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1
            have hl1 : result1.memEnv'.contains l := by
              simpa [h_mem] using hl
            exact hsub1 l hl1
      case vlet x e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcVlet :
                    typecheckVlet { ctx with pureCtx := true } x e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckVlet_structure { ctx with pureCtx := true } x e1 e2 fuel' res htcVlet with
                  ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_poison, _h_ret_pred⟩
                have hsub1 :
                    ∀ l, result1.memEnv'.contains l → ctx.memEnv.contains l :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1
                have htc2' :
                    typecheckExpr { ctx' with pureCtx := true } e2 (fuel' - 1) = .ok result2 := by
                  simpa [hctx'] using htc2
                have hsub2 :
                    ∀ l, result2.memEnv'.contains l → ctx'.memEnv.contains l :=
                  ih (fuel' - 1) hltSub ctx' e2 pe2 result2 hpe2 htc2'
                have hl2 : result2.memEnv'.contains l := by
                  simpa [h_mem] using hl
                have hctx2 : ctx'.memEnv.contains l := hsub2 l hl2
                have hl1 : result1.memEnv'.contains l := by
                  simpa [hctx'] using hctx2
                exact hsub1 l hl1
      case app e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcApp :
                    typecheckApp { ctx with pureCtx := true } e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckApp_structure { ctx with pureCtx := true } e1 e2 fuel' res htcApp with
                  ⟨result2, result1, st1, st2, p, p1, _isArrow, htc2, htc1, hcases⟩
                have hsub_arg :
                    ∀ l, result2.memEnv'.contains l → ctx.memEnv.contains l :=
                  ih (fuel' - 1) hltSub ctx e2 pe2 result2 hpe2 htc2
                let ctxFun :
                    TypeContext :=
                  { ctx with
                    memEnv := result2.memEnv'
                    tagEnv := result2.tagEnv'
                    nextLoc := result2.nextLoc'
                    nextTag := result2.nextTag'
                    regime := result2.regime' }
                have htc1' :
                    typecheckExpr { ctxFun with pureCtx := true } e1 (fuel' - 1) = .ok result1 := by
                  simpa [ctxFun] using htc1
                have hsub_fun_in :
                    ∀ l, result1.memEnv'.contains l → ctxFun.memEnv.contains l :=
                  ih (fuel' - 1) hltSub ctxFun e1 pe1 result1 hpe1 htc1'
                have hsub_fun :
                    ∀ l, result1.memEnv'.contains l → ctx.memEnv.contains l := by
                  intro l hl1
                  have hctxFun : ctxFun.memEnv.contains l := hsub_fun_in l hl1
                  have hl2 : result2.memEnv'.contains l := by
                    simpa [ctxFun] using hctxFun
                  exact hsub_arg l hl2
                cases hcases with
                | inl harrow =>
                    rcases harrow with ⟨_hisArrow, _hArrow, _hp1eq, hnotPure, _hsubtype⟩
                    simp at hnotPure
                | inr hparrow =>
                    rcases hparrow with
                      ⟨_hisArrowFalse, ⟨tcls, het1⟩, _hp1eq, hsubtype⟩
                    cases hq2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                        cases fuel' with
                        | zero =>
                            simp [typecheckApp] at htcApp
                        | succ fuelApp =>
                            have htc2' :
                                typecheckExpr { ctx with pureCtx := true } e2 fuelApp = .ok result2 := by
                              simpa using htc2
                            have htc1'' :
                                typecheckExpr { ctxFun with pureCtx := true } e1 fuelApp = .ok result1 := by
                              simpa [ctxFun] using htc1
                            have htcApp' := htcApp
                            unfold typecheckApp at htcApp'
                            simp [bind, Except.bind, htc2', hq2] at htcApp'
                            erw [htc1''] at htcApp'
                            cases hq1 : result1.qualType with
                            | mk et1 p1r pred1 =>
                                have het1' : et1 = ETyp.parrow st1 st2 p tcls := by
                                  simpa [hq1] using het1
                                have hp1r : p1r = p1 := by
                                  simpa [hq1] using _hp1eq
                                simp [hq1] at htcApp'
                                rw [het1'] at htcApp'
                                simp at htcApp'
                                by_cases htclsNil : tcls = []
                                · simp [htclsNil] at htcApp'
                                · have hsubtype' : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                                    simpa [hq2] using hsubtype
                                  simp [htclsNil, hsubtype'] at htcApp'
                                  cases hmap :
                                      List.mapM
                                        (fun tcl =>
                                          applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                            { ctx with pureCtx := true } result1 fuelApp)
                                        tcls with
                              | error err =>
                                  simp [hmap] at htcApp'
                                  cases htcApp'
                              | ok results =>
                                  cases results with
                                  | nil =>
                                      simp [hmap] at htcApp'
                                      cases htcApp'
                                  | cons first rest =>
                                      simp [hmap] at htcApp'
                                      have hjoin :
                                          joinTypeResults { ctx with pureCtx := true } first rest = .ok res := by
                                        exact htcApp'
                                      have hforall2 :
                                          List.Forall₂
                                            (fun tcl r =>
                                              applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                            tcls (first :: rest) := by
                                        exact
                                          List.mapM_Except_ok_implies_forall2 tcls
                                            (fun tcl =>
                                              applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                { ctx with pureCtx := true } result1 fuelApp)
                                            (first :: rest) (by simp [hmap])
                                      have hres_sub :
                                          ∀ r ∈ (first :: rest), ∀ l,
                                            r.memEnv'.contains l → ctx.memEnv.contains l := by
                                        intro r hr l hrl
                                        have hflip :
                                            List.Forall₂
                                              (fun r tcl =>
                                                applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                  { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                              (first :: rest) tcls :=
                                          List.Forall₂.flip hforall2
                                        rcases List.Forall2.exists_of_mem_left
                                            (R := fun r tcl =>
                                              applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                            hflip r hr with
                                          ⟨tcl, _htclMem, happly⟩
                                        cases tcl with
                                        | regular x pbody env =>
                                            cases fuelApp with
                                            | zero =>
                                                simp [applyPFnTClosure] at happly
                                            | succ fuelBody =>
                                                unfold applyPFnTClosure at happly
                                                simp [bind, Except.bind] at happly
                                                cases htcBody :
                                                    typecheckExpr
                                                      { { ctx with pureCtx := true } with
                                                        pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                        memEnv := result1.memEnv'
                                                        varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                            ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                        tagEnv := result1.tagEnv'
                                                        pureCtx := true
                                                        nextTag := result1.nextTag'
                                                        nextLoc := result1.nextLoc'
                                                        regime := result1.regime' }
                                                      (PExpr.toExpr pbody) fuelBody with
                                                | error err =>
                                                    simp [htcBody] at happly
                                                | ok result3 =>
                                                    simp [htcBody] at happly
                                                    cases hsubBodyRet : isSubtype st2 result3.qualType with
                                                    | false =>
                                                        cases hq3 : result3.qualType with
                                                        | mk et3 p3 pred3 =>
                                                            have hsubBodyRet' :
                                                                isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                                                              simpa [hq3] using hsubBodyRet
                                                            have hcontra : False := by
                                                              simp [hsubBodyRet', hq3] at happly
                                                            exact False.elim hcontra
                                                    | true =>
                                                        simp [hsubBodyRet, pure, Except.pure] at happly
                                                        have hr_mem : r.memEnv'.contains l = result3.memEnv'.contains l := by
                                                          cases hq3 : result3.qualType with
                                                          | mk et3 p3 pred3 =>
                                                              simp [hq3] at happly
                                                              have hrEq :
                                                                  r =
                                                                    { result3 with
                                                                      qualType :=
                                                                        normalizeAppResultByProvenance (joinPoison p1r p)
                                                                          { result3.qualType with
                                                                            poison := joinPoison p1r
                                                                              (joinPoison p result3.qualType.poison) } } := by
                                                                simpa [hq3] using happly.symm
                                                              simp [hrEq]
                                                        have hrl3 : result3.memEnv'.contains l := by
                                                          simpa [hr_mem] using hrl
                                                        let ctxBody :
                                                            TypeContext :=
                                                          { { ctx with pureCtx := true } with
                                                            pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                            memEnv := result1.memEnv'
                                                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                            tagEnv := result1.tagEnv'
                                                            pureCtx := true
                                                            nextTag := result1.nextTag'
                                                            nextLoc := result1.nextLoc'
                                                            regime := result1.regime' }
                                                        have hpeBody :
                                                            Expr.toPExpr? (PExpr.toExpr pbody) = some pbody := by
                                                          simpa using toExpr_toPExpr? pbody
                                                        have htcBody' :
                                                            typecheckExpr { ctxBody with pureCtx := true }
                                                              (PExpr.toExpr pbody) fuelBody = .ok result3 := by
                                                          simpa [ctxBody] using htcBody
                                                        have hsubBody :
                                                            ∀ l, result3.memEnv'.contains l → ctxBody.memEnv.contains l :=
                                                          ih fuelBody (by omega)
                                                            ctxBody (PExpr.toExpr pbody) pbody result3
                                                            hpeBody htcBody'
                                                        have hctxBody : ctxBody.memEnv.contains l := hsubBody l hrl3
                                                        have hl1 : result1.memEnv'.contains l := by
                                                          simpa [ctxBody] using hctxBody
                                                        exact hsub_fun l hl1
                                        | extern x retSpec capturedEnv =>
                                            have hmemEq := applyPFnTClosure_extern_memEnv_eq
                                              _ _ _ _ _ _ _ _ result1 r fuelApp x retSpec capturedEnv happly
                                            rw [hmemEq] at hrl
                                            exact hsub_fun l hrl
                                      have hfirst_sub :
                                          ∀ l, first.memEnv'.contains l →
                                            ({ ctx with pureCtx := true }).memEnv.contains l := by
                                        intro l hl
                                        have hctx : ctx.memEnv.contains l := hres_sub first (by simp) l hl
                                        simpa using hctx
                                      have hrest_sub :
                                          ∀ r ∈ rest, ∀ l, r.memEnv'.contains l →
                                            ({ ctx with pureCtx := true }).memEnv.contains l := by
                                        intro r hr l hl
                                        have hr' : r ∈ first :: rest := List.mem_cons_of_mem first hr
                                        have hctx : ctx.memEnv.contains l := hres_sub r hr' l hl
                                        simpa using hctx
                                      have hsub_join :
                                          ∀ l,
                                            res.memEnv'.contains l →
                                              ({ ctx with pureCtx := true }).memEnv.contains l :=
                                        joinTypeResults_mem_subset
                                          ({ ctx with pureCtx := true }) first rest res hjoin
                                          hfirst_sub hrest_sub
                                      have hctxPure : ({ ctx with pureCtx := true }).memEnv.contains l :=
                                        hsub_join l hl
                                      simpa using hctxPure
      case ite e1 e2 e3 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                cases hpe3 : Expr.toPExpr? e3 with
                | none =>
                    simp [hpe1, hpe2, hpe3] at hpe
                | some pe3 =>
                    have htcIf :
                        typecheckIf { ctx with pureCtx := true } e1 e2 e3 fuel' = .ok res := by
                      simpa [typecheckExpr] using htc
                    rcases typecheckIf_structure { ctx with pureCtx := true } e1 e2 e3 fuel' res htcIf with
                      htrue | hfalse | hstd
                    · rcases htrue with
                        ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool, res2, _res3, htc2, _htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
                      have htc2' :
                          typecheckExpr { ctxTrue with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctxTrue] using htc2
                      have hsub2 :
                          ∀ l, res2.memEnv'.contains l → ctxTrue.memEnv.contains l :=
                        ih (fuel' - 1) hltSub ctxTrue e2 pe2 res2 hpe2 htc2'
                      have hl2 : res2.memEnv'.contains l := by
                        simpa [h_mem] using hl
                      have hctxTrue : ctxTrue.memEnv.contains l := hsub2 l hl2
                      simpa [ctxTrue] using hctxTrue
                    · rcases hfalse with
                        ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool, _res2, res3, _htc2, htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                                                               nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
                      have htc3' :
                          typecheckExpr { ctxFalse with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctxFalse] using htc3
                      have hsub3 :
                          ∀ l, res3.memEnv'.contains l → ctxFalse.memEnv.contains l :=
                        ih (fuel' - 1) hltSub ctxFalse e3 pe3 res3 hpe3 htc3'
                      have hl3 : res3.memEnv'.contains l := by
                        simpa [h_mem] using hl
                      have hctxFalse : ctxFalse.memEnv.contains l := hsub3 l hl3
                      simpa [ctxFalse] using hctxFalse
                    · rcases hstd with
                        ⟨_h_std_case, res1, htc1, _hbool, res2, hstd_tail⟩
                      simp at hstd_tail
                      rcases hstd_tail with ⟨htc2, res3, hstd_tail'⟩
                      rcases hstd_tail' with
                        ⟨htc3, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp, _h_pred⟩
                      let ctx2 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      let ctx3 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res2.nextLoc'
                          nextTag := res2.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      have htc1' :
                          typecheckExpr { ctx with pureCtx := true } e1 (fuel' - 1) = .ok res1 := by
                        simpa using htc1
                      have hsub1 :
                          ∀ l, res1.memEnv'.contains l → ctx.memEnv.contains l :=
                        ih (fuel' - 1) hltSub ctx e1 pe1 res1 hpe1 htc1'
                      have htc2' :
                          typecheckExpr { ctx2 with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctx2] using htc2
                      have hsub2 :
                          ∀ l, res2.memEnv'.contains l → ctx2.memEnv.contains l :=
                        ih (fuel' - 1) hltSub ctx2 e2 pe2 res2 hpe2 htc2'
                      have htc3' :
                          typecheckExpr { ctx3 with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctx3] using htc3
                      have hsub3 :
                          ∀ l, res3.memEnv'.contains l → ctx3.memEnv.contains l :=
                        ih (fuel' - 1) hltSub ctx3 e3 pe3 res3 hpe3 htc3'
                      have hljoin : (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l := by
                        simpa [h_mem] using hl
                      have hor := joinMemEnvsStrong_contains_implies_or res2.memEnv' res3.memEnv' l hljoin
                      cases hor with
                      | inl h2 =>
                          have hctx2 : ctx2.memEnv.contains l := hsub2 l h2
                          have hl1 : res1.memEnv'.contains l := by
                            simpa [ctx2] using hctx2
                          exact hsub1 l hl1
                      | inr h3 =>
                          have hctx3 : ctx3.memEnv.contains l := hsub3 l h3
                          have hl1 : res1.memEnv'.contains l := by
                            simpa [ctx3] using hctx3
                          exact hsub1 l hl1
      case unaryop op e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcUnary :
                typecheckUnaryOp { ctx with pureCtx := true } op e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckUnaryOp_structure { ctx with pureCtx := true } op e1 fuel' res htcUnary with
              ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_ret_etyp,
                _h_ret_poison, _h_ret_pred⟩
            have hsub1 :
                ∀ l, result1.memEnv'.contains l → ctx.memEnv.contains l :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1
            have hl1 : result1.memEnv'.contains l := by
              simpa [h_mem] using hl
            exact hsub1 l hl1

lemma typecheckExpr_pure_regime_bridge_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ k b, ctx.regime.lookup? k = some b → res.regime'.lookup? k = some b := by
  classical
  revert ctx e pe res hpe htc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e pe res hpe htc k b hk
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e <;> try (simp [Expr.toPExpr?] at hpe)
      case num n =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hk
      case bool b' =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hk
      case unit =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hk
      case str s =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hk
      case var x =>
        have htcVar : typecheckVar { ctx with pureCtx := true } x = .ok res := by
          simpa [typecheckExpr] using htc
        have hreg :
            res.regime' = ({ ctx with pureCtx := true }).regime :=
          typecheckVar_preserves_regime { ctx with pureCtx := true } x res htcVar
        simpa [hreg] using hk
      case op e1 op e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcOp :
                    typecheckOp { ctx with pureCtx := true } e1 e2 fuel' op = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckOp_structure { ctx with pureCtx := true } e1 e2 op fuel' res htcOp with
                  ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, _h_mem, _h_tag, _h_loc, _h_ntag,
                    h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
                have hreg1 :
                    result1.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 k b hk
                have htc2' :
                    typecheckExpr
                        { updateCtxFromResult { ctx with pureCtx := true } result1 with pureCtx := true }
                        e2 (fuel' - 1) = .ok result2 := by
                  simpa [updateCtxFromResult] using htc2
                have hk2 :
                    (updateCtxFromResult { ctx with pureCtx := true } result1).regime.lookup? k = some b := by
                  simpa [updateCtxFromResult] using hreg1
                have hreg2 :
                    result2.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub (updateCtxFromResult { ctx with pureCtx := true } result1)
                    e2 pe2 result2 hpe2 htc2' k b hk2
                simpa [h_regime] using hreg2
      case deref e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcD :
                typecheckDeref { ctx with pureCtx := true } e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckDeref_structure { ctx with pureCtx := true } e1 fuel' res htcD with
              ⟨result1, htc1, _h_mem, _h_tag, _h_loc, _h_ntag, h_regime⟩
            have hreg1 :
                result1.regime'.lookup? k = some b :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 k b hk
            simpa [h_regime] using hreg1
      case vlet x e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcVlet :
                    typecheckVlet { ctx with pureCtx := true } x e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckVlet_structure { ctx with pureCtx := true } x e1 e2 fuel' res htcVlet with
                  ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, _h_mem, _h_tag, _h_loc, _h_ntag,
                    h_regime, _h_ret_poison, _h_ret_pred⟩
                have hreg1 :
                    result1.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 k b hk
                have htc2' :
                    typecheckExpr { ctx' with pureCtx := true } e2 (fuel' - 1) = .ok result2 := by
                  simpa [hctx'] using htc2
                have hk2 : ctx'.regime.lookup? k = some b := by
                  simpa [hctx'] using hreg1
                have hreg2 :
                    result2.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub ctx' e2 pe2 result2 hpe2 htc2' k b hk2
                simpa [h_regime] using hreg2
      case app e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcApp :
                    typecheckApp { ctx with pureCtx := true } e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckApp_structure { ctx with pureCtx := true } e1 e2 fuel' res htcApp with
                  ⟨result2, result1, st1, st2, p, p1, _isArrow, htc2, htc1, hcases⟩
                have hreg_arg :
                    result2.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub ctx e2 pe2 result2 hpe2 htc2 k b hk
                let ctxFun :
                    TypeContext :=
                  { ctx with
                    memEnv := result2.memEnv'
                    tagEnv := result2.tagEnv'
                    nextLoc := result2.nextLoc'
                    nextTag := result2.nextTag'
                    regime := result2.regime' }
                have htc1' :
                    typecheckExpr { ctxFun with pureCtx := true } e1 (fuel' - 1) = .ok result1 := by
                  simpa [ctxFun] using htc1
                have hkFun : ctxFun.regime.lookup? k = some b := by
                  simpa [ctxFun] using hreg_arg
                have hreg_fun :
                    result1.regime'.lookup? k = some b :=
                  ih (fuel' - 1) hltSub ctxFun e1 pe1 result1 hpe1 htc1' k b hkFun
                cases hcases with
                | inl harrow =>
                    rcases harrow with ⟨_hisArrow, _hArrow, _hp1eq, hnotPure, _hsubtype⟩
                    simp at hnotPure
                | inr hparrow =>
                    rcases hparrow with
                      ⟨_hisArrowFalse, ⟨tcls, het1⟩, _hp1eq, hsubtype⟩
                    cases hq2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                        cases fuel' with
                        | zero =>
                            simp [typecheckApp] at htcApp
                        | succ fuelApp =>
                            have htc2' :
                                typecheckExpr { ctx with pureCtx := true } e2 fuelApp = .ok result2 := by
                              simpa using htc2
                            have htc1'' :
                                typecheckExpr { ctxFun with pureCtx := true } e1 fuelApp = .ok result1 := by
                              simpa [ctxFun] using htc1
                            have htcApp' := htcApp
                            unfold typecheckApp at htcApp'
                            simp [bind, Except.bind, htc2', hq2] at htcApp'
                            erw [htc1''] at htcApp'
                            cases hq1 : result1.qualType with
                            | mk et1 p1r pred1 =>
                                have het1' : et1 = ETyp.parrow st1 st2 p tcls := by
                                  simpa [hq1] using het1
                                have hp1r : p1r = p1 := by
                                  simpa [hq1] using _hp1eq
                                simp [hq1] at htcApp'
                                rw [het1'] at htcApp'
                                simp at htcApp'
                                by_cases htclsNil : tcls = []
                                · simp [htclsNil] at htcApp'
                                · have hsubtype' : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                                    simpa [hq2] using hsubtype
                                  simp [htclsNil, hsubtype'] at htcApp'
                                  cases hmap :
                                      List.mapM
                                        (fun tcl =>
                                          applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                            { ctx with pureCtx := true } result1 fuelApp)
                                        tcls with
                                  | error err =>
                                      simp [hmap] at htcApp'
                                      cases htcApp'
                                  | ok results =>
                                      cases results with
                                      | nil =>
                                          simp [hmap] at htcApp'
                                          cases htcApp'
                                      | cons first rest =>
                                          simp [hmap] at htcApp'
                                          have hjoin :
                                              joinTypeResults { ctx with pureCtx := true } first rest = .ok res := by
                                            exact htcApp'
                                          have hforall2 :
                                              List.Forall₂
                                                (fun tcl r =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                tcls (first :: rest) := by
                                            exact
                                              List.mapM_Except_ok_implies_forall2 tcls
                                                (fun tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp)
                                                (first :: rest) (by simp [hmap])
                                          have hres_reg :
                                              ∀ r ∈ (first :: rest), r.regime'.lookup? k = some b := by
                                            intro r hr
                                            have hflip :
                                                List.Forall₂
                                                  (fun r tcl =>
                                                    applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                      { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                  (first :: rest) tcls :=
                                              List.Forall₂.flip hforall2
                                            rcases List.Forall2.exists_of_mem_left
                                                (R := fun r tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                hflip r hr with
                                              ⟨tcl, _htclMem, happly⟩
                                            cases tcl with
                                            | regular x pbody env =>
                                                cases fuelApp with
                                                | zero =>
                                                    simp [applyPFnTClosure] at happly
                                                | succ fuelBody =>
                                                    unfold applyPFnTClosure at happly
                                                    simp [bind, Except.bind] at happly
                                                    cases htcBody :
                                                        typecheckExpr
                                                          { { ctx with pureCtx := true } with
                                                            pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                            memEnv := result1.memEnv'
                                                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                            tagEnv := result1.tagEnv'
                                                            pureCtx := true
                                                            nextTag := result1.nextTag'
                                                            nextLoc := result1.nextLoc'
                                                            regime := result1.regime' }
                                                          (PExpr.toExpr pbody) fuelBody with
                                                    | error err =>
                                                        simp [htcBody] at happly
                                                    | ok result3 =>
                                                        simp [htcBody] at happly
                                                        cases hsubBodyRet : isSubtype st2 result3.qualType with
                                                        | false =>
                                                            cases hq3 : result3.qualType with
                                                            | mk et3 p3 pred3 =>
                                                                have hsubBodyRet' :
                                                                    isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                                                                  simpa [hq3] using hsubBodyRet
                                                                have hcontra : False := by
                                                                  simp [hsubBodyRet', hq3] at happly
                                                                exact False.elim hcontra
                                                        | true =>
                                                            simp [hsubBodyRet, pure, Except.pure] at happly
                                                            let ctxBody :
                                                                TypeContext :=
                                                              { { ctx with pureCtx := true } with
                                                                pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                                memEnv := result1.memEnv'
                                                                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                    ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                                tagEnv := result1.tagEnv'
                                                                pureCtx := true
                                                                nextTag := result1.nextTag'
                                                                nextLoc := result1.nextLoc'
                                                                regime := result1.regime' }
                                                            have hpeBody :
                                                                Expr.toPExpr? (PExpr.toExpr pbody) = some pbody := by
                                                              simpa using toExpr_toPExpr? pbody
                                                            have htcBody' :
                                                                typecheckExpr { ctxBody with pureCtx := true }
                                                                  (PExpr.toExpr pbody) fuelBody = .ok result3 := by
                                                              simpa [ctxBody] using htcBody
                                                            have hregBody :
                                                                result3.regime'.lookup? k = some b := by
                                                              have hkBody : ctxBody.regime.lookup? k = some b := by
                                                                simpa [ctxBody] using hreg_fun
                                                              exact
                                                                ih fuelBody (by omega)
                                                                  ctxBody (PExpr.toExpr pbody) pbody result3
                                                                  hpeBody htcBody' k b hkBody
                                                            have hrReg :
                                                                r.regime' = result3.regime' := by
                                                              cases hq3 : result3.qualType with
                                                              | mk et3 p3 pred3 =>
                                                                  simp [hq3] at happly
                                                                  have hrEq :
                                                                      r =
                                                                        { result3 with
                                                                          qualType :=
                                                                            normalizeAppResultByProvenance (joinPoison p1r p)
                                                                              { result3.qualType with
                                                                                poison := joinPoison p1r
                                                                                  (joinPoison p result3.qualType.poison) } } := by
                                                                    simpa [hq3] using happly.symm
                                                                  simp [hrEq]
                                                            simpa [hrReg] using hregBody
                                            | extern x retSpec capturedEnv =>
                                                have hregEq := applyPFnTClosure_extern_regime_eq
                                                  _ _ _ _ _ _ _ _ result1 r fuelApp x retSpec capturedEnv happly
                                                rw [hregEq]
                                                exact hreg_fun
                                          have hfirstReg : first.regime'.lookup? k = some b :=
                                            hres_reg first (by simp)
                                          have hrestReg : ∀ r ∈ rest, r.regime'.lookup? k = some b := by
                                            intro r hr
                                            exact hres_reg r (List.mem_cons_of_mem _ hr)
                                          exact
                                            joinTypeResults_regime_lookup_of_all
                                              ({ ctx with pureCtx := true }) first rest res hjoin k b hfirstReg hrestReg
      case ite e1 e2 e3 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                cases hpe3 : Expr.toPExpr? e3 with
                | none =>
                    simp [hpe1, hpe2, hpe3] at hpe
                | some pe3 =>
                    have htcIf :
                        typecheckIf { ctx with pureCtx := true } e1 e2 e3 fuel' = .ok res := by
                      simpa [typecheckExpr] using htc
                    rcases typecheckIf_structure { ctx with pureCtx := true } e1 e2 e3 fuel' res htcIf with
                      htrue | hfalse | hstd
                    · rcases htrue with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, res2, _res3, htc2, _htc3,
                         _h_mem, _h_tag, _h_loc, _h_ntag, h_regime, _h_poison, _h_etyp⟩
                      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨true, deps⟩ }
                      have htc2' :
                          typecheckExpr { ctxTrue with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctxTrue] using htc2
                      have hk2 : ctxTrue.regime.lookup? k = some b := by
                        simpa [ctxTrue] using hk
                      have hreg2 :
                          res2.regime'.lookup? k = some b :=
                        ih (fuel' - 1) hltSub ctxTrue e2 pe2 res2 hpe2 htc2' k b hk2
                      simpa [h_regime] using hreg2
                    · rcases hfalse with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, _res2, res3, _htc2, htc3,
                         _h_mem, _h_tag, _h_loc, _h_ntag, h_regime, _h_poison, _h_etyp⟩
                      let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨false, deps⟩,
                                                               nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
                      have htc3' :
                          typecheckExpr { ctxFalse with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctxFalse] using htc3
                      have hk3 : ctxFalse.regime.lookup? k = some b := by
                        simpa [ctxFalse] using hk
                      have hreg3 :
                          res3.regime'.lookup? k = some b :=
                        ih (fuel' - 1) hltSub ctxFalse e3 pe3 res3 hpe3 htc3' k b hk3
                      simpa [h_regime] using hreg3
                    · rcases hstd with
                        ⟨_h_std_case, res1, htc1, _hbool, res2, hstd_tail⟩
                      simp at hstd_tail
                      rcases hstd_tail with ⟨htc2, res3, hstd_tail'⟩
                      rcases hstd_tail' with
                        ⟨htc3, _h_mem, _h_tag, _h_loc, _h_ntag, h_regime, _h_poison, _h_etyp, _h_pred⟩
                      let ctx2 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      let ctx3 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res2.nextLoc'
                          nextTag := res2.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      have htc1' :
                          typecheckExpr { ctx with pureCtx := true } e1 (fuel' - 1) = .ok res1 := by
                        simpa using htc1
                      have hreg1 :
                          res1.regime'.lookup? k = some b :=
                        ih (fuel' - 1) hltSub ctx e1 pe1 res1 hpe1 htc1' k b hk
                      have htc2' :
                          typecheckExpr { ctx2 with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctx2] using htc2
                      have htc3' :
                          typecheckExpr { ctx3 with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctx3] using htc3
                      have hk2 : ctx2.regime.lookup? k = some b := by
                        simpa [ctx2] using hreg1
                      have hk3 : ctx3.regime.lookup? k = some b := by
                        simpa [ctx3] using hreg1
                      have hreg2 :
                          res2.regime'.lookup? k = some b :=
                        ih (fuel' - 1) hltSub ctx2 e2 pe2 res2 hpe2 htc2' k b hk2
                      have hreg3 :
                          res3.regime'.lookup? k = some b :=
                        ih (fuel' - 1) hltSub ctx3 e3 pe3 res3 hpe3 htc3' k b hk3
                      have hjoinReg :
                          (joinRegimes res2.regime' res3.regime').lookup? k = some b :=
                        joinRegimes_lookup_of_some_some res2.regime' res3.regime' k b hreg2 hreg3
                      simpa [h_regime] using hjoinReg
      case unaryop op e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcUnary :
                typecheckUnaryOp { ctx with pureCtx := true } op e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckUnaryOp_structure { ctx with pureCtx := true } op e1 fuel' res htcUnary with
              ⟨result1, _result_etyp, htc1, _h_op, _h_mem, _h_tag, _h_loc, _h_ntag, h_regime, _h_ret_etyp,
                _h_ret_poison, _h_ret_pred⟩
            have hreg1 :
                result1.regime'.lookup? k = some b :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 k b hk
            simpa [h_regime] using hreg1


lemma typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ l qt,
      ctx.memEnv.lookup l = some qt →
      res.memEnv'.lookup l = some qt := by
  classical
  revert ctx e pe res hpe htc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e pe res hpe htc l qt hlookup
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e <;> try (simp [Expr.toPExpr?] at hpe)
      case num n =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case bool b =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case unit =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case str s =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case var x =>
        have htcVar : typecheckVar { ctx with pureCtx := true } x = .ok res := by
          simpa [typecheckExpr] using htc
        have hmem :
            res.memEnv' = ({ ctx with pureCtx := true }).memEnv :=
          typecheckVar_preserves_memEnv { ctx with pureCtx := true } x res htcVar
        simpa [hmem] using hlookup
      case op e1 op e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcOp :
                    typecheckOp { ctx with pureCtx := true } e1 e2 fuel' op = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckOp_structure { ctx with pureCtx := true } e1 e2 op fuel' res htcOp with
                  ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
                have hlookup1 :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt hlookup
                have htc2' :
                    typecheckExpr
                        { updateCtxFromResult { ctx with pureCtx := true } result1 with pureCtx := true }
                        e2 (fuel' - 1) = .ok result2 := by
                  simpa [updateCtxFromResult] using htc2
                have hlookupCtx2 :
                    (updateCtxFromResult { ctx with pureCtx := true } result1).memEnv.lookup l = some qt := by
                  simpa [updateCtxFromResult] using hlookup1
                have hlookup2 :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub
                    (updateCtxFromResult { ctx with pureCtx := true } result1)
                    e2 pe2 result2 hpe2 htc2' l qt hlookupCtx2
                simpa [h_mem] using hlookup2
      case deref e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcD :
                typecheckDeref { ctx with pureCtx := true } e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckDeref_structure { ctx with pureCtx := true } e1 fuel' res htcD with
              ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime⟩
            have hlookup1 :
                result1.memEnv'.lookup l = some qt :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt hlookup
            simpa [h_mem] using hlookup1
      case vlet x e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcVlet :
                    typecheckVlet { ctx with pureCtx := true } x e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckVlet_structure { ctx with pureCtx := true } x e1 e2 fuel' res htcVlet with
                  ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_poison, _h_ret_pred⟩
                have hlookup1 :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt hlookup
                have htc2' :
                    typecheckExpr { ctx' with pureCtx := true } e2 (fuel' - 1) = .ok result2 := by
                  simpa [hctx'] using htc2
                have hlookupCtx' : ctx'.memEnv.lookup l = some qt := by
                  simpa [hctx'] using hlookup1
                have hlookup2 :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx' e2 pe2 result2 hpe2 htc2' l qt hlookupCtx'
                simpa [h_mem] using hlookup2
      case app e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcApp :
                    typecheckApp { ctx with pureCtx := true } e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckApp_structure { ctx with pureCtx := true } e1 e2 fuel' res htcApp with
                  ⟨result2, result1, st1, st2, p, p1, _isArrow, htc2, htc1, hcases⟩
                have hlookup_arg :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e2 pe2 result2 hpe2 htc2 l qt hlookup
                let ctxFun :
                    TypeContext :=
                  { ctx with
                    memEnv := result2.memEnv'
                    tagEnv := result2.tagEnv'
                    nextLoc := result2.nextLoc'
                    nextTag := result2.nextTag'
                    regime := result2.regime' }
                have htc1' :
                    typecheckExpr { ctxFun with pureCtx := true } e1 (fuel' - 1) = .ok result1 := by
                  simpa [ctxFun] using htc1
                have hlookupFunCtx : ctxFun.memEnv.lookup l = some qt := by
                  simpa [ctxFun] using hlookup_arg
                have hlookup_fun :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctxFun e1 pe1 result1 hpe1 htc1' l qt hlookupFunCtx
                cases hcases with
                | inl harrow =>
                    rcases harrow with ⟨_hisArrow, _hArrow, _hp1eq, hnotPure, _hsubtype⟩
                    simp at hnotPure
                | inr hparrow =>
                    rcases hparrow with
                      ⟨_hisArrowFalse, ⟨tcls, het1⟩, _hp1eq, hsubtype⟩
                    cases hq2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                        cases fuel' with
                        | zero =>
                            simp [typecheckApp] at htcApp
                        | succ fuelApp =>
                            have htc2' :
                                typecheckExpr { ctx with pureCtx := true } e2 fuelApp = .ok result2 := by
                              simpa using htc2
                            have htc1'' :
                                typecheckExpr { ctxFun with pureCtx := true } e1 fuelApp = .ok result1 := by
                              simpa [ctxFun] using htc1
                            have htcApp' := htcApp
                            unfold typecheckApp at htcApp'
                            simp [bind, Except.bind, htc2', hq2] at htcApp'
                            erw [htc1''] at htcApp'
                            cases hq1 : result1.qualType with
                            | mk et1 p1r pred1 =>
                                have het1' : et1 = ETyp.parrow st1 st2 p tcls := by
                                  simpa [hq1] using het1
                                have hp1r : p1r = p1 := by
                                  simpa [hq1] using _hp1eq
                                simp [hq1] at htcApp'
                                rw [het1'] at htcApp'
                                simp at htcApp'
                                by_cases htclsNil : tcls = []
                                · simp [htclsNil] at htcApp'
                                · have hsubtype' : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                                    simpa [hq2] using hsubtype
                                  simp [htclsNil, hsubtype'] at htcApp'
                                  cases hmap :
                                      List.mapM
                                        (fun tcl =>
                                          applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                            { ctx with pureCtx := true } result1 fuelApp)
                                        tcls with
                                  | error err =>
                                      simp [hmap] at htcApp'
                                      cases htcApp'
                                  | ok results =>
                                      cases results with
                                      | nil =>
                                          simp [hmap] at htcApp'
                                          cases htcApp'
                                      | cons first rest =>
                                          simp [hmap] at htcApp'
                                          have hjoin :
                                              joinTypeResults { ctx with pureCtx := true } first rest = .ok res := by
                                            exact htcApp'
                                          have hforall2 :
                                              List.Forall₂
                                                (fun tcl r =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                tcls (first :: rest) := by
                                            exact
                                              List.mapM_Except_ok_implies_forall2 tcls
                                                (fun tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp)
                                                (first :: rest) (by simp [hmap])
                                          have hres_mem :
                                              ∀ r ∈ (first :: rest), r.memEnv'.lookup l = some qt := by
                                            intro r hr
                                            have hflip :
                                                List.Forall₂
                                                  (fun r tcl =>
                                                    applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                      { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                  (first :: rest) tcls :=
                                              List.Forall₂.flip hforall2
                                            rcases List.Forall2.exists_of_mem_left
                                                (R := fun r tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                hflip r hr with
                                              ⟨tcl, _htclMem, happly⟩
                                            cases tcl with
                                            | regular x pbody env =>
                                                cases fuelApp with
                                                | zero =>
                                                    simp [applyPFnTClosure] at happly
                                                | succ fuelBody =>
                                                    unfold applyPFnTClosure at happly
                                                    simp [bind, Except.bind] at happly
                                                    cases htcBody :
                                                        typecheckExpr
                                                          { { ctx with pureCtx := true } with
                                                            pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                            memEnv := result1.memEnv'
                                                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                            tagEnv := result1.tagEnv'
                                                            pureCtx := true
                                                            nextTag := result1.nextTag'
                                                            nextLoc := result1.nextLoc'
                                                            regime := result1.regime' }
                                                          (PExpr.toExpr pbody) fuelBody with
                                                    | error err =>
                                                        simp [htcBody] at happly
                                                    | ok result3 =>
                                                        simp [htcBody] at happly
                                                        cases hsubBodyRet : isSubtype st2 result3.qualType with
                                                        | false =>
                                                            cases hq3 : result3.qualType with
                                                            | mk et3 p3 pred3 =>
                                                                have hsubBodyRet' :
                                                                    isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                                                                  simpa [hq3] using hsubBodyRet
                                                                have hcontra : False := by
                                                                  simp [hsubBodyRet', hq3] at happly
                                                                exact False.elim hcontra
                                                        | true =>
                                                            simp [hsubBodyRet, pure, Except.pure] at happly
                                                            let ctxBody :
                                                                TypeContext :=
                                                              { { ctx with pureCtx := true } with
                                                                pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                                memEnv := result1.memEnv'
                                                                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                    ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                                tagEnv := result1.tagEnv'
                                                                pureCtx := true
                                                                nextTag := result1.nextTag'
                                                                nextLoc := result1.nextLoc'
                                                                regime := result1.regime' }
                                                            have hpeBody :
                                                                Expr.toPExpr? (PExpr.toExpr pbody) = some pbody := by
                                                              simpa using toExpr_toPExpr? pbody
                                                            have htcBody' :
                                                                typecheckExpr { ctxBody with pureCtx := true }
                                                                  (PExpr.toExpr pbody) fuelBody = .ok result3 := by
                                                              simpa [ctxBody] using htcBody
                                                            have hlookupBodyCtx : ctxBody.memEnv.lookup l = some qt := by
                                                              simpa [ctxBody] using hlookup_fun
                                                            have hlookupBody :
                                                                result3.memEnv'.lookup l = some qt :=
                                                              ih fuelBody (by omega)
                                                                ctxBody (PExpr.toExpr pbody) pbody result3
                                                                hpeBody htcBody' l qt hlookupBodyCtx
                                                            have hrMem :
                                                                r.memEnv' = result3.memEnv' := by
                                                              cases hq3 : result3.qualType with
                                                              | mk et3 p3 pred3 =>
                                                                  simp [hq3] at happly
                                                                  have hrEq :
                                                                      r =
                                                                        { result3 with
                                                                          qualType :=
                                                                            normalizeAppResultByProvenance (joinPoison p1r p)
                                                                              { result3.qualType with
                                                                                poison := joinPoison p1r
                                                                                  (joinPoison p result3.qualType.poison) } } := by
                                                                    simpa [hq3] using happly.symm
                                                                  simp [hrEq]
                                                            simpa [hrMem] using hlookupBody
                                            | extern x retSpec capturedEnv =>
                                                have hmemEq := applyPFnTClosure_extern_memEnv_eq
                                                  _ _ _ _ _ _ _ _ result1 r fuelApp x retSpec capturedEnv happly
                                                rw [hmemEq]
                                                exact hlookup_fun
                                          have hfirstMem : first.memEnv'.lookup l = some qt :=
                                            hres_mem first (by simp)
                                          have hrestMem : ∀ r ∈ rest, r.memEnv'.lookup l = some qt := by
                                            intro r hr
                                            exact hres_mem r (List.mem_cons_of_mem _ hr)
                                          exact
                                            joinTypeResults_mem_lookup_of_all
                                              ({ ctx with pureCtx := true }) first rest res hjoin l qt hfirstMem hrestMem
      case ite e1 e2 e3 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                cases hpe3 : Expr.toPExpr? e3 with
                | none =>
                    simp [hpe1, hpe2, hpe3] at hpe
                | some pe3 =>
                    have htcIf :
                        typecheckIf { ctx with pureCtx := true } e1 e2 e3 fuel' = .ok res := by
                      simpa [typecheckExpr] using htc
                    rcases typecheckIf_structure { ctx with pureCtx := true } e1 e2 e3 fuel' res htcIf with
                      htrue | hfalse | hstd
                    · rcases htrue with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, res2, _res3, htc2, _htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨true, deps⟩ }
                      have htc2' :
                          typecheckExpr { ctxTrue with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctxTrue] using htc2
                      have hlookupCtxTrue : ctxTrue.memEnv.lookup l = some qt := by
                        simpa [ctxTrue] using hlookup
                      have hlookup2 :
                          res2.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctxTrue e2 pe2 res2 hpe2 htc2' l qt hlookupCtxTrue
                      simpa [h_mem] using hlookup2
                    · rcases hfalse with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, _res2, res3, _htc2, htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨false, deps⟩,
                                                               nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
                      have htc3' :
                          typecheckExpr { ctxFalse with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctxFalse] using htc3
                      have hlookupCtxFalse : ctxFalse.memEnv.lookup l = some qt := by
                        simpa [ctxFalse] using hlookup
                      have hlookup3 :
                          res3.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctxFalse e3 pe3 res3 hpe3 htc3' l qt hlookupCtxFalse
                      simpa [h_mem] using hlookup3
                    · rcases hstd with
                        ⟨_h_std_case, res1, htc1, _hbool, res2, hstd_tail⟩
                      simp at hstd_tail
                      rcases hstd_tail with ⟨htc2, res3, hstd_tail'⟩
                      rcases hstd_tail' with
                        ⟨htc3, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp, _h_pred⟩
                      let ctx2 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      let ctx3 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res2.nextLoc'
                          nextTag := res2.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      have htc1' :
                          typecheckExpr { ctx with pureCtx := true } e1 (fuel' - 1) = .ok res1 := by
                        simpa using htc1
                      have hlookup1 :
                          res1.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx e1 pe1 res1 hpe1 htc1' l qt hlookup
                      have htc2' :
                          typecheckExpr { ctx2 with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctx2] using htc2
                      have htc3' :
                          typecheckExpr { ctx3 with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctx3] using htc3
                      have hlookupCtx2 : ctx2.memEnv.lookup l = some qt := by
                        simpa [ctx2] using hlookup1
                      have hlookupCtx3 : ctx3.memEnv.lookup l = some qt := by
                        simpa [ctx3] using hlookup1
                      have hlookup2 :
                          res2.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx2 e2 pe2 res2 hpe2 htc2' l qt hlookupCtx2
                      have hlookup3 :
                          res3.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx3 e3 pe3 res3 hpe3 htc3' l qt hlookupCtx3
                      have hjoinMem :
                          (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt :=
                        joinMemEnvsStrong_lookup_of_some_some res2.memEnv' res3.memEnv' l qt hlookup2 hlookup3
                      simpa [h_mem] using hjoinMem
      case unaryop op e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcUnary :
                typecheckUnaryOp { ctx with pureCtx := true } op e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckUnaryOp_structure { ctx with pureCtx := true } op e1 fuel' res htcUnary with
              ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_ret_etyp,
                _h_ret_poison, _h_ret_pred⟩
            have hlookup1 :
                result1.memEnv'.lookup l = some qt :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt hlookup
            simpa [h_mem] using hlookup1

lemma typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ l qt k,
      ctx.memEnv.lookup l = some qt →
      qtypGuardTag qt = some k →
      ctx.regime.lookup? k ≠ none →
      res.memEnv'.lookup l = some qt := by
  classical
  revert ctx e pe res hpe htc
  refine Nat.strong_induction_on fuel ?_
  intro fuel ih ctx e pe res hpe htc l qt k hlookup hguard hRdef
  cases fuel with
  | zero =>
      simp [typecheckExpr] at htc
  | succ fuel' =>
      have hltSub : fuel' - 1 < Nat.succ fuel' := by
        exact Nat.lt_succ_of_le (Nat.sub_le fuel' 1)
      cases e <;> try (simp [Expr.toPExpr?] at hpe)
      case num n =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case bool b =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case unit =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case str s =>
        simp [typecheckExpr] at htc
        cases htc
        simpa using hlookup
      case var x =>
        have htcVar : typecheckVar { ctx with pureCtx := true } x = .ok res := by
          simpa [typecheckExpr] using htc
        have hmem :
            res.memEnv' = ({ ctx with pureCtx := true }).memEnv :=
          typecheckVar_preserves_memEnv { ctx with pureCtx := true } x res htcVar
        simpa [hmem] using hlookup
      case op e1 op e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcOp :
                    typecheckOp { ctx with pureCtx := true } e1 e2 fuel' op = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckOp_structure { ctx with pureCtx := true } e1 e2 op fuel' res htcOp with
                  ⟨result1, result2, _result_etyp, htc1, htc2, _h_op, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_etyp, _h_ret_poison, _h_ret_pred⟩
                have hlookup1 :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt k hlookup hguard hRdef
                have ⟨b, hkctx⟩ : ∃ b, ctx.regime.lookup? k = some b :=
                  Option.ne_none_iff_exists'.1 hRdef
                have hreg1 :
                    result1.regime'.lookup? k = some b :=
                  typecheckExpr_pure_regime_bridge_of_toPExpr
                    (ctx := ctx) (e := e1) (pe := pe1) (fuel := fuel' - 1) (res := result1)
                    hpe1 htc1 k b hkctx
                have htc2' :
                    typecheckExpr
                        { updateCtxFromResult { ctx with pureCtx := true } result1 with pureCtx := true }
                        e2 (fuel' - 1) = .ok result2 := by
                  simpa [updateCtxFromResult] using htc2
                have hlookupCtx2 :
                    (updateCtxFromResult { ctx with pureCtx := true } result1).memEnv.lookup l = some qt := by
                  simpa [updateCtxFromResult] using hlookup1
                have hRdef2 :
                    (updateCtxFromResult { ctx with pureCtx := true } result1).regime.lookup? k ≠ none := by
                  have hk2 :
                      (updateCtxFromResult { ctx with pureCtx := true } result1).regime.lookup? k = some b := by
                    simpa [updateCtxFromResult] using hreg1
                  intro hnone
                  rw [hk2] at hnone
                  contradiction
                have hlookup2 :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub
                    (updateCtxFromResult { ctx with pureCtx := true } result1)
                    e2 pe2 result2 hpe2 htc2' l qt k hlookupCtx2 hguard hRdef2
                simpa [h_mem] using hlookup2
      case deref e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcD :
                typecheckDeref { ctx with pureCtx := true } e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckDeref_structure { ctx with pureCtx := true } e1 fuel' res htcD with
              ⟨result1, htc1, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime⟩
            have hlookup1 :
                result1.memEnv'.lookup l = some qt :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt k hlookup hguard hRdef
            simpa [h_mem] using hlookup1
      case vlet x e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcVlet :
                    typecheckVlet { ctx with pureCtx := true } x e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckVlet_structure { ctx with pureCtx := true } x e1 e2 fuel' res htcVlet with
                  ⟨result1, result2, ctx', htc1, hctx', htc2, _h_ret_etyp, h_mem, _h_tag, _h_loc, _h_ntag,
                    _h_regime, _h_ret_poison, _h_ret_pred⟩
                have hlookup1 :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt k hlookup hguard hRdef
                have ⟨b, hkctx⟩ : ∃ b, ctx.regime.lookup? k = some b :=
                  Option.ne_none_iff_exists'.1 hRdef
                have hreg1 :
                    result1.regime'.lookup? k = some b :=
                  typecheckExpr_pure_regime_bridge_of_toPExpr
                    (ctx := ctx) (e := e1) (pe := pe1) (fuel := fuel' - 1) (res := result1)
                    hpe1 htc1 k b hkctx
                have htc2' :
                    typecheckExpr { ctx' with pureCtx := true } e2 (fuel' - 1) = .ok result2 := by
                  simpa [hctx'] using htc2
                have hlookupCtx' : ctx'.memEnv.lookup l = some qt := by
                  simpa [hctx'] using hlookup1
                have hRdef' : ctx'.regime.lookup? k ≠ none := by
                  have hk2 : ctx'.regime.lookup? k = some b := by
                    simpa [hctx'] using hreg1
                  intro hnone
                  rw [hk2] at hnone
                  contradiction
                have hlookup2 :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx' e2 pe2 result2 hpe2 htc2' l qt k hlookupCtx' hguard hRdef'
                simpa [h_mem] using hlookup2
      case app e1 e2 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                have htcApp :
                    typecheckApp { ctx with pureCtx := true } e1 e2 fuel' = .ok res := by
                  simpa [typecheckExpr] using htc
                rcases typecheckApp_structure { ctx with pureCtx := true } e1 e2 fuel' res htcApp with
                  ⟨result2, result1, st1, st2, p, p1, _isArrow, htc2, htc1, hcases⟩
                have hlookup_arg :
                    result2.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctx e2 pe2 result2 hpe2 htc2 l qt k hlookup hguard hRdef
                have ⟨b, hkctx⟩ : ∃ b, ctx.regime.lookup? k = some b :=
                  Option.ne_none_iff_exists'.1 hRdef
                have hreg_arg :
                    result2.regime'.lookup? k = some b :=
                  typecheckExpr_pure_regime_bridge_of_toPExpr
                    (ctx := ctx) (e := e2) (pe := pe2) (fuel := fuel' - 1) (res := result2)
                    hpe2 htc2 k b hkctx
                let ctxFun :
                    TypeContext :=
                  { ctx with
                    memEnv := result2.memEnv'
                    tagEnv := result2.tagEnv'
                    nextLoc := result2.nextLoc'
                    nextTag := result2.nextTag'
                    regime := result2.regime' }
                have htc1' :
                    typecheckExpr { ctxFun with pureCtx := true } e1 (fuel' - 1) = .ok result1 := by
                  simpa [ctxFun] using htc1
                have hkFun : ctxFun.regime.lookup? k = some b := by
                  simpa [ctxFun] using hreg_arg
                have hRdefFun : ctxFun.regime.lookup? k ≠ none := by
                  intro hnone
                  rw [hkFun] at hnone
                  contradiction
                have hlookupFunCtx : ctxFun.memEnv.lookup l = some qt := by
                  simpa [ctxFun] using hlookup_arg
                have hlookup_fun :
                    result1.memEnv'.lookup l = some qt :=
                  ih (fuel' - 1) hltSub ctxFun e1 pe1 result1 hpe1 htc1' l qt k hlookupFunCtx hguard hRdefFun
                have hreg_fun :
                    result1.regime'.lookup? k = some b :=
                  typecheckExpr_pure_regime_bridge_of_toPExpr
                    (ctx := ctxFun) (e := e1) (pe := pe1) (fuel := fuel' - 1) (res := result1)
                    hpe1 htc1' k b hkFun
                cases hcases with
                | inl harrow =>
                    rcases harrow with ⟨_hisArrow, _hArrow, _hp1eq, hnotPure, _hsubtype⟩
                    simp at hnotPure
                | inr hparrow =>
                    rcases hparrow with
                      ⟨_hisArrowFalse, ⟨tcls, het1⟩, _hp1eq, hsubtype⟩
                    cases hq2 : result2.qualType with
                    | mk etyp2 p2 pred2 =>
                        cases fuel' with
                        | zero =>
                            simp [typecheckApp] at htcApp
                        | succ fuelApp =>
                            have htc2' :
                                typecheckExpr { ctx with pureCtx := true } e2 fuelApp = .ok result2 := by
                              simpa using htc2
                            have htc1'' :
                                typecheckExpr { ctxFun with pureCtx := true } e1 fuelApp = .ok result1 := by
                              simpa [ctxFun] using htc1
                            have htcApp' := htcApp
                            unfold typecheckApp at htcApp'
                            simp [bind, Except.bind, htc2', hq2] at htcApp'
                            erw [htc1''] at htcApp'
                            cases hq1 : result1.qualType with
                            | mk et1 p1r pred1 =>
                                have het1' : et1 = ETyp.parrow st1 st2 p tcls := by
                                  simpa [hq1] using het1
                                have hp1r : p1r = p1 := by
                                  simpa [hq1] using _hp1eq
                                simp [hq1] at htcApp'
                                rw [het1'] at htcApp'
                                simp at htcApp'
                                by_cases htclsNil : tcls = []
                                · simp [htclsNil] at htcApp'
                                · have hsubtype' : isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } = true := by
                                    simpa [hq2] using hsubtype
                                  simp [htclsNil, hsubtype'] at htcApp'
                                  cases hmap :
                                      List.mapM
                                        (fun tcl =>
                                          applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                            { ctx with pureCtx := true } result1 fuelApp)
                                        tcls with
                                  | error err =>
                                      simp [hmap] at htcApp'
                                      cases htcApp'
                                  | ok results =>
                                      cases results with
                                      | nil =>
                                          simp [hmap] at htcApp'
                                          cases htcApp'
                                      | cons first rest =>
                                          simp [hmap] at htcApp'
                                          have hjoin :
                                              joinTypeResults { ctx with pureCtx := true } first rest = .ok res := by
                                            exact htcApp'
                                          have hforall2 :
                                              List.Forall₂
                                                (fun tcl r =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                tcls (first :: rest) := by
                                            exact
                                              List.mapM_Except_ok_implies_forall2 tcls
                                                (fun tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp)
                                                (first :: rest) (by simp [hmap])
                                          have hres_mem :
                                              ∀ r ∈ (first :: rest), r.memEnv'.lookup l = some qt := by
                                            intro r hr
                                            have hflip :
                                                List.Forall₂
                                                  (fun r tcl =>
                                                    applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                      { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                  (first :: rest) tcls :=
                                              List.Forall₂.flip hforall2
                                            rcases List.Forall2.exists_of_mem_left
                                                (R := fun r tcl =>
                                                  applyPFnTClosure tcl st1 st2 p p1r etyp2 p2 pred2
                                                    { ctx with pureCtx := true } result1 fuelApp = .ok r)
                                                hflip r hr with
                                              ⟨tcl, _htclMem, happly⟩
                                            cases tcl with
                                            | regular x pbody env =>
                                                cases fuelApp with
                                                | zero =>
                                                    simp [applyPFnTClosure] at happly
                                                | succ fuelBody =>
                                                    unfold applyPFnTClosure at happly
                                                    simp [bind, Except.bind] at happly
                                                    cases htcBody :
                                                        typecheckExpr
                                                          { { ctx with pureCtx := true } with
                                                            pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                            memEnv := result1.memEnv'
                                                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                            tagEnv := result1.tagEnv'
                                                            pureCtx := true
                                                            nextTag := result1.nextTag'
                                                            nextLoc := result1.nextLoc'
                                                            regime := result1.regime' }
                                                          (PExpr.toExpr pbody) fuelBody with
                                                    | error err =>
                                                        simp [htcBody] at happly
                                                    | ok result3 =>
                                                        simp [htcBody] at happly
                                                        cases hsubBodyRet : isSubtype st2 result3.qualType with
                                                        | false =>
                                                            cases hq3 : result3.qualType with
                                                            | mk et3 p3 pred3 =>
                                                                have hsubBodyRet' :
                                                                    isSubtype st2 { etyp := et3, poison := p3, pred := pred3 } = false := by
                                                                  simpa [hq3] using hsubBodyRet
                                                                have hcontra : False := by
                                                                  simp [hsubBodyRet', hq3] at happly
                                                                exact False.elim hcontra
                                                        | true =>
                                                            simp [hsubBodyRet, pure, Except.pure] at happly
                                                            let ctxBody :
                                                                TypeContext :=
                                                              { { ctx with pureCtx := true } with
                                                                pc := joinPoison p (joinPoison ({ ctx with pureCtx := true }).pc p1r)
                                                                memEnv := result1.memEnv'
                                                                varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                                                    ⟨etyp2, joinPoison ({ ctx with pureCtx := true }).pc p2, pred2⟩
                                                                tagEnv := result1.tagEnv'
                                                                pureCtx := true
                                                                nextTag := result1.nextTag'
                                                                nextLoc := result1.nextLoc'
                                                                regime := result1.regime' }
                                                            have hpeBody :
                                                                Expr.toPExpr? (PExpr.toExpr pbody) = some pbody := by
                                                              simpa using toExpr_toPExpr? pbody
                                                            have htcBody' :
                                                                typecheckExpr { ctxBody with pureCtx := true }
                                                                  (PExpr.toExpr pbody) fuelBody = .ok result3 := by
                                                              simpa [ctxBody] using htcBody
                                                            have hlookupBodyCtx : ctxBody.memEnv.lookup l = some qt := by
                                                              simpa [ctxBody] using hlookup_fun
                                                            have hRdefBody : ctxBody.regime.lookup? k ≠ none := by
                                                              have hkBody : ctxBody.regime.lookup? k = some b := by
                                                                simpa [ctxBody] using hreg_fun
                                                              intro hnone
                                                              rw [hkBody] at hnone
                                                              contradiction
                                                            have hlookupBody :
                                                                result3.memEnv'.lookup l = some qt :=
                                                              ih fuelBody (by omega)
                                                                ctxBody (PExpr.toExpr pbody) pbody result3
                                                                hpeBody htcBody' l qt k hlookupBodyCtx hguard hRdefBody
                                                            have hrMem :
                                                                r.memEnv' = result3.memEnv' := by
                                                              cases hq3 : result3.qualType with
                                                              | mk et3 p3 pred3 =>
                                                                  simp [hq3] at happly
                                                                  have hrEq :
                                                                      r =
                                                                        { result3 with
                                                                          qualType :=
                                                                            normalizeAppResultByProvenance (joinPoison p1r p)
                                                                              { result3.qualType with
                                                                                poison := joinPoison p1r
                                                                                  (joinPoison p result3.qualType.poison) } } := by
                                                                    simpa [hq3] using happly.symm
                                                                  simp [hrEq]
                                                            simpa [hrMem] using hlookupBody
                                            | extern x retSpec capturedEnv =>
                                                have hmemEq := applyPFnTClosure_extern_memEnv_eq
                                                  _ _ _ _ _ _ _ _ result1 r fuelApp x retSpec capturedEnv happly
                                                rw [hmemEq]
                                                exact hlookup_fun
                                          have hfirstMem : first.memEnv'.lookup l = some qt :=
                                            hres_mem first (by simp)
                                          have hrestMem : ∀ r ∈ rest, r.memEnv'.lookup l = some qt := by
                                            intro r hr
                                            exact hres_mem r (List.mem_cons_of_mem _ hr)
                                          exact
                                            joinTypeResults_mem_lookup_of_all
                                              ({ ctx with pureCtx := true }) first rest res hjoin l qt hfirstMem hrestMem
      case ite e1 e2 e3 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            cases hpe2 : Expr.toPExpr? e2 with
            | none =>
                simp [hpe1, hpe2] at hpe
            | some pe2 =>
                cases hpe3 : Expr.toPExpr? e3 with
                | none =>
                    simp [hpe1, hpe2, hpe3] at hpe
                | some pe3 =>
                    have htcIf :
                        typecheckIf { ctx with pureCtx := true } e1 e2 e3 fuel' = .ok res := by
                      simpa [typecheckExpr] using htc
                    rcases typecheckIf_structure { ctx with pureCtx := true } e1 e2 e3 fuel' res htcIf with
                      htrue | hfalse | hstd
                    · rcases htrue with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, res2, _res3, htc2, _htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨true, deps⟩ }
                      have htc2' :
                          typecheckExpr { ctxTrue with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctxTrue] using htc2
                      have hlookupCtxTrue : ctxTrue.memEnv.lookup l = some qt := by
                        simpa [ctxTrue] using hlookup
                      have hRdefTrue : ctxTrue.regime.lookup? k ≠ none := by
                        simpa [ctxTrue] using hRdef
                      have hlookup2 :
                          res2.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctxTrue e2 pe2 res2 hpe2 htc2' l qt k hlookupCtxTrue hguard hRdefTrue
                      simpa [h_mem] using hlookup2
                    · rcases hfalse with
                        ⟨k', deps, _hmatch, _hreg, _res1, _htc1, _hbool, _res2, res3, _htc2, htc3,
                         h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp⟩
                      let ctxFalse : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k' ⟨false, deps⟩,
                                                               nextLoc := _res2.nextLoc', nextTag := _res2.nextTag' }
                      have htc3' :
                          typecheckExpr { ctxFalse with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctxFalse] using htc3
                      have hlookupCtxFalse : ctxFalse.memEnv.lookup l = some qt := by
                        simpa [ctxFalse] using hlookup
                      have hRdefFalse : ctxFalse.regime.lookup? k ≠ none := by
                        simpa [ctxFalse] using hRdef
                      have hlookup3 :
                          res3.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctxFalse e3 pe3 res3 hpe3 htc3' l qt k hlookupCtxFalse hguard hRdefFalse
                      simpa [h_mem] using hlookup3
                    · rcases hstd with
                        ⟨_h_std_case, res1, htc1, _hbool, res2, hstd_tail⟩
                      simp at hstd_tail
                      rcases hstd_tail with ⟨htc2, res3, hstd_tail'⟩
                      rcases hstd_tail' with
                        ⟨htc3, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_poison, _h_etyp, _h_pred⟩
                      let ctx2 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res1.nextLoc'
                          nextTag := res1.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      let ctx3 :
                          TypeContext :=
                        { ctx with
                          memEnv := res1.memEnv'
                          tagEnv := res1.tagEnv'
                          nextLoc := res2.nextLoc'
                          nextTag := res2.nextTag'
                          regime := res1.regime'
                          pc := joinPoison ctx.pc res1.qualType.poison }
                      have htc1' :
                          typecheckExpr { ctx with pureCtx := true } e1 (fuel' - 1) = .ok res1 := by
                        simpa using htc1
                      have hlookup1 :
                          res1.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx e1 pe1 res1 hpe1 htc1' l qt k hlookup hguard hRdef
                      have ⟨b, hkctx⟩ : ∃ b, ctx.regime.lookup? k = some b :=
                        Option.ne_none_iff_exists'.1 hRdef
                      have hreg1 :
                          res1.regime'.lookup? k = some b :=
                        typecheckExpr_pure_regime_bridge_of_toPExpr
                          (ctx := ctx) (e := e1) (pe := pe1) (fuel := fuel' - 1) (res := res1)
                          hpe1 htc1' k b hkctx
                      have htc2' :
                          typecheckExpr { ctx2 with pureCtx := true } e2 (fuel' - 1) = .ok res2 := by
                        simpa [ctx2] using htc2
                      have htc3' :
                          typecheckExpr { ctx3 with pureCtx := true } e3 (fuel' - 1) = .ok res3 := by
                        simpa [ctx3] using htc3
                      have hlookupCtx2 : ctx2.memEnv.lookup l = some qt := by
                        simpa [ctx2] using hlookup1
                      have hlookupCtx3 : ctx3.memEnv.lookup l = some qt := by
                        simpa [ctx3] using hlookup1
                      have hRdef2 : ctx2.regime.lookup? k ≠ none := by
                        have hk2 : ctx2.regime.lookup? k = some b := by
                          simpa [ctx2] using hreg1
                        intro hnone
                        rw [hk2] at hnone
                        contradiction
                      have hRdef3 : ctx3.regime.lookup? k ≠ none := by
                        have hk3 : ctx3.regime.lookup? k = some b := by
                          simpa [ctx3] using hreg1
                        intro hnone
                        rw [hk3] at hnone
                        contradiction
                      have hlookup2 :
                          res2.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx2 e2 pe2 res2 hpe2 htc2' l qt k hlookupCtx2 hguard hRdef2
                      have hlookup3 :
                          res3.memEnv'.lookup l = some qt :=
                        ih (fuel' - 1) hltSub ctx3 e3 pe3 res3 hpe3 htc3' l qt k hlookupCtx3 hguard hRdef3
                      have hjoinMem :
                          (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt :=
                        joinMemEnvsStrong_lookup_of_some_some res2.memEnv' res3.memEnv' l qt hlookup2 hlookup3
                      simpa [h_mem] using hjoinMem
      case unaryop op e1 =>
        cases hpe1 : Expr.toPExpr? e1 with
        | none =>
            simp [hpe1] at hpe
        | some pe1 =>
            have htcUnary :
                typecheckUnaryOp { ctx with pureCtx := true } op e1 fuel' = .ok res := by
              simpa [typecheckExpr] using htc
            rcases typecheckUnaryOp_structure { ctx with pureCtx := true } op e1 fuel' res htcUnary with
              ⟨result1, _result_etyp, htc1, _h_op, h_mem, _h_tag, _h_loc, _h_ntag, _h_regime, _h_ret_etyp,
                _h_ret_poison, _h_ret_pred⟩
            have hlookup1 :
                result1.memEnv'.lookup l = some qt :=
              ih (fuel' - 1) hltSub ctx e1 pe1 result1 hpe1 htc1 l qt k hlookup hguard hRdef
            simpa [h_mem] using hlookup1
