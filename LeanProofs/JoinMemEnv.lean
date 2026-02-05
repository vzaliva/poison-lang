-- Formal properties of the poison language: JoinMemEnv idempotency

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
import Std.Data.ExtTreeMap
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false


-- Helper lemma: eraseDups preserves membership
lemma List.mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α] {x : α} {l : List α}
    (h : x ∈ l) : x ∈ l.eraseDups := by
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
            -- From length, get strict bound for the filtered tail.
            have hlen_as : as.length < n := by
              have hlen' : as.length + 1 = n := by simpa using hlen
              have : as.length < as.length + 1 := Nat.lt_succ_self as.length
              simpa [hlen'] using this
            cases hmem with
            | head =>
                -- x = a
                simp [List.eraseDups_cons]
            | tail _ hmem_as =>
                by_cases hxa : x = a
                · subst hxa
                  simp [List.eraseDups_cons]
                · -- x ≠ a, so it survives the filter
                  have hxfilter : x ∈ as.filter (fun b => !b == a) := by
                    apply (List.mem_filter).2
                    refine ⟨hmem_as, ?_⟩
                    by_cases hbeq : x == a
                    · have : x = a := LawfulBEq.eq_of_beq (a := x) (b := a) (by simpa using hbeq)
                      exact (hxa this).elim
                    · simp [hbeq]
                  have hlen_filter : (as.filter (fun b => !b == a)).length < n := by
                    have hle : (as.filter (fun b => !b == a)).length ≤ as.length :=
                      List.length_filter_le _ _
                    exact _root_.lt_of_le_of_lt hle hlen_as
                  have hx' :
                      x ∈ (as.filter (fun b => !b == a)).eraseDups := by
                    have hIH := ih (as.filter (fun b => !b == a)).length hlen_filter
                    exact hIH (as.filter (fun b => !b == a)) rfl x hxfilter
                  rw [List.eraseDups_cons]
                  exact List.Mem.tail a hx'
  exact hP l rfl x h

private lemma joinPoison_idempotent (p : Poison) : joinPoison p p = p := by
  cases p <;> rfl

-- Idempotency of joinPredicates: joining a predicate with itself returns itself
private lemma joinPredicates_idempotent (pred : Predicate) : joinPredicates pred pred = pred := by
  simp [joinPredicates]
  -- beqPredicate pred pred = true by reflexivity
  -- Note: (pred == pred) = BEq.beq pred pred, and BEq.beq for Predicate is beqPredicate
  have h_refl : beqPredicate pred pred = true := by
    -- Use LawfulBEq instance: (pred == pred) = true
    have : LawfulBEq Predicate := inferInstance
    have h_eq : (pred == pred) = true := this.rfl
    -- Convert BEq.beq to beqPredicate using simp
    simp [BEq.beq] at h_eq
    exact h_eq
  simp [h_refl]

-- Idempotency of the joining function used in joinMemEnvs
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
    -- Need to show joinPredicates pred pred = pred (idempotency)
    have h_pred_idem : joinPredicates pred pred = pred := joinPredicates_idempotent pred
    simp [beq_iff_eq, joinPoison_idempotent, h_pred_idem]

-- The joining function returns none when both inputs are none
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


private theorem removeAll_self [BEq α] [LawfulBEq α] (l : List α) : l.removeAll l = [] := by
  simp [List.removeAll, List.filter_eq_nil_iff]

private theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
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

private lemma go_get_not_mem
  (m1 m2 : MemoryTypeEnv)
  (f : Loc → Option QTyp → Option QTyp → Option QTyp)
  (ks : List Loc) (acc : MemoryTypeEnv) (k : Loc)
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

private lemma go_get_mem
  (m1 m2 : MemoryTypeEnv)
  (f : Loc → Option QTyp → Option QTyp → Option QTyp)
  (ks : List Loc) (acc : MemoryTypeEnv) (k : Loc)
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
              · have ih' := go_get_not_mem m1 m2 f xs (acc.erase k) k hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.erase k))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep, ih']
                simp [hfx, ExtTreeMap.getElem?_erase_self]
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
              · have ih' := go_get_not_mem m1 m2 f xs (acc.insert k v) k hmem
                have hstep :
                    (combineExtTreeMaps.go m1 m2 f (k :: xs) acc)[k]? =
                      (combineExtTreeMaps.go m1 m2 f xs (acc.insert k v))[k]? := by
                  simp [combineExtTreeMaps.go, hfx']
                rw [hstep, ih']
                simp [hfx, ExtTreeMap.getElem?_insert_self]
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


-- Proofs for MemoryTypeEnv.equiv reflexivity and transitivity
namespace MemoryTypeEnv

theorem equiv.refl (m : MemoryTypeEnv) : m.equiv m := by
  simp only [equiv]
  -- (ExtTreeMap.toList m == ExtTreeMap.toList m) = true by reflexivity of BEq
  have : LawfulBEq (List (Loc × QTyp)) := inferInstance
  exact this.rfl

theorem equiv.trans (m₁ m₂ m₃ : MemoryTypeEnv) : m₁.equiv m₂ → m₂.equiv m₃ → m₁.equiv m₃ := by
  simp only [equiv]
  intro h1 h2
  -- h1: (ExtTreeMap.toList m₁ == ExtTreeMap.toList m₂) = true
  -- h2: (ExtTreeMap.toList m₂ == ExtTreeMap.toList m₃) = true
  -- Goal: (ExtTreeMap.toList m₁ == ExtTreeMap.toList m₃) = true
  -- Convert boolean equalities to Prop equalities, use transitivity, convert back
  have : LawfulBEq (List (Loc × QTyp)) := inferInstance
  have h_list_eq : ExtTreeMap.toList m₁ = ExtTreeMap.toList m₂ := this.eq_of_beq h1
  have h_list_eq2 : ExtTreeMap.toList m₂ = ExtTreeMap.toList m₃ := this.eq_of_beq h2
  have h_list_eq3 : ExtTreeMap.toList m₁ = ExtTreeMap.toList m₃ := by
    rw [h_list_eq, h_list_eq2]
  -- Convert back to boolean equality: if a = b, then (a == b) = (a == a) = true
  have h_beq_eq : (ExtTreeMap.toList m₁ == ExtTreeMap.toList m₃) = true := by
    rw [h_list_eq3]
    exact this.rfl
  exact h_beq_eq

end MemoryTypeEnv

theorem joinMemEnv_idempotent : ∀ (m m1 m2 : MemoryTypeEnv),
  m.equiv m1 → m.equiv m2 → m.equiv (joinMemEnvs m1 m2) := by
  intros m m1 m2 h1 h2
  simp only [MemoryTypeEnv.equiv]
  -- Since m.equiv m1 and m.equiv m2, we have m1.toList = m.toList and m2.toList = m.toList
  have h_list_eq1 : ExtTreeMap.toList m = ExtTreeMap.toList m1 := by
    have : LawfulBEq (List (Loc × QTyp)) := inferInstance
    exact this.eq_of_beq h1
  have h_list_eq2 : ExtTreeMap.toList m = ExtTreeMap.toList m2 := by
    have : LawfulBEq (List (Loc × QTyp)) := inferInstance
    exact this.eq_of_beq h2
  have h_list_eq12 : ExtTreeMap.toList m1 = ExtTreeMap.toList m2 := by
    rw [← h_list_eq1, h_list_eq2]
  -- Reduce to showing the join of two equal maps is equal to the map.
  have hm1m2 : m1 = m2 := (ExtTreeMap.toList_inj).1 h_list_eq12
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
      else none
    | none, none => none
  -- Rewrite the goal to compare against m1.
  rw [h_list_eq1]
  -- Show `combineExtTreeMaps` returns `m1` when both inputs are `m1`.
  have hcombine : combineExtTreeMaps m1 m1 f = m1 := by
    -- Replace the key list with `m1.keys` (since keys are nodup).
    have hkeys_nodup : m1.keys.Nodup := ExtTreeMap.nodup_keys (t := m1)
    have hkeys_erase : m1.keys.eraseDups = m1.keys :=
      eraseDups_eq_self_of_nodup (h := hkeys_nodup)
    have hks : (m1.keys ++ m1.keys).eraseDups = m1.keys := by
      simp [List.eraseDups_append, removeAll_self, hkeys_erase]
    apply ExtTreeMap.ext_getElem?
    intro k
    -- Unfold combineExtTreeMaps and normalize the key list.
    dsimp [combineExtTreeMaps]
    rw [hks]
    by_cases hmem : k ∈ m1.keys
    · -- Key is in the map domain.
      have hgo := go_get_mem m1 m1 f m1.keys ({} : MemoryTypeEnv) k hmem
      -- Simplify using idempotency of the join function on identical inputs.
      have hfun : f k (m1[k]?) (m1[k]?) = m1[k]? := by
        simpa [f] using (joinMemEnvs_func_self k (m1[k]?))
      have hgo' := hgo
      simp [hfun] at hgo'
      have hmatch : (match m1[k]? with | some v => some v | none => none) = m1[k]? := by
        cases h : m1[k]? <;> rfl
      rw [hmatch] at hgo'
      exact hgo'
    · -- Key is not in the map domain.
      have hgo := go_get_not_mem m1 m1 f m1.keys ({} : MemoryTypeEnv) k hmem
      -- From `k ∉ m1.keys`, show `m1[k]? = none`.
      have hnot_mem : k ∉ m1 := by
        intro hk
        have hk' : k ∈ m1.keys := (ExtTreeMap.mem_keys).2 hk
        exact hmem hk'
      have hm1_none : m1[k]? = none := ExtTreeMap.getElem?_eq_none hnot_mem
      simpa [hm1_none] using hgo
  -- Conclude equality on toList.
  have h_toList : ExtTreeMap.toList m1 = ExtTreeMap.toList (joinMemEnvs m1 m2) := by
    rw [← hm1m2]
    change ExtTreeMap.toList m1 = ExtTreeMap.toList (combineExtTreeMaps m1 m1 f)
    simp [hcombine]
  have : LawfulBEq (List (Loc × QTyp)) := inferInstance
  rw [h_toList]
  exact this.rfl
