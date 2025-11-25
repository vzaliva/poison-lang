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
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

private lemma joinPoison_idempotent (p : Poison) : joinPoison p p = p := by
  cases p <;> rfl

-- Idempotency of the joining function used in joinMemEnvs
private lemma joinMemEnvs_func_idempotent :
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
      | none, none => none) k (some qt) (some qt) = some qt := by
  intros k qt
  cases qt with
  | mk t p pred =>
    cases pred <;> simp [beq_iff_eq, joinPoison_idempotent]

-- The joining function returns none when both inputs are none
private lemma joinMemEnvs_func_none :
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

-- Helper lemma: go preserves lookups for keys not in the list
private lemma go_get_not_mem [BEq α] [Hashable α] [LawfulBEq α] [DecidableEq α]
  (m1 m2 : HashMap α β)
  (f : α → Option β → Option β → Option β)
  (ks : List α) (acc : HashMap α β) (k : α)
  (h_not_in : k ∉ ks) :
  (combineMaps.go m1 m2 f ks acc).get? k = acc.get? k := by
  induction ks generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      have hk_ne : k ≠ x := by
        intro heq
        subst heq
        simp at h_not_in
      have h_not_in' : k ∉ xs := by
        simp at h_not_in
        exact h_not_in.2
      unfold combineMaps.go
      cases hfx : f x (m1.get? x) (m2.get? x) with
      | none =>
          specialize ih (acc.erase x) h_not_in'
          have h_erase : (acc.erase x).get? k = acc.get? k := by
            simp [HashMap.get?_eq_getElem?, HashMap.getElem?_erase, beq_iff_eq, hk_ne.symm]
          rw [ih, h_erase]
      | some v =>
          specialize ih (acc.insert x v) h_not_in'
          have h_insert : (acc.insert x v).get? k = acc.get? k := by
            simp [HashMap.get?_eq_getElem?, HashMap.getElem?_insert, beq_iff_eq, hk_ne.symm]
          rw [ih, h_insert]

-- Helper lemma: go computes the right value for keys in the list
private lemma go_get_mem [BEq α] [Hashable α] [LawfulBEq α] [DecidableEq α]
  (m1 m2 : HashMap α β)
  (f : α → Option β → Option β → Option β)
  (ks : List α) (acc : HashMap α β) (k : α)
  (h_in : k ∈ ks)
  (h_nodup : ks.Nodup) :
  (combineMaps.go m1 m2 f ks acc).get? k =
    match f k (m1.get? k) (m2.get? k) with
    | some v => some v
    | none => none := by
  induction ks generalizing acc with
  | nil => contradiction
  | cons x xs ih =>
      simp at h_in
      rw [List.nodup_cons] at h_nodup
      cases h_in with
      | inl heq =>
          -- k = x
          unfold combineMaps.go
          have h_not_in : x ∉ xs := h_nodup.1
          cases hfx : f x (m1.get? x) (m2.get? x) with
          | none =>
              -- After processing x, we continue with xs where x ∉ xs
              simp only []
              rw [heq]  -- Change goal from k to x
              have h_go := go_get_not_mem m1 m2 f xs (acc.erase x) x h_not_in
              rw [h_go]
              have h_erase : (acc.erase x).get? x = none := by
                simp [HashMap.get?_eq_getElem?]
              rw [h_erase, hfx]
          | some v =>
              simp only []
              rw [heq]  -- Change goal from k to x
              have h_go := go_get_not_mem m1 m2 f xs (acc.insert x v) x h_not_in
              rw [h_go]
              have h_insert : (acc.insert x v).get? x = some v := by
                simp [HashMap.get?_eq_getElem?]
              rw [h_insert, hfx]
      | inr hmem =>
          -- k ∈ xs, k ≠ x
          have hk_ne : k ≠ x := by
            intro heq
            subst heq
            exact h_nodup.1 hmem
          unfold combineMaps.go
          cases hfx : f x (m1.get? x) (m2.get? x) with
          | none =>
              simp only []
              specialize ih (acc.erase x) hmem h_nodup.2
              rw [ih]
          | some v =>
              simp only []
              specialize ih (acc.insert x v) hmem h_nodup.2
              rw [ih]

private lemma combineMaps_equiv_helper [BEq α] [Hashable α] [LawfulBEq α] [DecidableEq α]
  (m m1 m2 : HashMap α β)
  (f : α → Option β → Option β → Option β)
  (h1 : HashMap.Equiv m m1)
  (h2 : HashMap.Equiv m m2)
  (f_idem : ∀ k v, f k (some v) (some v) = some v)
  (f_none : ∀ k, f k none none = none) :
  HashMap.Equiv m (combineMaps m1 m2 f) := by
  classical
  have h_equiv : HashMap.Equiv m1 m2 := HashMap.Equiv.trans h1.symm h2
  refine HashMap.Equiv.of_forall_getElem?_eq ?_
  intro k
  have hk : m1.get? k = m2.get? k := HashMap.Equiv.getElem?_eq h_equiv
  have hm1 : m.get? k = m1.get? k := HashMap.Equiv.getElem?_eq h1
  -- Convert getElem? to get? for easier reasoning
  have hm1_get : m.get? k = m1.get? k := by
    simpa [HashMap.get?_eq_getElem?] using hm1
  -- Unfold combineMaps and expose the go function
  show m[k]? = (combineMaps m1 m2 f)[k]?
  unfold combineMaps
  -- Split on whether k is in the deduplicated key list
  by_cases h_in : k ∈ (m1.keys ++ m2.keys).dedup
  · -- k is in the list
    have h_nodup : ((m1.keys ++ m2.keys).dedup).Nodup := List.nodup_dedup _
    have h_go := go_get_mem m1 m2 f ((m1.keys ++ m2.keys).dedup) ({} : HashMap α β) k h_in h_nodup
    have h_rhs : (combineMaps.go m1 m2 f ((m1.keys ++ m2.keys).dedup) ({}:HashMap α β)).get? k =
      (combineMaps.go m1 m2 f ((m1.keys ++ m2.keys).dedup) ({}:HashMap α β))[k]? := rfl
    rw [← h_rhs]
    -- Case split on the value at k
    cases h_mem : m1.get? k with
    | none =>
        have hm2 : m2.get? k = none := by rw [← hk, h_mem]
        have hm : m.get? k = none := by rw [hm1_get, h_mem]
        have hf : f k none none = none := f_none k
        rw [h_go, h_mem, hm2, hf]
        simpa [HashMap.get?_eq_getElem?] using hm.symm
    | some v =>
        have hm2 : m2.get? k = some v := by rw [← hk, h_mem]
        have hm : m.get? k = some v := by rw [hm1_get, h_mem]
        have hf : f k (some v) (some v) = some v := f_idem k v
        rw [h_go, h_mem, hm2, hf]
        simpa [HashMap.get?_eq_getElem?] using hm
  · -- k is not in the list
    have h_go := go_get_not_mem m1 m2 f ((m1.keys ++ m2.keys).dedup) ({} : HashMap α β) k h_in
    have h_rhs : (combineMaps.go m1 m2 f ((m1.keys ++ m2.keys).dedup) ({}:HashMap α β)).get? k =
      (combineMaps.go m1 m2 f ((m1.keys ++ m2.keys).dedup) ({}:HashMap α β))[k]? := rfl
    rw [← h_rhs, h_go]
    -- Show empty map returns none
    have h_empty : ({} : HashMap α β).get? k = none := by
      simp [HashMap.get?_eq_getElem?]
    rw [h_empty]
    -- Need to show m.get? k = none
    have h_not_in_keys : k ∉ (m1.keys ++ m2.keys) := by
      intro h_contra
      have h_mem := List.mem_dedup.mpr h_contra
      exact h_in h_mem
    rw [List.mem_append] at h_not_in_keys
    push_neg at h_not_in_keys
    have h_not_m1 : k ∉ m1.keys := h_not_in_keys.1
    have h_not_m2 : k ∉ m2.keys := h_not_in_keys.2
    have hm1_none : m1.get? k = none := by
      cases h : m1.get? k with
      | none => rfl
      | some v =>
          -- If m1.get? k = some v, then k must be in m1.keys
          have h_isSome : m1[k]?.isSome := by
            rw [HashMap.get?_eq_getElem?] at h
            simp [h]
          have h_in_m1 : k ∈ m1 := HashMap.isSome_getElem?_iff_mem.mp h_isSome
          have h_in_keys : k ∈ m1.keys := HashMap.mem_keys.mpr h_in_m1
          exact absurd h_in_keys h_not_m1
    have hm_none : m.get? k = none := by rw [hm1_get, hm1_none]
    simpa [HashMap.get?_eq_getElem?] using hm_none.symm


theorem joinMemEnv_idempotent : ∀ (m m1 m2 : MemoryTypeEnv),
  m.equiv m1 → m.equiv m2 → m.equiv (joinMemEnvs m1 m2) := by
  intros m m1 m2 h1 h2
  simp [MemoryTypeEnv.equiv, joinMemEnvs]
  apply combineMaps_equiv_helper
  · exact h1
  · exact h2
  · intros k v
    have := joinMemEnvs_func_idempotent k v
    simp [beq_iff_eq] at this
    exact this
  · intro k
    exact joinMemEnvs_func_none k
