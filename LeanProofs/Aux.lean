-- General-purpose lemmas (lists, Except, Forall₂, ExtTreeMap).
-- This module is self-contained: no LeanPoison or other LeanProofs imports.

import Mathlib.Tactic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Basic
import Batteries.Data.List.Lemmas
import Init.Data.List.Lemmas
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

open Std

-- ================================================================
-- List: removeAll, eraseDups, membership
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
                · have hxfilter : x ∈ as.filter (fun b => !b == a) := by
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

-- ================================================================
-- List: association-list lookup
-- ================================================================

lemma List_lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (x y : α) (v : β) (h_ne : y ≠ x) :
  List.lookup y ((x, v) :: l) = List.lookup y l := by
  simp [List.lookup]
  by_cases h_beq : (y == x) = true
  · have h_eq : y = x := LawfulBEq.eq_of_beq h_beq
    contradiction
  · have h_false : (y == x) = false := by
      cases h : y == x
      · rfl
      · contradiction
    simp [h_false]

-- ================================================================
-- Except
-- ================================================================

theorem Except.error_ne_ok {ε α : Type} (err : ε) (a : α) : Except.error err ≠ Except.ok a :=
  fun h => nomatch h

private theorem Except.bind_eq_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β)
    (h : Except.bind x f = Except.ok b) :
    ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e =>
    simp [Except.bind] at h
  | ok a =>
    refine ⟨a, rfl, ?_⟩
    simpa [Except.bind] using h

-- ================================================================
-- ExtTreeMap
-- ================================================================

lemma ExtTreeMap_insert_preserves_injectivity
    {α : Type} {compare : α → α → Ordering} [TransCmp compare] [LawfulEqCmp compare]
    {β : Type} (m : ExtTreeMap α β compare) (k : α) (v : β)
    (h_fresh_value : ∀ k', m.get? k' ≠ some v)
    (h_inj : ∀ k₁ k₂ a, m.get? k₁ = some a → m.get? k₂ = some a → k₁ = k₂) :
  ∀ k₁ k₂ a, (m.insert k v).get? k₁ = some a → (m.insert k v).get? k₂ = some a → k₁ = k₂ := by
  intro k₁ k₂ a hlookup1 hlookup2
  rw [ExtTreeMap.get?_eq_getElem?] at hlookup1 hlookup2
  simp only [ExtTreeMap.getElem?_insert] at hlookup1 hlookup2
  by_cases h_eq1 : compare k k₁ = Ordering.eq
  · have h_k_eq : k = k₁ := LawfulEqCmp.eq_of_compare h_eq1
    have h_k1_eq : k₁ = k := h_k_eq.symm
    simp [h_eq1] at hlookup1
    subst hlookup1
    by_cases h_eq2 : compare k k₂ = Ordering.eq
    · have h_k_eq2 : k = k₂ := LawfulEqCmp.eq_of_compare h_eq2
      have h_k2_eq : k₂ = k := h_k_eq2.symm
      simp [h_eq2] at hlookup2
      rw [h_k1_eq, h_k2_eq]
    · simp [h_eq2] at hlookup2
      have h_contra : m.get? k₂ ≠ some v := h_fresh_value k₂
      contradiction
  · simp [h_eq1] at hlookup1
    by_cases h_eq2 : compare k k₂ = Ordering.eq
    · have h_k_eq2 : k = k₂ := LawfulEqCmp.eq_of_compare h_eq2
      have h_k2_eq : k₂ = k := h_k_eq2.symm
      simp [h_eq2] at hlookup2
      subst hlookup2
      have h_contra : m.get? k₁ ≠ some v := h_fresh_value k₁
      contradiction
    · simp [h_eq2] at hlookup2
      rw [← ExtTreeMap.get?_eq_getElem?] at hlookup1 hlookup2
      exact h_inj k₁ k₂ a hlookup1 hlookup2

-- ================================================================
-- List + Except: foldlM / mapM preserve properties
-- ================================================================

private theorem List.foldlM_Except_preserves_property_of_forall_mem
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

theorem List.foldlM_Except_preserves_property
    (xs : List α) (init : β) (f : β → α → Except ε β)
    (P : β → Prop)
    (h_init : P init)
    (h_preserve : ∀ (acc : β) (x : α), P acc → (∀ (acc' : β), f acc x = Except.ok acc' → P acc')) :
    ∀ (result : β), List.foldlM f init xs = Except.ok result → P result := by
  intro result h_fold
  refine List.foldlM_Except_preserves_property_of_forall_mem xs init f P (fun _ => True)
    h_init (fun x _ => trivial) (fun acc x hP _ => h_preserve acc x hP) result h_fold

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
        injection h_map with h_list_eq
        subst h_list_eq
        intro z h_mem
        simp [List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_fx_z : f x = Except.ok z := h_fx
          exact h_preserve x z h_fx_z
        | inr h_mem_rest =>
          exact ih rest_results h_map_results z h_mem_rest

-- ================================================================
-- List + Except + Forall₂
-- ================================================================

-- If List.mapM succeeds, we get a Forall₂ witness of per-element success.
theorem List.mapM_Except_ok_implies_forall2
    (xs : List α) (f : α → Except ε β) :
    ∀ (ys : List β), List.mapM f xs = Except.ok ys →
      List.Forall₂ (fun x y => f x = Except.ok y) xs ys := by
  induction xs with
  | nil =>
      intro ys h
      simp [List.mapM_nil, pure, Except.pure] at h
      cases h
      exact List.Forall₂.nil
  | cons x xs ih =>
      intro ys h
      simp [List.mapM_cons, bind, Except.bind] at h
      cases hx : f x with
      | error _err =>
          simp [hx] at h
      | ok y =>
          simp [hx] at h
          cases hxs : List.mapM f xs with
          | error _err =>
              simp [hxs] at h
          | ok ys' =>
              simp [hxs] at h
              injection h with hys
              subst hys
              exact List.Forall₂.cons hx (ih ys' hxs)

-- Forall₂ gives an existence for membership on the left.
theorem List.Forall2.exists_of_mem_left
    {R : α → β → Prop} {xs : List α} {ys : List β} :
    List.Forall₂ R xs ys →
    ∀ x ∈ xs, ∃ y, y ∈ ys ∧ R x y := by
  intro h
  induction h with
  | nil =>
      intro x hx
      cases hx
  | cons hx _htail ih =>
      intro x hxmem
      simp [List.mem_cons] at hxmem
      cases hxmem with
      | inl hxeq =>
          subst hxeq
          exact ⟨_, by simp, hx⟩
      | inr hxrest =>
          obtain ⟨y, hymem, hR⟩ := ih x hxrest
          exact ⟨y, by simp [hymem], hR⟩

-- If List.mapM succeeds, each input element maps to some output element.
private theorem List.mapM_Except_ok_exists_of_mem_left
    (xs : List α) (f : α → Except ε β) :
    ∀ (ys : List β), List.mapM f xs = Except.ok ys →
      ∀ x ∈ xs, ∃ y, y ∈ ys ∧ f x = Except.ok y := by
  intro ys hmap x hx
  have hForall2 := List.mapM_Except_ok_implies_forall2 (xs := xs) (f := f) ys hmap
  simpa using (List.Forall2.exists_of_mem_left (R := fun x y => f x = Except.ok y) hForall2 x hx)
