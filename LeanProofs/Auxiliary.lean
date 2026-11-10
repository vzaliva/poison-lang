-- General-purpose lemmas (lists, Except, ExtTreeMap).
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
-- List: eraseDups membership
-- ================================================================

lemma List.mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α] {x : α} {l : List α}
    (h : x ∈ l) : x ∈ l.eraseDups :=
  List.mem_eraseDups.mpr h

-- ================================================================
-- List: association-list lookup
-- ================================================================

lemma List_lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (x y : α) (v : β) (h_ne : y ≠ x) :
  List.lookup y ((x, v) :: l) = List.lookup y l := by
  grind [List.lookup]

-- ================================================================
-- Except
-- ================================================================

theorem Except.error_ne_ok {ε α : Type} (err : ε) (a : α) : Except.error err ≠ Except.ok a :=
  fun h => nomatch h

-- ================================================================
-- ExtTreeMap
-- ================================================================

lemma ExtTreeMap_insert_preserves_injectivity
    {α : Type} {compare : α → α → Ordering} [TransCmp compare] [LawfulEqCmp compare]
    {β : Type} (m : ExtTreeMap α β compare) (k : α) (v : β)
    (h_fresh_value : ∀ k', m.get? k' ≠ some v)
    (h_inj : ∀ k₁ k₂ a, m.get? k₁ = some a → m.get? k₂ = some a → k₁ = k₂) :
  ∀ k₁ k₂ a, (m.insert k v).get? k₁ = some a → (m.insert k v).get? k₂ = some a → k₁ = k₂ := by
  intro k₁ k₂ a h1 h2
  simp only [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert] at *
  grind

/-- `m` is a submap of `m'`: every key/value entry of `m` is preserved in `m'`.

    Insertions at fresh keys are allowed; overwrites and removals are forbidden.
    Used as the foundation for `TagMeaningExtends` (`⊑`) on `TagMeaning`. -/
abbrev ExtTreeMap.IsSubmap
    {α : Type} {compare : α → α → Ordering} [TransCmp compare]
    {β : Type} (m m' : ExtTreeMap α β compare) : Prop :=
  ∀ k v, m.get? k = some v → m'.get? k = some v

theorem ExtTreeMap.IsSubmap.refl
    {α : Type} {compare : α → α → Ordering} [TransCmp compare]
    {β : Type} (m : ExtTreeMap α β compare) : ExtTreeMap.IsSubmap m m :=
  fun _ _ h => h

theorem ExtTreeMap.IsSubmap.trans
    {α : Type} {compare : α → α → Ordering} [TransCmp compare]
    {β : Type} {m₁ m₂ m₃ : ExtTreeMap α β compare}
    (h₁ : ExtTreeMap.IsSubmap m₁ m₂) (h₂ : ExtTreeMap.IsSubmap m₂ m₃) :
    ExtTreeMap.IsSubmap m₁ m₃ :=
  fun k v h => h₂ k v (h₁ k v h)

-- ================================================================
-- List + Except: foldlM preserves properties
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
