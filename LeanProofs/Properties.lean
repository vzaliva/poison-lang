-- Formal properties of the poison language

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
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

open Std

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

theorem MemoryTypeEnv_eq_equiv {m₁ m₂ : MemoryTypeEnv} (h : m₁ = m₂) : m₁.equiv m₂ :=
  by
  rw [h]
  simp [MemoryTypeEnv.equiv]

-- ================================================================
-- Generic list lemmas (to reduce compilation burden elsewhere)
-- ================================================================

-- Helper lemma: if List.mapM succeeds, we get a Forall₂ witness of per-element success.
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

-- Helper lemma: Forall₂ gives an existence for membership on the left.
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

-- Helper lemma: if `List.mapM` succeeds, then each input element maps to some output element.
theorem List.mapM_Except_ok_exists_of_mem_left
    (xs : List α) (f : α → Except ε β) :
    ∀ (ys : List β), List.mapM f xs = Except.ok ys →
      ∀ x ∈ xs, ∃ y, y ∈ ys ∧ f x = Except.ok y := by
  intro ys hmap x hx
  have hForall2 := List.mapM_Except_ok_implies_forall2 (xs := xs) (f := f) ys hmap
  simpa using (List.Forall2.exists_of_mem_left (R := fun x y => f x = Except.ok y) hForall2 x hx)
