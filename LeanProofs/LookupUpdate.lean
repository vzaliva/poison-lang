-- Formal properties of the poison language: Helper Lemmas for Lookup/Update Operations

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Std.Data.ExtTreeMap.Lemmas

import Init.Data.List
import Init.Data.List.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std

-- ================================================================
-- Helper Lemmas for Lookup/Update Operations
-- ================================================================

-- General lemma: If y ≠ x, then List.lookup y ((x, v) :: l) = List.lookup y l
-- This holds for any association list because update prepends, and lookup skips non-matching keys
lemma List_lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (x y : α) (v : β) (h_ne : y ≠ x) :
  List.lookup y ((x, v) :: l) = List.lookup y l := by
  simp [List.lookup]
  -- Use by_cases on the boolean equality check
  by_cases h_beq : (y == x) = true
  · -- Case: (y == x) = true, which contradicts h_ne : y ≠ x
    have h_eq : y = x := LawfulBEq.eq_of_beq h_beq
    contradiction
  · -- Case: (y == x) ≠ true, so (y == x) = false
    have h_false : (y == x) = false := by
      cases h : y == x
      · rfl
      · contradiction
    simp [h_false]

-- CapturedVarEnv ↔ list convenience lemmas
@[simp] lemma CapturedVarEnv.lookup_eq (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.lookup env x = List.lookup x env := rfl

@[simp] lemma CapturedVarEnv.update_eq (env : CapturedVarEnv) (x : Name) (qt : QTyp) :
  CapturedVarEnv.update env x qt = (x, qt) :: env := rfl

@[simp] lemma CapturedVarEnv.hasKey_iff (env : CapturedVarEnv) (x : Name) :
  CapturedVarEnv.hasKey env x ↔ List.lookup x env ≠ none := by
  rfl

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarTypeEnv_lookup_update_eq (env : VarTypeEnv) (x : Name) (qt : QTyp) :
  (env.update x qt).lookup x = some qt := by
  simp [VarTypeEnv.update, VarTypeEnv.lookup]

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarTypeEnv_lookup_update_ne (env : VarTypeEnv) (x y : Name) (qt : QTyp) (h_ne : y ≠ x) :
  (env.update x qt).lookup y = env.lookup y := by
  by_cases h_eq : varTypeEnvCmp x y = .eq
  · have h_xy : x = y := LawfulEqCmp.eq_of_compare h_eq
    exact (h_ne h_xy.symm).elim
  · simp [VarTypeEnv.update, VarTypeEnv.lookup, ExtTreeMap.getElem?_insert, h_eq]

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarEnv_lookup_update_ne (env : VarEnv) (x y : Name) (v : Value) (h_ne : y ≠ x) :
  (env.update x v).lookup y = env.lookup y := by
  simp [VarEnv.update, VarEnv.lookup]
  exact List_lookup_cons_ne env x y v h_ne
