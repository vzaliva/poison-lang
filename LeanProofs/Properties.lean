-- Formal properties of the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanPoison.Poison
import LeanProofs.Equality
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


-- set_option diagnostics true

set_option maxHeartbeats 2000000

-- TODO: Ideally we would not need this but for brevity sometimes we close some
-- proofs with <;> followed by simp [...] and for some branches some args arew
-- not used. We should fix this to avoid disabling the linter warning.
set_option linter.unusedSimpArgs false

-- TODO: review these warnings
set_option linter.unnecessarySeqFocus false

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

section joinMemEnv_idempotent_Proofs

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

end joinMemEnv_idempotent_Proofs

theorem toExpr_toPExpr (pe : PExpr) :
  pe.toExpr.toPExpr = Except.ok pe := by
  induction pe with
  | unit | num _ | bool _ | str _ | var _ =>
    simp [PExpr.toExpr, Expr.toPExpr, pure, Except.pure]
  | vlet x e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | app e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | op e1 o e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | unaryop opname e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH]
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2, IH3]
  | deref e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH]

section TypecheckPExprPreservesTypestate

-- Private lemma for unit case
private lemma typecheck_unit_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat)
  (_C : ctx.pureCtx = true) (_P : Expr.unit.toPExpr = Except.ok pe) (H : typecheckExpr ctx Expr.unit (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for str case
private lemma typecheck_str_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (s : String)
  (_C : ctx.pureCtx = true) (_P : (Expr.str s).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.str s) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for num case
private lemma typecheck_num_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (n : Int)
  (_C : ctx.pureCtx = true) (_P : (Expr.num n).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.num n) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for bool case
private lemma typecheck_bool_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (b : Bool)
  (_C : ctx.pureCtx = true) (_P : (Expr.bool b).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.bool b) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  cases H
  simp [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for var case
private lemma typecheck_var_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (name : Name)
  (C : ctx.pureCtx = true) (_P : (Expr.var name).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.var name) (fuel + 1) = Except.ok result) :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp_all [typecheckExpr]
  -- All var cases preserve environment fields - handle uniformly
  simp [typecheckVar] at H
  cases h0: ctx.varEnv.lookup name with
  | none => simp_all
  | some qt =>
    simp [h0] at H
    cases h1: qt with
    | mk etyp poison pred =>
      simp [h1] at H
      cases h3 : pred with
      | guardClosure tag arg_name pred_body var_env =>
        -- Both guard variants behave identically for the environment fields
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
      | guardOnly tag =>
        cases h5 : ctx.tagEnv.get? tag with
        | none =>
          simp_all [typecheckVar, h0, h1, h3, h5, pure, Except.pure]
          cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
        | some bd =>
          cases bd with
          | mk value deps =>
            cases h6 : value with
            | false =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
            | true =>
              simp_all [typecheckVar, h0, h1, h3, h5, h6, pure, Except.pure]
              cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
      | noPred =>
        -- No predicate case: preserves environment
        simp_all [typecheckVar, h0, h1, h3, pure, Except.pure]
        cases result <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]

-- Private lemma for deref case
private lemma typecheck_deref_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr)
  (C : ctx.pureCtx = true) (P : e1.deref.toPExpr = Except.ok pe) (H : typecheckExpr ctx e1.deref (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero | succ fuel') <;>
    simp [typecheckDeref, bind, Except.bind] at H
  cases h0: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    -- use IH
    simp [Expr.toPExpr, Functor.map, Except.map] at P
    cases h1: e1.toPExpr with
    | error err =>
      simp_all
    | ok pe1 =>
      simp [h1] at P
      have hfuel : fuel' < fuel' + 1 + 1 := by linarith
      specialize IH fuel' hfuel ctx e1 pe1 result1 h1 C h0
      rcases IH with ⟨H1, H2, H3, H4⟩
      simp_all
      cases h2: result1.qualType with
      | mk etyp poison _pred =>
        simp_all
        cases h3: etyp with
        | ref t l =>
          simp_all
          cases h4: poison with
          | true =>
            simp_all [pure, Except.pure]
            cases result; cases result1; cases ctx; cases H; simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
          | false =>
            simp [h4] at H
            cases h5 : result1.memEnv'.get? l with
            | none =>
              simp_all
            | some qt =>
              cases h6 : qt with
              | mk etyp' p2 tp =>
                simp_all
                cases h7 : tp with
                | noPred =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    cases result; cases result1; cases ctx; cases H; simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                | guardOnly k =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    match h10 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                | guardClosure k arg_name pred_body var_env =>
                  simp_all
                  cases h9 : etyp' != t with
                  | true =>
                    simp_all
                  | false =>
                    simp_all [pure, Except.pure]
                    match h10 : result1.tagEnv'.get? k with
                    | none =>
                      simp_all <;>
                      cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
                    | some bd =>
                      cases bd with
                      | mk value _deps =>
                        cases value <;>
                        simp_all <;>
                        cases result <;> cases result1 <;> cases ctx <;> cases H <;> simp_all [MemoryTypeEnv.equiv, Std.HashMap.Equiv]
        | _ => simp_all

-- Private lemma for ite case
private lemma typecheck_ite_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 e3 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.ite e2 e3).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.ite e2 e3) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckIf, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with| error err | ok pe1 ) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h3: e2.toPExpr with | error err | ok pe2) <;> simp [h3] at P
  (cases h4: e3.toPExpr with | error err | ok pe3) <;> simp [h4] at P

  cases h8: matchGuard e1 ctx.memEnv ctx.varEnv with
  | error err =>
    -- simple case: no matching predicate found
    simp_all
    cases h5: typecheckExpr ctx e1 fuel' with
    | error err =>
      simp_all
    | ok result1 =>
      simp [h5] at H
      have hfuel : fuel' < fuel' + 1 + 1 := by linarith
      have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h5
      rcases IH1 with ⟨H1, H2, H3, H4⟩
      simp_all
      cases h6: result1.qualType with
      | mk etyp' poison' pred' =>
        simp_all
        cases h7: etyp' != ETyp.bool with
        | true =>
          simp_all
        | false =>
          simp_all [pure, Except.pure]
          cases h9: typecheckExpr
                      { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                        tagEnv := result1.tagEnv', nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := ctx.pureCtx }
                      e2 fuel' with
          | error err =>
            simp_all
          | ok result2 =>
            simp_all
            cases h10: result2.qualType with
            | mk etyp2 p'' pred =>
              simp_all
              cases h11: typecheckExpr
                      { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                        tagEnv := result1.tagEnv',
                        nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := ctx.pureCtx }
                      e3 fuel' with
              | error err =>
                simp_all
              | ok result3 =>
                simp_all
                cases h12: result3.qualType with
                | mk etyp3 p''' pred =>
                  simp_all
                  cases h13: beqETypSignature etyp2 etyp3 with
                  | false =>
                    simp_all
                  | true =>
                    simp_all [pure, Except.pure]
                    have C' : ({ pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                 tagEnv := result1.tagEnv',
                                 nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                            := by simp_all
                    have IH2 := IH fuel' hfuel
                        { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv',
                          nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true }
                        e2 pe2 result2 h3 C' h9
                    have C'' : ({ pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                                  tagEnv := result1.tagEnv',
                                  nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                            := by simp_all
                    have IH3 := IH fuel' hfuel
                        { pc := joinPoison ctx.pc poison', memEnv := result1.memEnv', varEnv := ctx.varEnv,
                          tagEnv := result1.tagEnv',
                          nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                        e3 pe3 result3 h4 C'' h11
                    rcases IH2 with ⟨H14, H15, H16⟩
                    rcases IH3 with ⟨H17, H18, H19⟩
                    -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv' ∧ result1.memEnv'.equiv result3.memEnv'
                    -- Goal: memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv')
                    -- Use joinMemEnv_idempotent with m=result1.memEnv', m1=result2.memEnv', m2=result3.memEnv'
                    have H_join : result1.memEnv'.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                      joinMemEnv_idempotent result1.memEnv' result2.memEnv' result3.memEnv' H14 H17
                    have H_trans : ctx.memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                      Std.HashMap.Equiv.trans H1 H_join
                    cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
  | ok k_deps =>
    -- predicate-based case: matching predicate found
    simp_all
    have ctx_eta :
      { pc := ctx.pc,
        memEnv := ctx.memEnv,
        varEnv := ctx.varEnv,
        tagEnv := ctx.tagEnv,
        nextLoc := ctx.nextLoc,
        nextTag := ctx.nextTag,
        pureCtx := true } = ctx := by
      rw [← C]

    cases h5: typecheckExpr {
                              pc := ctx.pc,
                              memEnv := ctx.memEnv,
                              varEnv := ctx.varEnv,
                              tagEnv := ctx.tagEnv,
                              nextLoc := ctx.nextLoc,
                              nextTag := ctx.nextTag,
                              pureCtx := true
                            } e1 fuel' with
    | error err =>
       rw [h5] at H
       simp at H
    | ok result1 =>
      rw [h5] at H
      simp at H
      cases h6: result1.qualType with
      | mk etyp1 p' pred =>
        simp_all
        cases h7: etyp1 != ETyp.bool
        · -- false case: etyp1 = ETyp.bool, proceed with the then/else branches
          simp_all [pure, Except.pure]
          cases h9:  typecheckExpr
                      { pc := ctx.pc,
                        memEnv := ctx.memEnv,
                        varEnv := ctx.varEnv,
                        tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
                        nextLoc := ctx.nextLoc,
                        nextTag := ctx.nextTag,
                        pureCtx := true }
                      e2 fuel' with
          | error err =>
            simp [h9] at H
          | ok result2 =>
            simp [h9] at H
            cases h10: result2.qualType with
            | mk etyp2 p'' pred =>
              simp [h10] at H
              cases h11: typecheckExpr
                      { pc := ctx.pc,
                        memEnv := ctx.memEnv,
                        varEnv := ctx.varEnv,
                        tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
                        nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                      e3 fuel' with
              | error err =>
                simp [h11] at H
              | ok result3 =>
                simp [h11] at H
                cases h12: result3.qualType with
                | mk etyp3 p''' pred =>
                  simp [h12] at H
                  cases h13: beqETypSignature etyp2 etyp3 with
                  | false =>
                    simp [h13] at H
                  | true =>
                    simp [h13] at H
                    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
                    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h5
                    rcases IH1 with ⟨H1, H2, H3, H4⟩
                    have C' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                 tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
                                 nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true } : TypeContext).pureCtx = true
                            := by simp
                    have IH2 :=
                      IH fuel' hfuel { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                       tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := true, deps := k_deps.2 },
                                       nextLoc := ctx.nextLoc, nextTag := ctx.nextTag, pureCtx := true }
                                       e2 pe2 result2 h3 C' h9

                    have C'' : ({ pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                                       tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
                                       nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true } : TypeContext).pureCtx = true
                            := by simp
                    have IH3 :=
                      IH fuel' hfuel
                        { pc := ctx.pc, memEnv := ctx.memEnv, varEnv := ctx.varEnv,
                          tagEnv := Std.HashMap.insert ctx.tagEnv k_deps.1 { value := false, deps := k_deps.2 },
                          nextLoc := result2.nextLoc', nextTag := result2.nextTag', pureCtx := true }
                        e3 pe3 result3 h4 C'' h11
                    rcases IH2 with ⟨H14, H15, H16⟩
                    rcases IH3 with ⟨H17, H18, H19⟩
                    -- Prove: memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv')
                    -- We have: memEnv.equiv memEnv (reflexivity from H1)
                    -- And: memEnv.equiv result2.memEnv' (from H14)
                    -- And: memEnv.equiv result3.memEnv' (from H17)
                    -- Use joinMemEnv_idempotent with m=memEnv, m1=result2.memEnv', m2=result3.memEnv'
                    have H_join : ctx.memEnv.equiv (joinMemEnvs result2.memEnv' result3.memEnv') :=
                      joinMemEnv_idempotent ctx.memEnv result2.memEnv' result3.memEnv' H14 H17
                    cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
        · -- true case: etyp1 != ETyp.bool, the else branch returns an error (contradiction)
          simp_all

-- Private lemma for op case
private lemma typecheck_op_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 : Expr) (op : Op) (e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.op op e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.op op e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckOp, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
  cases h3: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h3] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h3
    rcases IH1 with ⟨H1, H2, H3, H4⟩
    simp_all
    cases h4: result1.qualType with
    | mk etyp1 p1 pred1 =>
      simp_all
      cases h5: typecheckExpr
                      { pc := ctx.pc, memEnv := result1.memEnv',
                        varEnv := ctx.varEnv,
                        tagEnv := result1.tagEnv',
                        nextLoc := result1.nextLoc',
                        nextTag := result1.nextTag',
                        pureCtx := ctx.pureCtx }
                      e2 fuel' with
      | error err =>
        simp_all
      | ok result2 =>
        simp_all
        cases h6: result2.qualType with
        | mk etyp2 p2 pred2 =>
          simp_all
          cases h7: opEType? op etyp1 etyp2 with
          | some etyp3 =>
            simp_all [pure, Except.pure]
            have C' : ({ pc := ctx.pc,
                         memEnv := result1.memEnv',
                         varEnv := ctx.varEnv,
                         tagEnv := result1.tagEnv',
                         nextLoc := result1.nextLoc',
                         nextTag := result1.nextTag',
                         pureCtx := true } : TypeContext).pureCtx = true
                    := by simp_all
            have IH2 := IH fuel' hfuel
                      { pc := ctx.pc,
                        memEnv := result1.memEnv',
                        varEnv := ctx.varEnv,
                        tagEnv := result1.tagEnv',
                        nextLoc := result1.nextLoc',
                        nextTag := result1.nextTag',
                        pureCtx := true }
                      e2 pe2 result2 h2 C' h5
            rcases IH2 with ⟨H8, H9, H10⟩
            simp_all
            cases result; cases result1; cases result2; cases ctx; cases H; simp_all
            -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
            apply Std.HashMap.Equiv.trans H1 H8
          | none =>
            simp_all

-- Private lemma for unaryop case
private lemma typecheck_unaryop_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (op : UnaryOp) (e : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.unaryop op e).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.unaryop op e) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckUnaryOp, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  cases h2: typecheckExpr ctx e fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h2] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    cases h4: result1.qualType with
    | mk etyp p pred =>
      simp_all
      cases h7: opUnaryEType? op etyp with
      | some r =>
        simp_all [pure, Except.pure]
        specialize IH fuel' hfuel ctx e pe1 result1 h1 C h2
        rcases IH with ⟨H8, H9, H10⟩
        simp_all
        cases result; cases result1; cases ctx; cases H; simp_all
      | none =>
        simp_all

-- Private lemma for vlet case
private lemma typecheck_vlet_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (x : Name) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (Expr.vlet x e1 e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (Expr.vlet x e1 e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckVlet, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
  cases h3: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h3] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h3
    rcases IH1 with ⟨H1, H2, H3, H4⟩
    simp_all
    cases h4: result1.qualType with
    | mk etyp1 p1 pred1 =>
      simp_all
      cases h4: typecheckExpr
                      { pc := ctx.pc, memEnv := result1.memEnv',
                        varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
                        tagEnv := result1.tagEnv',
                        nextLoc := result1.nextLoc',
                        nextTag := result1.nextTag', pureCtx := ctx.pureCtx }
                      e2 fuel' with
      | error err =>
        simp_all
      | ok result2 =>
        simp_all
        cases h5: result2.qualType with
        | mk etyp2 p2 pred2 =>
          simp_all [pure, Except.pure]
          have C' : ({ pc := ctx.pc,
                       memEnv := result1.memEnv',
                       varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
                       tagEnv := result1.tagEnv',
                       nextLoc := result1.nextLoc',
                       nextTag := result1.nextTag',
                       pureCtx := true } : TypeContext).pureCtx = true
                      := by simp_all
          have IH2 := IH fuel' hfuel
            { pc := ctx.pc,
              memEnv := result1.memEnv',
              varEnv := ctx.varEnv.update x { etyp := etyp1, poison := p1, pred := pred1 },
              tagEnv := result1.tagEnv',
              nextLoc := result1.nextLoc',
              nextTag := result1.nextTag',
              pureCtx := true }
            e2 pe2 result2 h2 C' h4
          rcases IH2 with ⟨H8, H9, H10⟩
          simp_all
          cases result; cases result1; cases result2; cases ctx; cases H; simp_all
          -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv'
          apply Std.HashMap.Equiv.trans H1 H8

-- Private lemma for app case
private lemma typecheck_app_preserves_typestate (ctx : TypeContext) (pe : PExpr) (result : TypeResult) (fuel : Nat) (e1 e2 : Expr)
  (C : ctx.pureCtx = true) (P : (e1.app e2).toPExpr = Except.ok pe) (H : typecheckExpr ctx (e1.app e2) (fuel + 1) = Except.ok result)
  (IH : ∀ m < fuel + 1, ∀ (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = Except.ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e m = Except.ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag') :
  ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag' := by
  simp [typecheckExpr] at H
  (cases fuel with | zero |succ fuel') <;> simp_all [typecheckApp, bind, Except.bind]
  simp [Expr.toPExpr, Functor.map, Except.map] at P
  (cases h1: e1.toPExpr with | error err | ok pe1) <;> simp [h1, Seq.seq, Except.bind, Except.map] at P
  (cases h2: e2.toPExpr with | error err | ok pe2) <;> simp [h2, Seq.seq, Except.bind, Except.map] at P
  cases h3: typecheckExpr ctx e1 fuel' with
  | error err =>
    simp_all
  | ok result1 =>
    simp [h3] at H
    have hfuel : fuel' < fuel' + 1 + 1 := by linarith
    have IH1 := IH fuel' hfuel ctx e1 pe1 result1 h1 C h3
    rcases IH1 with ⟨H1, H2, H3, H4⟩
    simp_all
    cases h4: result1.qualType with
    | mk etyp1 p1 pred1 =>
      simp [h4] at H
      cases h5: etyp1 with
      | arrow st1 st2 _p tcl =>
        -- non-pure arrow case; not expected under pureCtx hypothesis
        simp_all
      | parrow st1 st2 p tcl =>
        simp [h5] at H
        cases h6: typecheckExpr
                    { pc := ctx.pc, memEnv := result1.memEnv', varEnv := ctx.varEnv, tagEnv := result1.tagEnv',
                      nextLoc := result1.nextLoc', nextTag := result1.nextTag', pureCtx := true }
                    e2 fuel' with
        | error err =>
          simp_all
        | ok result2 =>
          simp (config := { failIfUnchanged := false }) [h6] at H
          have C' : ({ pc := ctx.pc,
                       memEnv := result1.memEnv',
                       varEnv := ctx.varEnv,
                       tagEnv := result1.tagEnv',
                       nextLoc := result1.nextLoc',
                       nextTag := result1.nextTag',
                       pureCtx := true } : TypeContext).pureCtx = true
                := by simp_all
          have IH2 := IH fuel' hfuel
            { pc := ctx.pc,
              memEnv := result1.memEnv',
              varEnv := ctx.varEnv,
              tagEnv := result1.tagEnv',
              nextLoc := result1.nextLoc',
              nextTag := result1.nextTag',
              pureCtx := true }
            e2 pe2 result2 h2 C' h6
          rcases IH2 with ⟨H7, H8, H9, H10⟩
          simp_all
          cases h7: result2.qualType with
          | mk etyp2 p2 pred2 =>
            simp_all
            cases h7: isSubtype st1 { etyp := etyp2, poison := p2, pred := pred2 } with
            | false =>
              simp_all
            | true =>
              simp_all [pure, Except.pure]
              cases tcl with
              | mk x body env =>
                simp_all
                cases h8: typecheckExpr
                      { pc := joinPoison p (joinPoison ctx.pc p1),
                        memEnv := result2.memEnv',
                        varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                        tagEnv := result2.tagEnv',
                        nextLoc := result2.nextLoc',
                        nextTag := result2.nextTag',
                        pureCtx := true }
                      body.toExpr fuel' with
                | error err =>
                  simp_all
                | ok result3 =>
                  simp_all
                  cases h9: result3.qualType with
                  | mk etyp3 p3 pred3 =>
                    simp_all
                    cases h10: isSubtype st2 { etyp := etyp3, poison := p3, pred := pred3 } with
                    | false =>
                      simp_all
                    | true =>
                      simp_all [pure, Except.pure]
                      have C'' : ({ pc := joinPoison p (joinPoison ctx.pc p1),
                                    memEnv := result2.memEnv',
                                    varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                                    tagEnv := result2.tagEnv',
                                    nextLoc := result2.nextLoc',
                                    nextTag := result2.nextTag',
                                    pureCtx := true } : TypeContext).pureCtx = true
                          := by simp_all
                      have hb : body.toExpr.toPExpr = Except.ok body := by
                        simpa using toExpr_toPExpr body
                      have IH3 := IH fuel' hfuel
                        { pc := joinPoison p (joinPoison ctx.pc p1),
                          memEnv := result2.memEnv',
                          varEnv := VarTypeEnv.update env x { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 },
                          tagEnv := result2.tagEnv',
                          nextLoc := result2.nextLoc',
                          nextTag := result2.nextTag',
                          pureCtx := true }
                        body.toExpr body result3 hb C'' h8
                      rcases IH3 with ⟨H11, H12, H13, H14⟩
                      cases result; cases result1; cases result2; cases result3; cases ctx; cases H; simp_all
                      -- Prove transitivity: memEnv.equiv result1.memEnv' ∧ result1.memEnv'.equiv result2.memEnv' ∧ result2.memEnv'.equiv result3.memEnv'
                      apply Std.HashMap.Equiv.trans H1
                      apply Std.HashMap.Equiv.trans H7
                      exact H11
      | _ => simp_all

theorem typecheck_PExpr_preserves_typestate :
  ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (pe : PExpr) (result : TypeResult),
    e.toPExpr = .ok pe →
    ctx.pureCtx = true →
    typecheckExpr ctx e fuel = .ok result →
    ctx.memEnv.equiv result.memEnv' ∧ ctx.tagEnv = result.tagEnv' ∧ ctx.nextLoc = result.nextLoc' ∧ ctx.nextTag = result.nextTag'
 := by
  intro fuel
   -- strong induction on `fuel`
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro ctx e pe result P C H
    cases n with
    | zero =>
      simp [typecheckExpr] at H
    | succ fuel =>
      cases e with
      | unit =>
        apply typecheck_unit_preserves_typestate ctx pe result fuel C P H
      | str s =>
        apply typecheck_str_preserves_typestate ctx pe result fuel s C P H
      | num n =>
        apply typecheck_num_preserves_typestate ctx pe result fuel n C P H
      | bool b =>
        apply typecheck_bool_preserves_typestate ctx pe result fuel b C P H
      | var name =>
        apply typecheck_var_preserves_typestate ctx pe result fuel name C P H
      | deref e1 =>
        apply typecheck_deref_preserves_typestate ctx pe result fuel e1 C P H IH
      | ite e1 e2 e3  =>
        apply typecheck_ite_preserves_typestate ctx pe result fuel e1 e2 e3 C P H IH
      | op e1 op e2 =>
        apply typecheck_op_preserves_typestate ctx pe result fuel e1 op e2 C P H IH
      | unaryop op e =>
        apply typecheck_unaryop_preserves_typestate ctx pe result fuel op e C P H IH
      | vlet x e1 e2 =>
        apply typecheck_vlet_preserves_typestate ctx pe result fuel x e1 e2 C P H IH
      | app e1 e2 =>
        apply typecheck_app_preserves_typestate ctx pe result fuel e1 e2 C P H IH
      /- The following cases are not possible to convert to PExpr -/
      | newRef _
      | assign _ _
      | seq _ _
      | kwhile _ _
      | fn _ _ _ _
      | pfn _ _ _ _
      | rand _
      | frand _
      | printString _
      | printInt _ =>
        contradiction

end TypecheckPExprPreservesTypestate

-- ================================================================
-- Evaluation Preserves Variable Environment
-- ================================================================
--
-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)

section VarEnvPreservation

-- Helper lemma: bevalFunctionBody preserves varEnv
private lemma bevalFunctionBody_preserves_varEnv
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
    pure (.success finalConfig v) →
  currentConfig.varEnv = finalConfig.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel
  revert finalConfig v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro finalConfig v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, bevalFunctionBody returns outOfFuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp [pure] at h_eval
      -- Apply congrFun to convert function equality to point-wise equality
      apply congrFun (a := ()) at h_eval
      -- Now we have: EvalResult.outOfFuel = EvalResult.success finalConfig v
      -- Injection will give us the contradictory components
      injection h_eval with h_contr
      -- h_contr is a contradiction between different constructors, so cases derives False
      cases h_contr
    | succ fuel' =>
      -- fuel = fuel' + 1: bevalFunctionBody has enough fuel
      unfold LeanPoison.bevalFunctionBody at h_eval
      simp at h_eval
      -- Convert IO to EStateM form
      apply congrFun (a := ()) at h_eval
      simp [bind, Bind.bind, EStateM.bind] at h_eval
      -- Split on body evaluation result
      split at h_eval
      · next h_body_result h_body_state h_beval_body =>
        split at h_eval
        · next evalConfig v_body =>
          -- Body evaluation succeeded
          split at h_eval
          · -- isPure = true branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
          · -- isPure = false branch
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            -- finalConfig = { currentConfig with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc, pureMode := false }
            -- So finalConfig.varEnv = currentConfig.varEnv (record update doesn't touch varEnv)
            simp
        · next =>
          injection h_eval with h_contr _
          injection h_contr
        · next msg =>
          injection h_eval with h_contr _
          injection h_contr
      · next h_body_error h_body_state =>
        injection h_eval

-- Helper lemmas for beval_preserves_varEnv, one per expression constructor

private lemma beval_preserves_varEnv_num (n : Int) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.num n) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_bool (b : Bool) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.bool b) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_unit (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ Expr.unit verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_str (s : String) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.str s) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_var (x : Name) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.var x) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  cases h_lookup : config₀.varEnv.lookup x with
  | some v' =>
    simp [h_lookup] at h_eval
    injection h_eval with h_cfg _
    injection h_cfg with h_cfg_eq
    subst h_cfg_eq
    rfl
  | none =>
    simp [h_lookup] at h_eval
    injection h_eval with h_contr _
    injection h_contr
private lemma beval_preserves_varEnv_op (e1 e2 : Expr) (op : Op) (fuel' : Nat) (verbose : Bool) (config₀ config₃ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.op e1 op e2) verbose = pure (.success config₃ v)) :
  config₀.varEnv = config₃.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁ v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg with h_cfg_eq
            subst h_cfg_eq
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁ v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁ v₁ h_beval1'
            have h_beval2' : LeanPoison.beval fuel' config₁ e2 verbose = pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₁ config₂ v₂ h_beval2'
            exact Eq.trans IH1 IH2
          | none =>
            simp [h_evalOp] at h_eval
            injection h_eval with h_cfg _
            injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 =>
        cases h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => cases h_eval

private lemma beval_preserves_varEnv_unaryop (op : UnaryOp) (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' v' =>
      cases h_evalUnaryOp : LeanPoison.evalUnaryOp op v' with
      | some v_result =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' v') := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' v' h_beval1'
      | none =>
        simp [h_evalUnaryOp] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_ite (e1 e2 e3 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool true)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool true) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next config₁' =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result3 h_state3 h_beval3 =>
        split at h_eval
        · next config₂ v₃ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.bool false)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.bool false) h_beval1'
          have h_beval3' : LeanPoison.beval fuel' config₁' e3 verbose = pure (.success config₂ v₃) := by
            funext _
            simp [pure]
            exact h_beval3
          let IH3 := IH fuel' h_fuel e3 verbose config₁' config₂ v₃ h_beval3'
          exact Eq.trans IH1 IH3
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error3 h_state3 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_newRef (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.newRef e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      injection h_eval with h_cfg _
      injection h_cfg with h_cfg_eq
      subst h_cfg_eq
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      simp [freshLoc]
      exact IH1
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_assign (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' l =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ n =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' (Value.loc l)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' (Value.loc l) h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ (Value.num n) h_beval2'
          simp
          exact Eq.trans IH1 IH2
        · next v => injection h_eval with h_cfg _; injection h_cfg
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_deref (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.deref e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' l =>
      have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
      have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.loc l)) := by
        funext _
        simp [pure]
        exact h_beval1
      let IH1 := IH fuel' h_fuel e1 verbose config₀ config' (Value.loc l) h_beval1'
      cases h_mem_lookup : config'.memory[l]? with
      | some n =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        exact IH1
      | none =>
        simp [h_mem_lookup] at h_eval
        injection h_eval with h_contr _
        injection h_contr
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_seq (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_split1_result h_split1_state h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      . next h_split3_config h_split3_v1 h_beval2 =>
        split at h_eval
        · next h_split4_config config₂ v₂ =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1 with h_eval_e1_result h_eval_e1_config
          subst h_eval_e1_result h_eval_e2 h_eval_e1_config
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose = pure (.success config₂ v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₁' config₂ v₂ h_beval2'
          exact Eq.trans IH1 IH2
        . next h_split4_eq =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
        . next h_split4_msg h_split4_eq =>
          injection h_eval with h_eval_e1 h_eval_e2
          injection h_eval_e1
      . next h_split3_eq => injection h_eval
    · next h_split2_error h_split2_state =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
    . next h_split2_msg h_split2_eq =>
      injection h_eval with h_eval_e1 h_eval_e2
      injection h_eval_e1
  . next h_split1_error h_split1_state h_split1_eq => injection h_eval

private lemma beval_preserves_varEnv_kwhile (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  unfold LeanPoison.beval at h_eval
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel'.succ - 1) config₀ unfolded verbose
  simp at h_eval
  -- After simp: the let binding is inlined and fuel'.succ - 1 simplifies to fuel'
  -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose = pure (.success config₁ v)
  -- Convert to applied form to work with the monadic structure
  apply congrFun (a := ()) at h_eval
  -- h_eval now contains: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose () = pure (.success config₁ v) ()
  have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
  -- Define the unfolded expression that kwhile expands to
  let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  -- h_eval already contains the evaluation of this unfolded expression
  -- Convert from applied form to pure form for IH
  have h_beval_unfolded : LeanPoison.beval fuel' config₀ unfolded verbose = pure (.success config₁ v) := by
    funext _
    simp [pure]
    exact h_eval
  -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
  -- The unfolded expression (ite) preserves varEnv by IH (which internally uses the ite proof)
  exact IH fuel' h_fuel unfolded verbose config₀ config₁ v h_beval_unfolded

private lemma beval_preserves_varEnv_vlet (x : Name) (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval1 =>
    split at h_eval
    · next config₁' v₁ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval2 =>
        split at h_eval
        · next config₂ v₂ =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config₁' v₁) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₀ config₁' v₁ h_beval1'
          simp
          exact IH1
        · next => injection h_eval with h_cfg _; injection h_cfg
        · next msg => injection h_eval with h_cfg _; injection h_cfg
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_fn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.fn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_pfn (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ) (fuel' : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (_IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.pfn x paramType body returnType) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  apply congrFun (a := ()) at h_eval
  simp [pure] at h_eval
  injection h_eval with h_cfg _
  injection h_cfg with h_cfg_eq
  subst h_cfg_eq
  rfl

private lemma beval_preserves_varEnv_app (e1 e2 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result1 h_state1 h_beval2 =>
    split at h_eval
    · next config₁' v₂ =>
      simp [EStateM.bind] at h_eval
      split at h_eval
      · next h_result2 h_state2 h_beval1 =>
        split at h_eval
        · next config₂ x body env =>
          split at h_eval
          · injection h_eval with h_contr _; injection h_contr
          · -- pureMode is false, call bevalFunctionBody
            -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body false = pure (.success config₁ v)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
            have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.closure x body env)) := by
              funext _
              simp [pure]
              exact h_beval1
            let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.closure x body env) h_beval1'
            -- Extract bevalFunctionBody equality from h_eval
            -- Convert from applied form to pure form
            have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval
            -- Apply helper lemma
            have h_funcBody : config₂.varEnv = config₁.varEnv :=
              bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body false v h_bevalFunctionBody
            -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
            exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next config₂ x body env =>
          -- peClosure case (pure function), call bevalFunctionBody with isPure=true
          -- h_eval contains: bevalFunctionBody fuel' verbose config₂ env x v₂ body true = pure (.success config₁ v)
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose = pure (.success config₁' v₂) := by
            funext _
            simp [pure]
            exact h_beval2
          let IH2 := IH fuel' h_fuel e2 verbose config₀ config₁' v₂ h_beval2'
          have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose = pure (.success config₂ (Value.peClosure x body env)) := by
            funext _
            simp [pure]
            exact h_beval1
          let IH1 := IH fuel' h_fuel e1 verbose config₁' config₂ (Value.peClosure x body env) h_beval1'
          -- Extract bevalFunctionBody equality from h_eval
          -- Convert from applied form to pure form
          have h_bevalFunctionBody : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
              pure (.success config₁ v) := by
            funext _
            simp [pure]
            exact h_eval
          -- Apply helper lemma
          have h_funcBody : config₂.varEnv = config₁.varEnv :=
            bevalFunctionBody_preserves_varEnv fuel' verbose config₂ config₁ env x v₂ body true v h_bevalFunctionBody
          -- Chain: config₀.varEnv = config₁'.varEnv (by IH2) = config₂.varEnv (by IH1) = config₁.varEnv (by h_funcBody)
          exact Eq.trans (Eq.trans IH2 IH1) h_funcBody
        · next v => injection h_eval with h_contr _; injection h_contr
        · next => injection h_eval with h_contr _; injection h_contr
        · next msg => injection h_eval with h_contr _; injection h_contr
      · next h_error2 h_state2 => injection h_eval
    · next => injection h_eval with h_contr _; injection h_contr
    · next msg => injection h_eval with h_contr _; injection h_contr
  · next h_error1 h_state1 => injection h_eval

private lemma beval_preserves_varEnv_rand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.rand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_frand (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.frand e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      split at h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next r_result r_state =>
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          subst h_cfg_eq
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
        · next r_error r_state => injection h_eval
      · simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          injection h_eval with h_cfg _
          injection h_cfg
        · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printInt (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printInt e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' n =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.num n) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

private lemma beval_preserves_varEnv_printString (e1 : Expr) (fuel' : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel'.succ, ∀ (e : Expr) (verbose : Bool) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) → config₀.varEnv = config₁.varEnv)
    (h_eval : LeanPoison.beval fuel'.succ config₀ (Expr.printString e1) verbose = pure (.success config₁ v)) :
  config₀.varEnv = config₁.varEnv := by
  unfold LeanPoison.beval at h_eval
  simp at h_eval
  apply congrFun (a := ()) at h_eval
  simp [bind, Bind.bind, EStateM.bind] at h_eval
  split at h_eval
  · next h_result h_state h_beval1 =>
    split at h_eval
    · next config' s =>
      simp [Functor.map, EStateM.map] at h_eval
      split at h_eval
      · next p_result p_state =>
        injection h_eval with h_cfg _
        injection h_cfg with h_cfg_eq
        subst h_cfg_eq
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose = pure (.success config' (Value.str s)) := by
          funext _
          simp [pure]
          exact h_beval1
        exact IH fuel' h_fuel e1 verbose config₀ config' (Value.str s) h_beval1'
      · next p_error p_state => injection h_eval
    · next v => injection h_eval with h_cfg _; injection h_cfg
    · next => injection h_eval with h_cfg _; injection h_cfg
    · next msg => injection h_eval with h_cfg _; injection h_cfg
  · next h_error h_state => injection h_eval

-- Lemma: beval never modifies the variable environment
-- This is a fundamental property: evaluation doesn't change variable bindings
-- (variables can only be added/shadowed via let, but the varEnv itself is immutable)
lemma beval_preserves_varEnv (e : Expr) (fuel : Nat) (verbose : Bool) (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ e verbose = pure (.success config₁ v) →
  config₀.varEnv = config₁.varEnv := by
  intro h_eval
  -- Proof by strong induction on fuel, then case analysis on e
  -- For all expression forms, the varEnv field is never modified
  -- (even in let bindings, we create a new config with extended varEnv for the body,
  --  but the final result restores the original varEnv)
  revert e config₀ config₁ v h_eval verbose
  induction fuel using Nat.strong_induction_on with
  | _ n IH =>
    intro e verbose config₀ config₁ v h_eval
    cases n with
    | zero =>
      -- When fuel = 0, beval returns outOfFuel, not success
      unfold LeanPoison.beval at h_eval
      simp at h_eval
      apply congrFun (a := ()) at h_eval
      cases h_eval
    | succ fuel' =>
      cases e with
      | num n => exact beval_preserves_varEnv_num n fuel' verbose config₀ config₁ v IH h_eval
      | bool b => exact beval_preserves_varEnv_bool b fuel' verbose config₀ config₁ v IH h_eval
      | unit => exact beval_preserves_varEnv_unit fuel' verbose config₀ config₁ v IH h_eval
      | str s => exact beval_preserves_varEnv_str s fuel' verbose config₀ config₁ v IH h_eval
      | var x => exact beval_preserves_varEnv_var x fuel' verbose config₀ config₁ v IH h_eval
      | op e1 op e2 =>
        exact beval_preserves_varEnv_op e1 e2 op fuel' verbose config₀ config₁ v IH h_eval
      | unaryop op e1 =>
        exact beval_preserves_varEnv_unaryop op e1 fuel' verbose config₀ config₁ v IH h_eval
      | ite e1 e2 e3 =>
        exact beval_preserves_varEnv_ite e1 e2 e3 fuel' verbose config₀ config₁ v IH h_eval
      | newRef e1 =>
        exact beval_preserves_varEnv_newRef e1 fuel' verbose config₀ config₁ v IH h_eval
      | assign e1 e2 =>
        exact beval_preserves_varEnv_assign e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | deref e1 =>
        exact beval_preserves_varEnv_deref e1 fuel' verbose config₀ config₁ v IH h_eval
      | seq e1 e2 =>
        exact beval_preserves_varEnv_seq e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | kwhile e1 e2 =>
        exact beval_preserves_varEnv_kwhile e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | vlet x e1 e2 =>
        exact beval_preserves_varEnv_vlet x e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | fn x paramType body returnType =>
        exact beval_preserves_varEnv_fn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | pfn x paramType body returnType =>
        exact beval_preserves_varEnv_pfn x paramType body returnType fuel' verbose config₀ config₁ v IH h_eval
      | app e1 e2 =>
        exact beval_preserves_varEnv_app e1 e2 fuel' verbose config₀ config₁ v IH h_eval
      | rand e1 =>
        exact beval_preserves_varEnv_rand e1 fuel' verbose config₀ config₁ v IH h_eval
      | frand e1 =>
        exact beval_preserves_varEnv_frand e1 fuel' verbose config₀ config₁ v IH h_eval
      | printInt e1 =>
        exact beval_preserves_varEnv_printInt e1 fuel' verbose config₀ config₁ v IH h_eval
      | printString e1 =>
        exact beval_preserves_varEnv_printString e1 fuel' verbose config₀ config₁ v IH h_eval

end VarEnvPreservation

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

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarTypeEnv_lookup_update_ne (env : VarTypeEnv) (x y : Name) (qt : QTyp) (h_ne : y ≠ x) :
  (env.update x qt).lookup y = env.lookup y := by
  simp [VarTypeEnv.update, VarTypeEnv.lookup]
  exact List_lookup_cons_ne env x y qt h_ne

-- If y ≠ x, then updating env with x doesn't affect lookup y
lemma VarEnv_lookup_update_ne (env : VarEnv) (x y : Name) (v : Value) (h_ne : y ≠ x) :
  (env.update x v).lookup y = env.lookup y := by
  simp [VarEnv.update, VarEnv.lookup]
  exact List_lookup_cons_ne env x y v h_ne

-- ================================================================
-- Evaluation Preserves Memory Monotonicity
-- ================================================================
--
-- Lemma: beval can only add memory locations, never remove them
-- This is a fundamental property: evaluation doesn't deallocate memory
--

section MemoryMonotonicity

-- Helper lemma for op case: binary operations chain memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_op (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1_eq =>
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2_eq =>
          split at h_eval
          · next config'' v2 =>
            -- e2 evaluated successfully
            -- Case analysis on evalOp result
            cases h_evalOp : LeanPoison.evalOp op v1 v2 with
            | some v_result =>
              -- evalOp succeeded
              simp [h_evalOp] at h_eval
              simp [pure] at h_eval
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result with h_eq_config h_eq_val
              -- config₁ = config''
              subst h_eq_config
              -- Convert to pure form for IH
              have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                               pure (.success config' v1) := by
                funext _; simp [pure]; exact h_beval1_eq
              have h_beval2' : LeanPoison.beval fuel' config' e2 verbose =
                               pure (.success config'' v2) := by
                funext _; simp [pure]; exact h_beval2_eq
              -- Chain through IH
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
              exact IH fuel' h_fuel e2 config' config'' v2 h_beval2' l IH1
            | none =>
              -- evalOp returned none (contradiction with success)
              simp [h_evalOp] at h_eval
              simp [pure] at h_eval
              injection h_eval with h_eq_result h_eq_state
              injection h_eq_result
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for seq case: sequences chain memory monotonicity through e1 then e2
private lemma beval_memory_monotonic_seq (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1_eq =>
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2_eq =>
          split at h_eval
          · next config'' v2 =>
            -- e2 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config''
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' v1) := by
              funext _; simp [pure]; exact h_beval1_eq
            have h_beval2' : LeanPoison.beval fuel' config' e2 verbose =
                             pure (.success config'' v2) := by
              funext _; simp [pure]; exact h_beval2_eq
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
            exact IH fuel' h_fuel e2 config' config'' v2 h_beval2' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma for unaryop case: unary operations chain memory monotonicity through e1
private lemma beval_memory_monotonic_unaryop (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Unfold beval (use unfold, not simp, due to mutual recursion)
  unfold LeanPoison.beval at h_eval
  -- Apply unit argument to convert to applied form
  apply congrFun (a := ()) at h_eval
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    simp at h_eval
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' v1 =>
        -- e1 evaluated successfully to config', v1
        -- Case analysis on evalUnaryOp result
        cases h_evalOp : LeanPoison.evalUnaryOp op v1 with
        | some v_result =>
          -- evalUnaryOp succeeded
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Convert h_beval1 to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' v1) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH for e1
          exact IH fuel' h_fuel e1 config₀ config' v1 h_beval1' l h_contains
        | none =>
          -- evalUnaryOp returned none (contradiction with success)
          simp [h_evalOp] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result
      · next h_result1_error =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma for ite case: conditionals chain memory monotonicity through e1, then either e2 or e3
private lemma beval_memory_monotonic_ite (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' =>
        -- e1 evaluated successfully to config₁', now branch on boolean value (true case)
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- Branch matched Value.bool true, now evaluate e2
          split at h_eval
          · next config₂ v₂ =>
            -- e2 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' (Value.bool true)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose =
                             pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool true) h_beval1' l h_contains
            exact IH fuel' h_fuel e2 config₁' config₂ v₂ h_beval2' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next config₁' =>
        -- e1 evaluated successfully to config₁', now branch on boolean value (false case)
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result3 h_state3 h_beval3 =>
          -- Branch matched Value.bool false, now evaluate e3
          split at h_eval
          · next config₂ v₃ =>
            -- e3 evaluated successfully
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' (Value.bool false)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval3' : LeanPoison.beval fuel' config₁' e3 verbose =
                             pure (.success config₂ v₃) := by
              funext _
              simp [pure]
              exact h_beval3
            -- Chain through IH
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.bool false) h_beval1' l h_contains
            exact IH fuel' h_fuel e3 config₁' config₂ v₃ h_beval3' l IH1
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error3 h_state3 => injection h_eval
      · next v =>
        -- e1 evaluated to non-boolean value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for deref case: dereference chains memory monotonicity through e1
private lemma beval_memory_monotonic_deref (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.deref e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Unfold beval (use unfold, not simp, due to mutual recursion)
  unfold LeanPoison.beval at h_eval
  -- Apply unit argument to convert to applied form
  apply congrFun (a := ()) at h_eval
  -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel, not success
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    simp at h_eval
    -- Unfold monadic bind to expose match expressions
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation (outer EStateM.Result)
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' loc_val =>
        -- e1 evaluated to location loc_val
        -- Extract memory lookup result first
        cases h_mem_lookup : config'.memory.get? loc_val with
        | some n =>
          -- Location found in memory
          -- Rewrite the match expression using the lookup result
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = some n := h_mem_lookup
          rw [h_mem_eq] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config'.memory.contains l
          -- Use IH on e1: fuel' < fuel'.succ, and beval uses fuel'
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          -- Convert h_beval1 to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.loc loc_val)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH for e1 (note: IH has order: e, config₀, config₁, v, h_eval, l, h_contains)
          exact IH fuel' h_fuel e1 config₀ config' (Value.loc loc_val) h_beval1' l h_contains
        | none =>
          -- Location not found: deref returns runtimeError (contradiction)
          -- Note: config'.memory[loc_val]? is syntactic sugar for config'.memory.get? loc_val
          have h_mem_eq : config'.memory[loc_val]? = none := h_mem_lookup
          rw [h_mem_eq] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_contr
          cases h_contr
      · next h_result1_error =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next h_val =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 =>
      -- e1 evaluation returned error from EStateM (contradiction)
      injection h_eval

-- Helper lemma: HashMap.insert preserves contains for all keys
-- HashMap.insert either adds a new key or updates an existing one, but never removes other keys
-- This is used by both assign and newRef proofs
private lemma HashMap_insert_preserves_contains {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {β : Type}
    (m : Std.HashMap α β) (k k' : α) (v : β) :
  m.contains k' → (m.insert k v).contains k' := by
  intro h_contains
  -- HashMap.insert preserves all existing keys - it only adds or updates, never removes
  -- Case analysis: if k' = k, use Std.HashMap.contains_insert
  -- If k' ≠ k, insert doesn't affect other keys (get? is preserved for distinct keys)
  by_cases h_eq : k = k'
  · -- k = k': insert definitely makes this key present
    subst h_eq
    -- Use the mathlib lemma: (m.insert k v).contains k = true
    simp [Std.HashMap.contains_insert]
  · -- k ≠ k': insert preserves other keys
    -- Use the fact that for distinct keys, getElem? is preserved
    -- Convert both sides to mem/getElem? form
    rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?]
    rw [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?] at h_contains
    -- Now use getElem?_insert: (m.insert k v)[k']? = if (k == k') then some v else m[k']?
    rw [Std.HashMap.getElem?_insert]
    -- Case analysis on (k == k')
    by_cases h_beq : (k == k')
    · -- If (k == k') = true, then we get some v, and isSome (some v) = true
      simp [h_beq]
    · -- If (k == k') = false, then we get m[k']?, and isSome m[k']? = true by h_contains
      simp [h_beq, h_contains]

-- Helper lemma for newRef case: newRef allocates memory (adds one location, but preserves existing)
private lemma beval_memory_monotonic_newRef (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to number n
        -- Final config₁ is {config'' with memory := config''.memory.update l' n}
        -- where (l', config'') = freshLoc config'
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Extract that config₁ = {config'' with memory := config''.memory.update l' n}
        -- where freshLoc config' = (l', config'')
        -- freshLoc is defined in Runtime.lean, accessible directly
        -- config'' = {config' with nextLoc := config'.nextLoc + 1}, so config''.memory = config'.memory
        have h_config''_mem : ({ config' with nextLoc := config'.nextLoc + 1 } : Config).memory = config'.memory := rfl
        -- Extract memory equality from config₁
        have h_mem_eq : config₁.memory = config'.memory.update config'.nextLoc n := by
          -- From h_eq_config: config₁ = {memory := config''.memory.update l' n, ...}
          -- where l' = config'.nextLoc and config''.memory = config'.memory
          have h_lhs_mem : ({ memory := config'.memory.update config'.nextLoc n, varEnv := config'.varEnv, nextLoc := config'.nextLoc + 1, pureMode := config'.pureMode } : Config).memory = config'.memory.update config'.nextLoc n := rfl
          have h_congr : ({ memory := config'.memory.update config'.nextLoc n, varEnv := config'.varEnv, nextLoc := config'.nextLoc + 1, pureMode := config'.pureMode } : Config).memory = config₁.memory :=
            congrArg Config.memory h_eq_config
          rw [← h_congr, h_lhs_mem]
        -- Convert to pure form for IH
        have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                         pure (.success config' (Value.num n)) := by
          funext _
          simp [pure]
          exact h_beval1
        -- Chain through IH: config₀ → config' (via e1)
        have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
        have IH1 := IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
        -- Now we need: config'.memory.contains l → config'.memory.update config'.nextLoc n contains l
        -- HashMap.update (which is insert) preserves contains for all keys
        rw [h_mem_eq]
        -- Use the helper lemma: HashMap.insert preserves contains
        exact HashMap_insert_preserves_contains config'.memory config'.nextLoc l n IH1
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for assign case: assignment chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_assign (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' loc_val =>
        -- e1 evaluated to location loc_val
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ n =>
            -- e2 evaluated to number n
            -- Final config₁ is {config₂ with memory := config₂.memory.update loc_val n}
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with memory := config₂.memory.update loc_val n}
            -- Memory.update is just insert, which preserves contains
            have h_mem_eq : config₁.memory = config₂.memory.update loc_val n := by
              -- From h_eq_config: {memory := config₂.memory.update loc_val n, ...} = config₁
              have h_lhs_mem : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₂.memory.update loc_val n := rfl
              have h_congr : ({ memory := config₂.memory.update loc_val n, varEnv := config₂.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              rw [← h_congr, h_lhs_mem]
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                                 pure (.success config₁' (Value.loc loc_val)) := by
              funext _
              simp [pure]
              exact h_beval1
            have h_beval2' : LeanPoison.beval fuel' config₁' e2 verbose =
                             pure (.success config₂ (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH: config₀ → config₁' (via e1), then config₁' → config₂ (via e2)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' (Value.loc loc_val) h_beval1' l h_contains
            have IH2 := IH fuel' h_fuel e2 config₁' config₂ (Value.num n) h_beval2' l IH1
            -- Now we need: config₂.memory.contains l → config₂.memory.update loc_val n contains l
            -- HashMap.update is just insert, and insert preserves contains for all keys
            rw [h_mem_eq]
            -- Memory.update = HashMap.insert, which preserves contains
            -- If l = loc_val, insert adds/updates it (definitely contains)
            -- If l ≠ loc_val, insert doesn't remove it (preserves contains)
            exact HashMap_insert_preserves_contains config₂.memory loc_val l n IH2
          · next v =>
            -- e2 evaluated to non-number value (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next =>
            -- e2 evaluation returned outOfFuel (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next msg =>
            -- e2 evaluation returned runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next v =>
        -- e1 evaluated to non-location value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma for vlet case: let binding chains memory monotonicity through e1 and e2
private lemma beval_memory_monotonic_vlet (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result1 h_state1 h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' v₁ =>
        -- e1 evaluated successfully to config₁', v₁
        -- Now create config'' with updated varEnv and evaluate e2
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result2 h_state2 h_beval2 =>
          -- e2 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ v₂ =>
            -- e2 evaluated successfully to config₂, v₂
            -- Final config₁ is {config₂ with varEnv := config₁'.varEnv}
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- Extract that config₁ = {config₂ with varEnv := config₁'.varEnv}
            -- This means config₁.memory = config₂.memory (since only varEnv differs)
            -- From h_eq_config: {memory := config₂.memory, varEnv := config₁'.varEnv, ...} = config₁
            -- Taking memory of both sides using congrArg: lhs.memory = config₁.memory
            -- But lhs.memory = config₂.memory, so config₁.memory = config₂.memory
            have h_lhs_mem : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₂.memory := rfl
            have h_mem_eq : config₁.memory = config₂.memory := by
              -- Apply congrArg to h_eq_config to get: lhs.memory = config₁.memory
              have h_congr : ({ memory := config₂.memory, varEnv := config₁'.varEnv, nextLoc := config₂.nextLoc, pureMode := config₂.pureMode } : Config).memory = config₁.memory :=
                congrArg Config.memory h_eq_config
              -- Now combine with h_lhs_mem: config₂.memory = lhs.memory = config₁.memory
              rw [← h_congr, h_lhs_mem]
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config₁' v₁) := by
              funext _
              simp [pure]
              exact h_beval1
            -- For e2, we evaluate with config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            have h_beval2' : LeanPoison.beval fuel' ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) e2 verbose =
                             pure (.success config₂ v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            -- Chain through IH: config₀ → config₁' (via e1), then config₁' → config₂ (via e2)
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH1 := IH fuel' h_fuel e1 config₀ config₁' v₁ h_beval1' l h_contains
            -- config'' = {config₁' with varEnv := config₁'.varEnv.update x v₁}
            -- config'' has same memory as config₁', so if l is in config₁'.memory, it's in config''.memory
            have h_config''_mem_eq : ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }).memory.contains l =
                                     config₁'.memory.contains l := by
              simp
            rw [← h_config''_mem_eq] at IH1
            -- Now apply IH on e2: config'' → config₂
            have IH2 := IH fuel' h_fuel e2 ({ config₁' with varEnv := config₁'.varEnv.update x v₁ }) config₂ v₂ h_beval2' l IH1
            -- config₁.memory = config₂.memory from h_mem_eq
            rw [h_mem_eq]
            exact IH2
          · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
          · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
        · next h_error2 h_state2 => injection h_eval
      · next => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
      · next msg => simp [pure] at h_eval; injection h_eval with h_eq_result h_eq_state; injection h_eq_result
    · next h_error1 h_state1 => injection h_eval

-- Helper lemma: bevalFunctionBody preserves memory monotonicity
-- This is needed for the app case
private lemma bevalFunctionBody_memory_monotonic
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
    pure (.success finalConfig v) →
  ∀ l, currentConfig.memory.contains l → finalConfig.memory.contains l := by
  intro h_eval l h_contains
  cases fuel with
  | zero =>
    -- When fuel = 0, bevalFunctionBody returns outOfFuel (contradiction)
    unfold LeanPoison.bevalFunctionBody at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Split on body evaluation
    split at h_eval
    · next h_body_result h_body_state h_beval_body =>
      split at h_eval
      · next evalConfig v_body =>
        -- Body evaluation succeeded
        -- Now handle the if-then-else on isPure using split
        split at h_eval
        · -- isPure = true branch: finalConfig = {currentConfig with pureMode := false}
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          -- Extract memory equality: finalConfig.memory = currentConfig.memory
          have h_mem_eq : finalConfig.memory = currentConfig.memory := by
            have h_lhs_mem : ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv, nextLoc := currentConfig.nextLoc, pureMode := false } : Config).memory = currentConfig.memory := rfl
            have h_congr : ({ memory := currentConfig.memory, varEnv := currentConfig.varEnv, nextLoc := currentConfig.nextLoc, pureMode := false } : Config).memory = finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          rw [h_mem_eq]
          exact h_contains
        · -- isPure = false branch: finalConfig = {currentConfig with memory := evalConfig.memory, ...}
          injection h_eval with h_cfg _
          injection h_cfg with h_cfg_eq
          -- Extract memory: finalConfig.memory = evalConfig.memory
          have h_mem_eq : finalConfig.memory = evalConfig.memory := by
            have h_lhs_mem : ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextLoc := evalConfig.nextLoc, pureMode := false } : Config).memory = evalConfig.memory := rfl
            have h_congr : ({ memory := evalConfig.memory, varEnv := currentConfig.varEnv, nextLoc := evalConfig.nextLoc, pureMode := false } : Config).memory = finalConfig.memory :=
              congrArg Config.memory h_cfg_eq
            rw [← h_congr, h_lhs_mem]
          -- bodyConfig = {currentConfig with varEnv := env.update x v₂, pureMode := isPure}
          -- In this branch, isPure = false, so bodyConfig with isPure = bodyConfig with false
          -- But we need to extract that isPure = false from being in the false branch
          -- Use the fact that bodyConfig was created with pureMode := isPure, but we can rewrite it
          -- Actually, we don't need to rewrite - we can just use h_beval_body as-is since it has the right config
          have h_bodyConfig_mem : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).memory = currentConfig.memory := rfl
          -- Convert to pure form for IH
          have h_beval_body' : LeanPoison.beval fuel' ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) body verbose =
                               pure (.success evalConfig v_body) := by
            funext _
            simp [pure]
            exact h_beval_body
          -- Apply IH to body evaluation
          -- Use the original IH with fuel' < fuel'.succ
          have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body' l
          rw [h_bodyConfig_mem] at IH_body
          -- Now we have: currentConfig.memory.contains l → evalConfig.memory.contains l
          have h_mem_contains := IH_body h_contains
          rw [h_mem_eq]
          exact h_mem_contains
      · next => injection h_eval with h_contr _; injection h_contr
      · next msg => injection h_eval with h_contr _; injection h_contr
    · next h_body_error h_body_state => injection h_eval

-- Helper lemma for app case: function application chains memory monotonicity through e1, e2, and body
private lemma beval_memory_monotonic_app (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.app e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e2 evaluation (app evaluates e2 first)
    split at h_eval
    · next h_result2 h_state2 h_beval2 =>
      -- e2 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config₁' v₂ =>
        -- e2 evaluated to config₁', v₂
        simp [EStateM.bind] at h_eval
        split at h_eval
        · next h_result1 h_state1 h_beval1 =>
          -- e1 evaluation succeeded with ok, now split on inner EvalResult
          split at h_eval
          · next config₂ x body env =>
            -- e1 evaluated to closure
            -- Check if config₂.pureMode
            split at h_eval
            · next h_pureMode =>
              -- Pure mode case: runtime error (contradiction)
              injection h_eval with h_contr
              cases h_contr
            · next h_notPureMode =>
              -- Not pure mode: call bevalFunctionBody
              -- h_eval: bevalFunctionBody fuel' verbose config₂ env x v₂ body false = pure (.success config₁ v)
              have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
              -- Convert to pure form for IH
              have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose =
                               pure (.success config₁' v₂) := by
                funext _
                simp [pure]
                exact h_beval2
              have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose =
                               pure (.success config₂ (Value.closure x body env)) := by
                funext _
                simp [pure]
                exact h_beval1
              -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
              have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2' l h_contains
              have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.closure x body env) h_beval1' l IH2
              -- Apply bevalFunctionBody memory monotonicity helper
              have h_bevalFunctionBody' : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body false =
                                         pure (.success config₁ v) := by
                funext _
                simp [pure]
                exact h_eval
              -- Construct IH with fuel' bound from fuel'.succ bound
              have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
                LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
                ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
                intro m h_m_lt_fuel' e config₀ config₁ v h_beval_eq l h_contains_loc
                have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
                exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_eq l h_contains_loc
              exact bevalFunctionBody_memory_monotonic fuel' verbose config₂ config₁ env x v₂ body false v IH_fuel' h_bevalFunctionBody' l IH1
          · next config₂ x body env =>
            -- e1 evaluated to peClosure (pure function)
            -- bevalFunctionBody with isPure=true
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            -- Convert to pure form for IH
            have h_beval2' : LeanPoison.beval fuel' config₀ e2 verbose =
                             pure (.success config₁' v₂) := by
              funext _
              simp [pure]
              exact h_beval2
            have h_beval1' : LeanPoison.beval fuel' config₁' e1 verbose =
                             pure (.success config₂ (Value.peClosure x body env)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Chain through IH: config₀ → config₁' (via e2), then config₁' → config₂ (via e1)
            have IH2 := IH fuel' h_fuel e2 config₀ config₁' v₂ h_beval2' l h_contains
            have IH1 := IH fuel' h_fuel e1 config₁' config₂ (Value.peClosure x body env) h_beval1' l IH2
            -- Apply bevalFunctionBody memory monotonicity helper
            have h_bevalFunctionBody' : LeanPoison.bevalFunctionBody fuel' verbose config₂ env x v₂ body true =
                                       pure (.success config₁ v) := by
              funext _
              simp [pure]
              exact h_eval
            -- Construct IH with fuel' bound from fuel'.succ bound
            have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
              LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
              ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
              intro m h_m_lt_fuel' e config₀ config₁ v h_beval_eq l h_contains_loc
              have h_m_lt_fuel'_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt_fuel' (Nat.le_succ fuel')
              exact IH m h_m_lt_fuel'_succ e config₀ config₁ v h_beval_eq l h_contains_loc
            exact bevalFunctionBody_memory_monotonic fuel' verbose config₂ config₁ env x v₂ body true v IH_fuel' h_bevalFunctionBody' l IH1
          · next v =>
            -- e1 evaluated to non-closure value (contradiction)
            injection h_eval with h_contr
            cases h_contr
          · next =>
            -- e1 evaluation returned outOfFuel (contradiction)
            injection h_eval with h_contr
            cases h_contr
          · next msg =>
            -- e1 evaluation returned runtimeError (contradiction)
            injection h_eval with h_contr
            cases h_contr
        · next h_error1 h_state1 => injection h_eval
      · next =>
        -- e2 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e2 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error2 h_state2 => injection h_eval

-- Helper lemma for rand case: random chains memory monotonicity through e1
private lemma beval_memory_monotonic_rand (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.rand e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- Now split on if n >= 0 (branch for generating random number)
        split at h_eval
        · -- n >= 0: generate random number
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next r_result r_state =>
            -- IO.rand succeeded
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Apply IH on e1: rand doesn't modify memory, only e1 evaluation does
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
          · next r_error r_state => injection h_eval
        · -- n < 0: error case (contradiction with success)
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next p_result p_state =>
            -- IO.println succeeded, but we get runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for frand case: faulty random chains memory monotonicity through e1
private lemma beval_memory_monotonic_frand (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.frand e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- Now split on if n >= 0 (branch for generating faulty random number)
        split at h_eval
        · -- n >= 0: generate faulty random number
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next r_result r_state =>
            -- IO.rand succeeded
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result with h_eq_config h_eq_val
            -- config₁ = config' from h_eq_config
            subst h_eq_config
            -- Convert to pure form for IH
            have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                             pure (.success config' (Value.num n)) := by
              funext _
              simp [pure]
              exact h_beval1
            -- Apply IH on e1: frand doesn't modify memory, only e1 evaluation does
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
          · next r_error r_state => injection h_eval
        · -- n < 0: error case (contradiction with success)
          simp [Functor.map, EStateM.map] at h_eval
          split at h_eval
          · next p_result p_state =>
            -- IO.println succeeded, but we get runtimeError (contradiction)
            simp [pure] at h_eval
            injection h_eval with h_eq_result h_eq_state
            injection h_eq_result
          · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for printInt case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printInt (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.printInt e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' n =>
        -- e1 evaluated to Value.num n
        -- IO.println is wrapped in Functor.map/EStateM.map
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          -- IO.println succeeded
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Convert to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.num n)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH on e1: printInt doesn't modify memory, only e1 evaluation does
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          exact IH fuel' h_fuel e1 config₀ config' (Value.num n) h_beval1' l h_contains
        · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-number value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for printString case: print chains memory monotonicity through e1
private lemma beval_memory_monotonic_printString (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.printString e1) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- Handle fuel check
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    unfold LeanPoison.beval at h_eval
    apply congrFun (a := ()) at h_eval
    simp [pure] at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- When fuel > 0, proceed with evaluation
    unfold LeanPoison.beval at h_eval
    simp at h_eval
    apply congrFun (a := ()) at h_eval
    simp [bind, Bind.bind, EStateM.bind] at h_eval
    -- Case analysis on e1 evaluation
    split at h_eval
    · next h_result h_state h_beval1 =>
      -- e1 evaluation succeeded with ok, now split on inner EvalResult
      split at h_eval
      · next config' s =>
        -- e1 evaluated to Value.str s
        -- IO.println is wrapped in Functor.map/EStateM.map
        simp [Functor.map, EStateM.map] at h_eval
        split at h_eval
        · next p_result p_state =>
          -- IO.println succeeded
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- config₁ = config' from h_eq_config
          subst h_eq_config
          -- Convert to pure form for IH
          have h_beval1' : LeanPoison.beval fuel' config₀ e1 verbose =
                           pure (.success config' (Value.str s)) := by
            funext _
            simp [pure]
            exact h_beval1
          -- Apply IH on e1: printString doesn't modify memory, only e1 evaluation does
          have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          exact IH fuel' h_fuel e1 config₀ config' (Value.str s) h_beval1' l h_contains
        · next p_error p_state => injection h_eval
      · next v =>
        -- e1 evaluated to non-string value (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next =>
        -- e1 evaluation returned outOfFuel (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
      · next msg =>
        -- e1 evaluation returned runtimeError (contradiction)
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result
    · next h_error h_state => injection h_eval

-- Helper lemma for kwhile case: while loops chain memory monotonicity through iterations
private lemma beval_memory_monotonic_kwhile (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = pure (.success config₁ v) →
      ∀ l, config₀.memory.contains l → config₁.memory.contains l) :
  LeanPoison.beval fuel config₀ (Expr.kwhile e1 e2) verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro h_eval l h_contains
  -- kwhile expands to: ite e1 (seq e2 (kwhile e1 e2)) unit, then evaluates with fuel - 1
  unfold LeanPoison.beval at h_eval
  -- After unfold: let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
  --                beval (fuel - 1) config₀ unfolded verbose
  simp at h_eval
  -- After simp: the let binding is inlined and fuel - 1 simplifies
  -- Handle fuel = 0 case separately
  cases fuel with
  | zero =>
    -- When fuel = 0, beval returns outOfFuel (contradiction)
    simp [pure] at h_eval
    apply congrFun (a := ()) at h_eval
    injection h_eval with h_contr
    cases h_contr
  | succ fuel' =>
    -- fuel = fuel' + 1, so fuel - 1 = fuel'
    -- So we have: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose = pure (.success config₁ v)
    -- Convert to applied form to work with the monadic structure
    apply congrFun (a := ()) at h_eval
    -- h_eval now contains: beval fuel' config₀ (Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit) verbose () = pure (.success config₁ v) ()
    have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
    -- Define the unfolded expression that kwhile expands to
    let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
    -- h_eval already contains the evaluation of this unfolded expression
    -- Convert from applied form to pure form for IH
    have h_beval_unfolded : LeanPoison.beval fuel' config₀ unfolded verbose = pure (.success config₁ v) := by
      funext _
      simp [pure]
      exact h_eval
    -- Apply IH: since fuel' < fuel'.succ, we can use IH for the unfolded expression
    -- The unfolded expression (ite) preserves memory monotonicity by IH (which internally uses the ite proof)
    exact IH fuel' h_fuel unfolded config₀ config₁ v h_beval_unfolded l h_contains

-- Memory Monotonicity Lemma: evaluation can only add memory locations, never remove them
-- This is a key property that follows from the fact that memory locations are never deallocated
lemma beval_memory_monotonic : ∀ (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  LeanPoison.beval fuel config₀ e verbose = pure (.success config₁ v) →
  ∀ l, config₀.memory.contains l → config₁.memory.contains l := by
  intro e fuel verbose config₀ config₁ v h_eval
  -- Proof by strong induction on fuel, then case analysis on expression
  induction fuel using Nat.strong_induction_on generalizing e config₀ config₁ v with
  | _ fuel IH =>
    intro l h_contains
    cases e with
    | num n | bool b | str s | unit =>
      -- Literals don't modify memory: config₁ = config₀
      -- All literals (numbers, booleans, strings, unit) follow the same pattern
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | var x =>
      -- Variables don't modify memory: config₁ = config₀
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval does variable lookup
        -- After unfold and apply congrFun, we need to handle the match on lookup
        -- Case analysis on variable lookup result using cases instead of split
        cases h_lookup : config₀.varEnv.lookup x with
        | some v_found =>
          -- Variable found: beval returns success with same config
          simp [h_lookup] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_eq_result h_eq_state
          injection h_eq_result with h_eq_config h_eq_val
          -- Now we have config₁ = config₀ from h_eq_config
          subst h_eq_config
          -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
          exact h_contains
        | none =>
          -- Variable not found: beval returns runtimeError (contradiction with success)
          simp [h_lookup] at h_eval
          simp [pure] at h_eval
          injection h_eval with h_contr
          -- h_contr : runtimeError ... = success ... is impossible
          cases h_contr
    | op e1 op e2 =>
      -- Binary operations: memory changes come from e1 and e2, evalOp doesn't allocate
      -- Use helper lemma for binary operations
      exact beval_memory_monotonic_op e1 e2 op fuel verbose config₀ config₁ v IH h_eval l h_contains
    | unaryop op e1 =>
      -- Unary operations: memory changes come from e1, evalUnaryOp doesn't modify memory
      -- Use helper lemma for unary operations
      exact beval_memory_monotonic_unaryop op e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | ite e1 e2 e3 =>
      -- Conditionals: memory changes from e1, then either e2 or e3
      -- Use helper lemma for conditionals
      exact beval_memory_monotonic_ite e1 e2 e3 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | newRef e1 =>
      -- newRef allocates memory: adds one location
      -- Use helper lemma for newRef
      exact beval_memory_monotonic_newRef e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | assign e1 e2 =>
      -- Assignment: memory changes from e1 and e2, but no new allocations
      -- Use helper lemma for assign
      exact beval_memory_monotonic_assign e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | deref e1 =>
      -- Dereference: memory changes only from e1, deref itself doesn't modify memory
      -- Use helper lemma for deref
      exact beval_memory_monotonic_deref e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | seq e1 e2 =>
      -- Sequence: memory changes from e1, then e2
      -- Use helper lemma for sequences
      exact beval_memory_monotonic_seq e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | kwhile e1 e2 =>
      -- While loops: needs careful handling of iteration
      -- Use helper lemma for kwhile
      exact beval_memory_monotonic_kwhile e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | vlet x e1 e2 =>
      -- Let binding: memory changes from e1, then e2
      -- Use helper lemma for vlet
      exact beval_memory_monotonic_vlet x e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | fn x paramType body returnType | pfn x paramType body returnType =>
      -- Function abstractions don't modify memory: config₁ = config₀
      -- Both fn and pfn just create closures without modifying config
      -- Unfold beval (use unfold, not simp, due to mutual recursion)
      unfold LeanPoison.beval at h_eval
      -- Apply unit argument to convert to applied form
      apply congrFun (a := ()) at h_eval
      -- Handle fuel check: if fuel = 0, beval returns outOfFuel (contradiction)
      cases fuel with
      | zero =>
        -- When fuel = 0, beval returns outOfFuel, not success
        simp [pure] at h_eval
        injection h_eval with h_contr
        -- h_contr : outOfFuel = success ... is impossible
        cases h_contr
      | succ fuel' =>
        -- When fuel > 0, beval returns success with same config
        simp [pure] at h_eval
        injection h_eval with h_eq_result h_eq_state
        injection h_eq_result with h_eq_config h_eq_val
        -- Now we have config₁ = config₀ from h_eq_config
        subst h_eq_config
        -- Goal: config₀.memory.contains l → config₀.memory.contains l (trivial)
        exact h_contains
    | app e1 e2 =>
      -- Function application: memory changes from e1, e2, and function body
      -- Use helper lemma for app
      exact beval_memory_monotonic_app e1 e2 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | rand e1 =>
      -- Random: memory changes only from e1
      -- Use helper lemma for rand
      exact beval_memory_monotonic_rand e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | frand e1 =>
      -- Faulty random: memory changes only from e1
      -- Use helper lemma for frand
      exact beval_memory_monotonic_frand e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | printInt e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printInt
      exact beval_memory_monotonic_printInt e1 fuel verbose config₀ config₁ v IH h_eval l h_contains
    | printString e1 =>
      -- Print: memory changes only from e1
      -- Use helper lemma for printString
      exact beval_memory_monotonic_printString e1 fuel verbose config₀ config₁ v IH h_eval l h_contains

end MemoryMonotonicity
