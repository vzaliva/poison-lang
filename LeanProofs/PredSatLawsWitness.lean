/-
  PredSatLawsWitness.lean — `PredSatLaws` is satisfiable at a tag meaning with a
  matchable guard.

  `PredSatLaws predSat tm` is a hypothesis of the fault-robustness theorem, so the
  theorem only says something when the laws can be met.  This module gives a concrete
  model: the tag meaning that interprets tag `0` as the guard `v => v`, and the
  satisfaction relation "the checked value is `true`".  It also exhibits a context that
  respects this tag meaning and in which `matchGuard` selects tag `0`, so the premises
  of `PredSatLaws.match_iff` are met and the law is exercised.

  The module is a leaf of the import graph; nothing on the fault-robustness proof path
  depends on it.
-/

import LeanProofs.StepFRIte

open Std

namespace PredSatLawsWitness

/-- Descriptor of the guard `v => v`. -/
def idDesc : GuardDesc := { argName := "v", body := PExpr.var "v", capEnv := [] }

/-- Tag meaning that interprets tag `0` as the guard `v => v`. -/
def idTm : TagMeaning := (∅ : TagMeaning).update 0 idDesc

/-- Satisfaction relation of the guard `v => v`: the checked value is `true`. -/
def idSat : PredSat := fun _ _ _ v => v = Value.bool true

private theorem idTm_lookup_eq {k : Tag} {d : GuardDesc} (h : idTm.lookup k = some d) :
    d = idDesc := by
  by_cases hk : (0 : Tag) = k
  · subst hk
    simpa [idTm, TagMeaning.lookup, TagMeaning.update] using h.symm
  · simp [idTm, TagMeaning.lookup, TagMeaning.update, hk] at h

/-- A pure expression equal to the guard body `v` with the argument replaced by the
    variable `x` is the variable `x`. -/
private theorem equalWithEnvs_var_arg {pe : PExpr} {sCap : CapturedVarEnv} {x : Name} :
    ∀ {fuel : Nat},
      PExpr.equalWithEnvs (PExpr.var "v") [] pe sCap (some ("v", PExpr.var x)) fuel = true →
      pe = PExpr.var x := by
  intro fuel h
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel =>
      by_cases hx : x = "v"
      · subst hx
        cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
      · have hbeq : (PExpr.var x == PExpr.var "v") = false := by
          simp [BEq.beq, beqPExpr, hx]
        cases fuel with
        | zero => simp [PExpr.equalWithEnvs, hbeq] at h
        | succ fuel =>
            cases pe <;> simp_all [PExpr.equalWithEnvs]

/-- A pure expression equal to the guard body `v` with the argument replaced by a
    dereference is itself a dereference. -/
private theorem equalWithEnvs_deref_arg {pe : PExpr} {sCap : CapturedVarEnv} {x : Name}
    {fuel : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "v") [] pe sCap
      (some ("v", PExpr.deref (PExpr.var x))) fuel = true) :
    ∃ pe', pe = PExpr.deref pe' := by
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel =>
      have hbeq : (PExpr.deref (PExpr.var x) == PExpr.var "v") = false := by
        simp [BEq.beq, beqPExpr]
      cases fuel with
      | zero => simp [PExpr.equalWithEnvs, hbeq] at h
      | succ fuel =>
          cases pe <;> simp_all [PExpr.equalWithEnvs]

private theorem toPExpr?_eq_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.var x)) : e = Expr.var x := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_eq_deref {e : Expr} {pe : PExpr}
    (h : e.toPExpr? = some (PExpr.deref pe)) : ∃ e', e = Expr.deref e' := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

/-- The laws hold for the guard `v => v` read as "the checked value is `true`".

    `match_iff`: a condition that matches the guard is the owner variable itself, so it
    evaluates to the owner's value.  A reference owner cannot arise for a condition of
    type `bool`, because a dereference evaluates to a number.

    `mem_footprint`: the relation reads neither the realisation map nor the memory. -/
theorem predSatLaws_idSat : PredSatLaws idSat idTm := by
  refine ⟨?_, ?_⟩
  · intro condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hric hterm
    obtain ⟨pe, hpe, hown⟩ := matchGuard_ok_matched_owner ctx condition k deps hmatch
    rcases hown with
      ⟨x, qt, arg, body, cap, hlookup, hpred, heq⟩ |
      ⟨x, qt, ls, arg, body, cap, hlookup, hetyp, hne, hall, heq⟩
    · have hdesc : (⟨arg, body, cap⟩ : GuardDesc) = idDesc :=
        idTm_lookup_eq (hwf.1
          (GuardDescInEnvsDeep.intro qt k ⟨arg, body, cap⟩
            (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt))
            (by simp [qtypGuardDesc?, hpred])))
      simp only [idDesc, GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      have hcond : condition = Expr.var x := toPExpr?_eq_var (equalWithEnvs_var_arg heq ▸ hpe)
      subst hcond
      obtain ⟨v', hρ, _, hv⟩ := terminatesTo_var_inv' x _ _ _ hterm
      subst hv
      exact ⟨Value.bool b, Or.inl ⟨x, qt, "v", PExpr.var "v", [], hlookup, hpred, hρ⟩,
        by simp [idSat]⟩
    · exfalso
      obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
        have hlist : ls.toList.isEmpty = false := by
          rw [ExtTreeSet.isEmpty_toList]; exact hne
        cases htl : ls.toList with
        | nil => simp [htl] at hlist
        | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
      obtain ⟨memQt, hmem, hpred⟩ := hall l hl
      have hdesc : (⟨arg, body, cap⟩ : GuardDesc) = idDesc :=
        idTm_lookup_eq (hwf.1
          (GuardDescInEnvsDeep.intro memQt k ⟨arg, body, cap⟩
            (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt))
            (by simp [qtypGuardDesc?, hpred])))
      simp only [idDesc, GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      obtain ⟨pe', rfl⟩ := equalWithEnvs_deref_arg heq
      obtain ⟨e', rfl⟩ := toPExpr?_eq_deref hpe
      obtain ⟨_, _, n, _, _, hv, _⟩ := terminatesTo_deref_inv' e' _ _ _ hterm
      cases hv
  · intro _ _ _ _ _ _ _ _ _
    exact Iff.rfl

/-! ### The law is exercised

The context `y : {v : bool | v}` (tag `0`) respects `idTm`, and `matchGuard` selects
tag `0` for the condition `y`, so the premises of `PredSatLaws.match_iff` are met. -/

/-- The type of a clean boolean guarded by tag `0` with the guard `v => v`. -/
def guardedBool : QTyp :=
  { etyp := ETyp.bool, poison := false,
    pred := Predicate.guardClosure 0 "v" (PExpr.var "v") [] }

/-- The context `y : {v : bool | v}`. -/
def guardedCtx : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅,
    varEnv := (∅ : VarTypeEnv).update "y" guardedBool, tagEnv := ∅,
    nextLoc := 0, nextTag := 1, pureCtx := false }

theorem guardedCtx_wf : wfTagMeaningCtx idTm guardedCtx := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
    have hroot : qtRoot = guardedBool := by
      by_cases hx : x = "y"
      · subst hx
        have hupd := VarTypeEnv_lookup_update_eq (∅ : VarTypeEnv) "y" guardedBool
        simp only [guardedCtx] at hlookup
        rw [hupd] at hlookup
        exact (Option.some.inj hlookup).symm
      · have hupd := VarTypeEnv_lookup_update_ne (∅ : VarTypeEnv) "y" x guardedBool hx
        simp only [guardedCtx] at hlookup
        rw [hupd] at hlookup
        simp [VarTypeEnv.lookup] at hlookup
    subst hroot
    have hqt : qt = guardedBool :=
      QTypInQTyp_eq_of_nonFunctionTarget hinq
        (by simp [guardedBool, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    subst hqt
    simp [qtypGuardDesc?, guardedBool] at hdesc
    obtain ⟨rfl, rfl⟩ := hdesc
    simp [idTm, TagMeaning.lookup, TagMeaning.update, idDesc]
  | inMem _ _ l _ qtRoot hlookup hinq =>
    simp [guardedCtx, MemoryTypeEnv.lookup] at hlookup

theorem guardedCtx_matches :
    ∃ deps, matchGuard (Expr.var "y") guardedCtx.memEnv guardedCtx.varEnv 10 = .ok (0, deps) :=
  ⟨_, rfl⟩

end PredSatLawsWitness
