-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

import LeanProofs.NonInterference


open List

section TypeSystemEnforcesNonInterference

def terminatesToSucc (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel.succ c₀ e verbose = pure (Except.ok (c₁, out.toValue?.getD Value.unit)) ∧
    out.toExpr? = none

private lemma terminatesToSucc_of_terminatesTo :
  ∀ {e : Expr} {c₀ c₁ : Config} {out : ExprOrValue},
    terminatesTo e c₀ c₁ out → terminatesToSucc e c₀ c₁ out := by
  rintro e c₀ c₁ out ⟨n, v, h1, h2⟩
  rcases n with _ | ⟨n'⟩
  · unfold LeanPoison.beval at h1
    dsimp at h1
    apply congrFun (a := ()) at h1
    injection h1 with h1 _
    injection h1
  · exists n', v

def terminatesToWithFuel (fuel : Nat) (verbose : Bool) (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
  LeanPoison.beval fuel c₀ e verbose = pure (Except.ok (c₁, out.toValue?.getD Value.unit)) ∧
  out.toExpr? = none

private lemma terminatesTo_of_terminatesToWithFuel :
  ∀ {fuel : Nat} {v : Bool} {e : Expr} {c₀ c₁ : Config} {out : ExprOrValue},
    terminatesToWithFuel fuel v e c₀ c₁ out → terminatesTo e c₀ c₁ out := by
  rintro fuel v e c₀ c₁ out ⟨h1, h2⟩
  exists fuel, v

private lemma ExprOrValue.eq_value_of_toExpr?_eq_none_getD
    {o : ExprOrValue} {d v : Value}
    (hte : o.toExpr? = none)
    (hv : o.toValue?.getD d = v) :
    o = ExprOrValue.value v := by
  cases o with
  | expr e =>
    simp [ExprOrValue.toExpr?] at hte
  | value v =>
    simp [ExprOrValue.toExpr?] at hte
    have hv' := hv
    simp [ExprOrValue.toValue?, Option.getD] at hv'
    subst hv'
    rfl

private lemma agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
    {R : Regime} {s : InputSpec} {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv}
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
      qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    {l : Address} {qt : QTyp}
    (hlookup : s.locs.lookup l = some qt)
    (hpoison : qt.poison = false) :
    μ₁.lookup l = μ₂.lookup l := by
  have hpred := (hppt l qt hlookup).2
  have hpred_false : qt.pred.isSome = false := by
    simpa [hpoison] using hpred.symm
  simp [agreeOnCriticalInputsUnderRegimeSpec] at haociurs
  obtain ⟨hlocs, _⟩ := haociurs
  rw [List.forall₂_iff_get] at hlocs
  rcases hlocs with ⟨hsrle, hlocs⟩
  have hlookup_hash : s.locs.get? l = some qt := by
    simpa [MemoryTypeEnv.lookup] using hlookup
  have hmem_pair : (l, qt) ∈ s.locs.toList := by
    simpa using (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := s.locs) (k := l) (v := qt)).2 hlookup_hash
  have hmem := hmem_pair
  rw [List.mem_iff_get] at hmem
  rcases hmem with ⟨⟨i, hsi⟩, hmem⟩
  have hri := hsi
  rw [← hsrle] at hri
  specialize hlocs i hri hsi
  rw [hmem] at hlocs
  cases hr : R.locBits.get ⟨i, hri⟩
  · rw [hr] at hlocs
    rcases hlocs with _ | ⟨_, _, ⟨tp, hpred_some⟩, _, _⟩
    have : False := by
      have h := hpred_false
      simp [hpred_some, Option.isSome] at h
    exact this.elim
  · rw [hr] at hlocs
    rcases hlocs with ⟨_, _, hmu⟩ | _
    exact hmu

private lemma agreeOnCriticalInputsUnderRegimeSpec.var_eq_of_poison_false
    {R : Regime} {s : InputSpec} {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv}
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (hppf : ∀ (x : Name) (qt : QTyp), s.vars.lookup x = some qt →
        qt.poison = qt.pred.isSome)
    {x : Name} {qt : QTyp}
    (hlookup : s.vars.lookup x = some qt)
    (hpoison : qt.poison = false) :
    ρ₁.lookup x = ρ₂.lookup x := by
  have hpred := hppf x qt hlookup
  have hpred_false : qt.pred.isSome = false := by
    simpa [hpoison] using hpred.symm
  simp [agreeOnCriticalInputsUnderRegimeSpec] at haociurs
  obtain ⟨_, hvars⟩ := haociurs
  rw [List.forall₂_iff_get] at hvars
  rcases hvars with ⟨hsrve, hvars⟩
  have hlookup_list : List.lookup x s.vars = some qt := by
    simpa [VarTypeEnv.lookup] using hlookup
  obtain ⟨vars₁, vars₂, hsv_eq, _⟩ :=
    (List.lookup_eq_some_iff).1 hlookup_list
  have hmem_pair : (x, qt) ∈ s.vars := by
    simp [hsv_eq]
  have hmem := hmem_pair
  rw [List.mem_iff_get] at hmem
  rcases hmem with ⟨⟨i, hsi⟩, hmem⟩
  have hri : i < R.varBits.length := by
    simpa [hsrve] using hsi
  specialize hvars i hri hsi
  have hvars' := hvars
  rw [hmem] at hvars'
  rcases hr : R.varBits.get ⟨i, hri⟩
  · rw [hr] at hvars'
    rcases hvars' with _ | ⟨_, _, ⟨tp, hpred_some⟩, _, _⟩
    have : False := by
      have h := hpred_false
      simp [Option.isSome, hpred_some] at h
    exact this.elim
  · rw [hr] at hvars'
    rcases hvars' with ⟨_, _, hρ⟩ | _
    exact hρ

private lemma TypeSystemEnforcesNonInterference_unit
    {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx Expr.unit n = Except.ok res)
    (ht1 : terminatesTo Expr.unit (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo Expr.unit (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  simp [typecheckUnit] at htc
  injection htc with htc
  subst res
  have heval1_rw := heval1
  simp [LeanPoison.beval] at heval1_rw
  apply congrFun (a := ()) at heval1_rw
  injection heval1_rw with heval1_rw _
  injection heval1_rw with heval1_rw
  injection heval1_rw with heval1m heval1v
  have heval2_rw := heval2
  simp [LeanPoison.beval] at heval2_rw
  apply congrFun (a := ()) at heval2_rw
  injection heval2_rw with heval2_rw _
  injection heval2_rw with heval2_rw
  injection heval2_rw with heval2m heval2v
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    dsimp at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hp)
      rw [← heval1m, ← heval2m]
      simp [mkInit]
      exact hmu
  · have ho1 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 heval1v.symm
    have ho2 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 heval2v.symm
    right
    simp [ho1, ho2]

private lemma TypeSystemEnforcesNonInterference_num
    {x : Int} {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx (Expr.num x) n = Except.ok res)
    (ht1 : terminatesTo (Expr.num x) (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo (Expr.num x) (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  simp [typecheckInt] at htc
  injection htc with htc
  subst res
  have heval1_rw := heval1
  simp [LeanPoison.beval] at heval1_rw
  apply congrFun (a := ()) at heval1_rw
  injection heval1_rw with heval1_rw _
  injection heval1_rw with heval1_rw
  injection heval1_rw with heval1m heval1v
  have heval2_rw := heval2
  simp [LeanPoison.beval] at heval2_rw
  apply congrFun (a := ()) at heval2_rw
  injection heval2_rw with heval2_rw _
  injection heval2_rw with heval2_rw
  injection heval2_rw with heval2m heval2v
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    dsimp at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hp)
      rw [← heval1m, ← heval2m]
      simp [mkInit]
      exact hmu
  · have ho1 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 heval1v.symm
    have ho2 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 heval2v.symm
    right
    simp [ho1, ho2]

private lemma TypeSystemEnforcesNonInterference_bool
    {x : Bool} {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx (Expr.bool x) n = Except.ok res)
    (ht1 : terminatesTo (Expr.bool x) (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo (Expr.bool x) (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  simp [typecheckBool] at htc
  injection htc with htc
  subst res
  have heval1_rw := heval1
  simp [LeanPoison.beval] at heval1_rw
  apply congrFun (a := ()) at heval1_rw
  injection heval1_rw with heval1_rw _
  injection heval1_rw with heval1_rw
  injection heval1_rw with heval1m heval1v
  have heval2_rw := heval2
  simp [LeanPoison.beval] at heval2_rw
  apply congrFun (a := ()) at heval2_rw
  injection heval2_rw with heval2_rw _
  injection heval2_rw with heval2_rw
  injection heval2_rw with heval2m heval2v
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    dsimp at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hp)
      rw [← heval1m, ← heval2m]
      simp [mkInit]
      exact hmu
  · have ho1 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 heval1v.symm
    have ho2 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 heval2v.symm
    right
    simp [ho1, ho2]

private lemma TypeSystemEnforcesNonInterference_str
    {x : String} {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx (Expr.str x) n = Except.ok res)
    (ht1 : terminatesTo (Expr.str x) (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo (Expr.str x) (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  simp [typecheckString] at htc
  injection htc with htc
  subst res
  have heval1_rw := heval1
  simp [LeanPoison.beval] at heval1_rw
  apply congrFun (a := ()) at heval1_rw
  injection heval1_rw with heval1_rw _
  injection heval1_rw with heval1_rw
  injection heval1_rw with heval1m heval1v
  have heval2_rw := heval2
  simp [LeanPoison.beval] at heval2_rw
  apply congrFun (a := ()) at heval2_rw
  injection heval2_rw with heval2_rw _
  injection heval2_rw with heval2_rw
  injection heval2_rw with heval2m heval2v
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    dsimp at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hp)
      rw [← heval1m, ← heval2m]
      simp [mkInit]
      exact hmu
  · have ho1 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 heval1v.symm
    have ho2 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 heval2v.symm
    right
    simp [ho1, ho2]

private lemma TypeSystemEnforcesNonInterference_var
    {x : String} {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (hocrm : ∀ (et : ETyp),
        obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false)
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hppf : ∀ (x : Name) (qt : QTyp), s.vars.lookup x = some qt →
        qt.poison = qt.pred.isSome)
    (hctxp : ctx.pc = false)
    (hctxe : ctx.tagEnv = ∅)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (hctxsv : ∀ {x : Name} {qt : QTyp}, s.vars.lookup x = some qt →
        ctx.varEnv.lookup x = some qt)
    (hctxv : ∀ {x : Name} {qt : QTyp}, ctx.varEnv.lookup x = some qt →
        ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx (Expr.var x) n = Except.ok res)
    (ht1 : terminatesTo (Expr.var x) (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo (Expr.var x) (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  have heval1_rw := heval1
  simp [LeanPoison.beval] at heval1_rw
  apply congrFun (a := ()) at heval1_rw
  have ⟨v1, hv1⟩ : ∃ v, (mkInit μ₁ ρ₁).varEnv.lookup x = some v := by
    rcases hvel : (mkInit μ₁ ρ₁).varEnv.lookup x with _ | ⟨v⟩
    · rw [hvel] at heval1_rw
      dsimp at heval1_rw
      injection heval1_rw with heval1_rw _
      injection heval1_rw
    · exists v
  rw [hv1] at heval1_rw
  dsimp at heval1_rw
  injection heval1_rw with heval1_rw _
  injection heval1_rw with heval1_rw
  injection heval1_rw with heval1m heval1v
  have heval2_rw := heval2
  simp [LeanPoison.beval] at heval2_rw
  apply congrFun (a := ()) at heval2_rw
  have ⟨v2, hv2⟩ : ∃ v, (mkInit μ₂ ρ₂).varEnv.lookup x = some v := by
    rcases hvel : (mkInit μ₂ ρ₂).varEnv.lookup x with _ | ⟨v⟩
    · rw [hvel] at heval2_rw
      dsimp at heval2_rw
      injection heval2_rw with heval2_rw _
      injection heval2_rw
    · exists v
  rw [hv2] at heval2_rw
  dsimp at heval2_rw
  injection heval2_rw with heval2_rw _
  injection heval2_rw with heval2_rw
  injection heval2_rw with heval2m heval2v
  have ⟨qt, hqt⟩ : ∃ qt, ctx.varEnv.lookup x = some qt := by
    simp [typecheckVar] at htc
    rcases hl : ctx.varEnv.lookup x with _ | ⟨qt⟩
    · rw [hl] at htc
      dsimp at htc
      injection htc
    · exists qt
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    -- TODO: use typecheck_PExpr_preserves_typestate?
    have hctxres : res.memEnv' = ctx.memEnv := by
      rcases qt with ⟨qt, poison, pred⟩
      simp [typecheckVar] at htc
      rw [hqt] at htc
      dsimp at htc
      rcases pred with _ | ⟨pred⟩ <;> dsimp at htc
      · injection htc with htc
        subst res
        dsimp
      · rcases pred with ⟨t, a, pred, varenv⟩
        dsimp at htc
        rcases hctxt : ctx.tagEnv[t]? with _ | ⟨⟨_ | _, tvd⟩⟩
        all_goals {
          rw [hctxt] at htc
          dsimp at htc
          injection htc with htc
          subst res
          dsimp
        }
    rw [hctxres] at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hp)
      rw [← heval1m, ← heval2m]
      simp [mkInit]
      exact hmu
  · rcases het : obs.retEtyp? with _ | ⟨et⟩ <;> try (left; rfl)
    have ho1 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 heval1v.symm
    have ho2 := ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 heval2v.symm
    simp [ho1, ho2]
    have ⟨hre, hrp⟩ := hocrm et het
    rcases hsxv : s.vars.lookup x with _ | ⟨qt'⟩
    · simp [VarTypeEnv.lookup] at hsxv
      simp [VarTypeEnv.hasKey, VarTypeEnv.lookup] at hctxv
      have ⟨hqtpo, hqtpred⟩ := hctxv hqt (fun y hy => hsxv x y hy (refl _))
      simp [typecheckVar] at htc
      rw [hqt] at htc
      rcases qt with ⟨qte, qtpo, qtpred⟩
      dsimp at hqtpred
      rw [hqtpred] at htc
      dsimp at htc
      injection htc with htc
      subst res; dsimp at *
      rw [hctxp, hqtpo] at hrp
      simp [joinPoison] at hrp
    · have hctxsv' := hctxsv hsxv
      rw [hqt] at hctxsv'
      injection hctxsv' with hctxsv'
      subst qt'
      rcases hqtpo : qt.poison
      · have hmu :=
          agreeOnCriticalInputsUnderRegimeSpec.var_eq_of_poison_false
            (haociurs := haociurs) (hppf := hppf) (hlookup := hsxv) (hpoison := hqtpo)
        simp [mkInit] at hv1
        simp [mkInit] at hv2
        rw [hv1, hv2] at hmu
        injection hmu
      · have hqtpred := hppf x qt hsxv
        rw [hqtpo] at hqtpred
        simp [typecheckVar] at htc
        rw [hqt] at htc
        rcases qt with ⟨qte, qtpo, qtpred⟩
        dsimp at hqtpred
        rcases qtpred with _ | ⟨pk, parg, pbody, pv⟩ <;> try injection hqtpred
        dsimp at htc
        rw [hctxe, Std.HashMap.getElem?_empty] at htc
        dsimp at htc
        injection htc with htc
        subst res; dsimp at *
        rw [hctxp, hqtpo] at hrp
        simp [joinPoison] at hrp

private lemma TypeSystemEnforcesNonInterference_unaryop
    {op : UnaryOp} {e : Expr} {n : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    (ih :
      ∀ (m : ℕ), m < n →
      ∀ (e : Expr) (s : InputSpec) (obs : ObservableSpec),
      wfInputSpec s → wfObsSpec obs →
      ∀ (ctx : TypeContext), ctxMatchesInputSpec s ctx →
      ∀ (res : TypeResult), typecheck ctx e m = Except.ok res →
      (∀ (et : ETyp), obs.retEtyp? = some et →
        res.qualType.etyp = et ∧ res.qualType.poison = false) →
      (∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false) →
      wfInputSpec s → wfObsSpec obs → ctxMatchesInputSpec s ctx →
      ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
        (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
      inputsConformSpec s μ₁ ρ₁ → inputsConformSpec s μ₂ ρ₂ →
      runtimeInstantiatesCtx ctx μ₁ ρ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ →
      consistentRegimeSpec R s μ₁ ρ₁ → consistentRegimeSpec R s μ₂ ρ₂ →
      agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂ →
      terminatesTo e (mkInit μ₁ ρ₁) cf₁ o₁ → terminatesTo e (mkInit μ₂ ρ₂) cf₂ o₂ →
      observablesEqual obs cf₁ cf₂ o₁ o₂)
    (hiq1 : inputKeysUnique s)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt → qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hppf : ∀ (x : Name) (qt : QTyp), s.vars.lookup x = some qt → qt.poison = qt.pred.isSome)
    (hos : wfObsSpec obs)
    (hctxp : ctx.pc = false)
    (hctxte : ctx.tagEnv = ∅)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt → ctx.memEnv.lookup l = some qt)
    (hctxsv : ∀ {x : Name} {qt : QTyp}, s.vars.lookup x = some qt → ctx.varEnv.lookup x = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (hctxv : ∀ {x : Name} {qt : QTyp}, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = none)
    (hocrm : ∀ (et : ETyp), obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false)
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et → res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hics1 : inputsConformSpec s μ₁ ρ₁)
    (hics2 : inputsConformSpec s μ₂ ρ₂)
    (hric1 : runtimeInstantiatesCtx ctx μ₁ ρ₁)
    (hric2 : runtimeInstantiatesCtx ctx μ₂ ρ₂)
    (hcrs1 : consistentRegimeSpec R s μ₁ ρ₁)
    (hcrs2 : consistentRegimeSpec R s μ₂ ρ₂)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx (Expr.unaryop op e) n = Except.ok res)
    (ht1 : terminatesTo (Expr.unaryop op e) (mkInit μ₁ ρ₁) cf₁ o₁)
    (ht2 : terminatesTo (Expr.unaryop op e) (mkInit μ₂ ρ₂) cf₂ o₂) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  rcases n with _ | n <;> try (simp [typecheckUnaryOp] at htc; done)
  have ⟨fuel1, v1, heval1, hte1⟩ := terminatesToSucc_of_terminatesTo ht1
  have ⟨fuel2, v2, heval2, hte2⟩ := terminatesToSucc_of_terminatesTo ht2
  have ⟨res', htc'⟩ : ∃ res', typecheckExpr ctx e n = Except.ok res' := by
    simp [typecheckUnaryOp] at htc
    rcases hres' : typecheckExpr ctx e n with _ | ⟨res'⟩
    · rw [hres'] at htc
      simp [bind, Except.bind] at htc
    · exists res'
  have ⟨hocrm', hocmm'⟩ : ObsConstraints obs res' := by
    simp [ObsConstraints]
    simp [typecheckUnaryOp] at htc
    simp [bind, Except.bind] at htc
    rw [htc'] at htc
    dsimp at htc
    rcases res with ⟨⟨et, po, pred⟩, me, te, nl, nt⟩
    rcases res' with ⟨⟨et', po', pred'⟩, me', te', nl', nt'⟩
    dsimp at *
    have ⟨r, hr⟩ : ∃ r, opUnaryEType? op et' = some r := by
      rcases hr : opUnaryEType? op et' with _ | ⟨r⟩
      · rw [hr] at htc
        dsimp at htc
        injection htc
      · exists r
    rw [hr] at htc
    dsimp at htc
    dsimp [pure, Except.pure] at htc
    injection htc with htc
    injection htc with hqt hme hte hnl hnt
    injection hqt with het hpo hpred
    subst r me' te' nl' nt' pred
    constructor
    · rintro qt hqt
      have ⟨hrqt, hrp⟩ := hocrm qt hqt
      subst qt
      constructor
      · simp [opUnaryEType?] at hr
        rcases op; rcases et' <;> injection hr
      · rw [hctxp] at hpo
        simp [joinPoison] at hpo
        rw [hpo, hrp]
    · rintro l qt hqt
      have ⟨hmqt, hmp⟩ := hocmm l qt hqt
      constructor
      · apply hmqt
      · apply hmp
  have terminatesToUnaryOp :
      ∀ {fuel : Nat} {verbose : Bool} {μ : Memory} {ρ : VarEnv}
        {cf : Config} {out : ExprOrValue},
        LeanPoison.beval fuel.succ (mkInit μ ρ) (Expr.unaryop op e) verbose =
            pure (Except.ok (cf, out.toValue?.getD Value.unit)) →
        out.toExpr? = none →
        ∃ o',
          terminatesToWithFuel fuel verbose e (mkInit μ ρ) cf o' ∧
            LeanPoison.evalUnaryOp op (o'.toValue?.getD Value.unit) =
              some (out.toValue?.getD Value.unit) := by
    intro fuel verbose μ ρ cf out heval hout
    simp [LeanPoison.beval] at heval
    simp [pure, bind] at heval
    unfold EStateM.pure at heval
    unfold EStateM.bind at heval
    apply congrFun (a := ()) at heval
    rcases heval' : LeanPoison.beval fuel (mkInit μ ρ) e verbose () with ⟨⟨e'⟩ | ⟨cf', r⟩⟩
    · rw [heval'] at heval
      dsimp at heval
      injection heval with heval
      injection heval
    · rw [heval'] at heval
      dsimp at heval
      rcases heop : LeanPoison.evalUnaryOp op r with _ | ⟨val⟩
      · rw [heop] at heval
        dsimp at heval
        injection heval with heval
        injection heval
      · rw [heop] at heval
        dsimp at heval
        injection heval with heval
        injection heval with heval
        injection heval with hcf hval
        subst cf'
        have hval' : val = out.toValue?.getD Value.unit := by
          simpa using hval
        have heop_out : LeanPoison.evalUnaryOp op r =
            some (out.toValue?.getD Value.unit) := by
          simpa [hval'] using heop
        refine ⟨ExprOrValue.value r, ?_, ?_⟩
        · constructor
          · simp [pure]
            unfold EStateM.pure
            funext x
            rcases x with ⟨⟩
            simp [ExprOrValue.toValue?]
            exact heval'
          · simp [ExprOrValue.toExpr?]
        · simpa [ExprOrValue.toValue?, Option.getD] using heop_out
    · rw [heval'] at heval
      dsimp at heval
      injection heval
  have ⟨o₁', ⟨heval1', hte1'⟩, heop1'⟩ := terminatesToUnaryOp heval1 hte1
  have ⟨o₂', ⟨heval2', hte2'⟩, heop2'⟩ := terminatesToUnaryOp heval2 hte2
  have ⟨hom, hor⟩ : observablesEqual obs cf₁ cf₂ o₁' o₂' := by
    have hn := Nat.lt_add_right 1 (Nat.lt_add_one n)
    have his : wfInputSpec s := ⟨hiq1, hppt, hppf⟩
    have hctx : ctxMatchesInputSpec s ctx :=
      ⟨hctxp, hctxte, hctxsm, hctxsv, hctxm, hctxv⟩
    have ht1' := terminatesTo_of_terminatesToWithFuel ⟨heval1', hte1'⟩
    have ht2' := terminatesTo_of_terminatesToWithFuel ⟨heval2', hte2'⟩
    apply ih
      n hn e s obs his hos ctx hctx
      res' htc' hocrm' hocmm' his hos hctx
      μ₁ μ₂ ρ₁ ρ₂ R cf₁ cf₂ o₁' o₂'
      hics1 hics2 hric1 hric2 hcrs1 hcrs2 haociurs
      ht1' ht2'
  simp [observablesEqual]
  constructor
  · exact hom
  · rcases hor with (hor | hor) <;> try (left; exact hor)
    right
    have ⟨v₁, hv1⟩ : ∃v₁, o₁ = ExprOrValue.value v₁ := by
      exists (o₁.toValue?.getD Value.unit)
      exact ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte1 rfl
    have ⟨v₂, hv2⟩: ∃v₂, o₂ = ExprOrValue.value v₂ := by
      exists (o₂.toValue?.getD Value.unit)
      exact ExprOrValue.eq_value_of_toExpr?_eq_none_getD hte2 rfl
    rw [hor] at heop1'
    rw [heop1'] at heop2'
    injection heop2' with ho
    rw [hv1, hv2] at ho
    simp [ExprOrValue.toValue?] at ho
    rw [hv1, hv2, ho]

-- Type system enforces Non-Interference
theorem TypeSystemEnforcesNonInterference (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  TypeSystemEnforcesNonInterference_spec e s obs
:= by
  rintro _ _ ctx hctx ⟨fuel_tc, res, htc, ⟨hocrm, hocmm⟩⟩
  induction fuel_tc using Nat.strong_induction_on
    generalizing e s obs ctx hctx res hocrm hocmm with
  | _ n ih =>
    rintro ⟨hiq1, hppt, hppf⟩ hos _ μ₁ μ₂ ρ₁ ρ₂ R cf₁ cf₂ o₁ o₂
           hics1 hics2 hric1 hric2 hcrs1 hcrs2 haociurs ht1 ht2
    rcases hctx with ⟨hctxp, hctxte, hctxsm, hctxsv, hctxm, hctxv⟩
    simp [NonInterferenceSpec] at ih
    cases e with
    | unit =>
      exact
        TypeSystemEnforcesNonInterference_unit
          (hocmm := hocmm) (hppt := hppt)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (haociurs := haociurs) htc ht1 ht2
    | num _ =>
      exact
        TypeSystemEnforcesNonInterference_num
          (hocmm := hocmm) (hppt := hppt)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (haociurs := haociurs) htc ht1 ht2
    | bool _ =>
      exact
        TypeSystemEnforcesNonInterference_bool
          (hocmm := hocmm) (hppt := hppt)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (haociurs := haociurs) htc ht1 ht2
    | str _ =>
      exact
        TypeSystemEnforcesNonInterference_str
          (hocmm := hocmm) (hppt := hppt)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (haociurs := haociurs) htc ht1 ht2
    | var _ =>
      exact
        TypeSystemEnforcesNonInterference_var
          (hocrm := hocrm) (hocmm := hocmm)
          (hppt := hppt) (hppf := hppf)
          (hctxp := hctxp) (hctxe := hctxte)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (hctxsv := hctxsv) (hctxv := hctxv)
          (haociurs := haociurs) htc ht1 ht2
    | unaryop _ _ =>
      exact
        TypeSystemEnforcesNonInterference_unaryop
          (ih := ih)
          (hiq1 := hiq1) (hppt := hppt) (hppf := hppf) (hos := hos)
          (hctxp := hctxp) (hctxte := hctxte)
          (hctxsm := hctxsm) (hctxsv := hctxsv)
          (hctxm := hctxm) (hctxv := hctxv)
          (hocrm := hocrm) (hocmm := hocmm)
          (hics1 := hics1) (hics2 := hics2)
          (hric1 := hric1) (hric2 := hric2)
          (hcrs1 := hcrs1) (hcrs2 := hcrs2)
          (haociurs := haociurs)
          htc ht1 ht2
    | op _ _ _ =>
      sorry
    | ite _ _ _ =>
      sorry
    | newRef _ =>
      sorry
    | assign _ _ =>
      sorry
    | deref _ =>
      sorry
    | seq _ _ =>
      sorry
    | kwhile _ _ =>
      sorry
    | vlet _ _ _ =>
      sorry
    | fn _ _ _ _ =>
      sorry
    | pfn _ _ _ _ =>
      sorry
    | app _ _ =>
      sorry
    | rand _ =>
      sorry
    | frand _ =>
      sorry
    | printString _ =>
      sorry
    | printInt _ =>
      sorry

end TypeSystemEnforcesNonInterference
