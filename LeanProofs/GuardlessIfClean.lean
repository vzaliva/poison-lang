import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Poison
import LeanProofs.Properties
import Mathlib.Tactic

open Std

/-- Extract the guard tag from a qualified type's predicate, if present. -/
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

/-- A qualified type is guardless whenever it is clean. -/
def guardlessIfCleanQTyp (qt : QTyp) : Prop :=
  qt.poison = false → qtypGuardTag qt = none

def nonClosureQTyp (qt : QTyp) : Prop :=
  match qt.etyp with
  | ETyp.arrow _ _ _ _ => False
  | ETyp.parrow _ _ _ _ => False
  | _ => True

mutual /- TODO: can be rewritten using `deepVarEnvProperty` -/

inductive guardlessIfCleanQTypDeep : QTyp → Prop
| intro (qt : QTyp) :
  guardlessIfCleanQTyp qt →
  guardlessIfCleanClosureEnv qt →
  guardlessIfCleanQTypDeep qt

/-- Clean qualified types in a memory typing environment must carry no guard tags. -/
inductive guardlessIfCleanMem : MemoryTypeEnv → Prop
| intro (locs : MemoryTypeEnv) :
  (∀ {l qt}, locs.lookup l = some qt → guardlessIfCleanQTypDeep qt) →
  guardlessIfCleanMem locs

/-- Clean qualified types in a variable typing environment must carry no guard tags. -/
inductive guardlessIfCleanVars : VarTypeEnv → Prop
| intro (vars : VarTypeEnv) :
  (∀ {x qt}, vars.lookup x = some qt → guardlessIfCleanQTypDeep qt) →
  guardlessIfCleanVars vars

inductive guardlessIfCleanClosureEnv : QTyp → Prop
| arrow (qt : QTyp) (env : VarTypeEnv) :
  qt.etyp = ETyp.arrow _ _ _ (FnTClosure.mk _ _ env) →
  guardlessIfCleanVars env →
  guardlessIfCleanClosureEnv qt
| parrow (qt : QTyp) (env : VarTypeEnv) :
  qt.etyp = ETyp.parrow _ _ _ (PFnTClosure.mk _ _ env) →
  guardlessIfCleanVars env →
  guardlessIfCleanClosureEnv qt
| other (qt : QTyp) :
  nonClosureQTyp qt →
  guardlessIfCleanClosureEnv qt

end /- mutual -/


section GuardlessIfCleanLemmas

private lemma guardlessIfCleanQTypDeep.of_nonClosure
    {qt : QTyp} :
    guardlessIfCleanQTyp qt →
    nonClosureQTyp qt →
    guardlessIfCleanQTypDeep qt := by
  intro hqt hnc
  exact guardlessIfCleanQTypDeep.intro qt hqt (guardlessIfCleanClosureEnv.other qt hnc)

private lemma guardlessIfCleanMem.lookup
    {locs : MemoryTypeEnv}
    (hmem : guardlessIfCleanMem locs)
    {l : Address} {qt : QTyp}
    (hlookup : locs.lookup l = some qt) :
    guardlessIfCleanQTypDeep qt := by
  cases hmem with
  | intro _ hlocs => exact hlocs hlookup

private lemma guardlessIfCleanVars.lookup
    {vars : VarTypeEnv}
    (hvars : guardlessIfCleanVars vars)
    {x : Name} {qt : QTyp}
    (hlookup : vars.lookup x = some qt) :
    guardlessIfCleanQTypDeep qt := by
  cases hvars with
  | intro _ hlookup' => exact hlookup' hlookup

private lemma guardlessIfCleanQTypDeep.guardless
    {qt : QTyp} :
    guardlessIfCleanQTypDeep qt → guardlessIfCleanQTyp qt := by
  intro h
  cases h with
  | intro _ hguard _ => exact hguard

private lemma guardlessIfCleanQTypDeep.closure
    {qt : QTyp} :
    guardlessIfCleanQTypDeep qt → guardlessIfCleanClosureEnv qt := by
  intro h
  cases h with
  | intro _ _ hclosure => exact hclosure

private lemma guardlessIfCleanClosureEnv.congr
    {qt₁ qt₂ : QTyp}
    (het : qt₁.etyp = qt₂.etyp) :
    guardlessIfCleanClosureEnv qt₁ →
    guardlessIfCleanClosureEnv qt₂ := by
  cases qt₁ with
  | mk etyp poison₁ pred₁ =>
      cases qt₂ with
      | mk etyp₂ poison₂ pred₂ =>
          have het' : etyp = etyp₂ := het
          subst het'
          intro hclosure
          cases hclosure with
          | other _ hnc =>
              exact guardlessIfCleanClosureEnv.other _ hnc
          | arrow _ env hetyp hvars =>
            dsimp at hetyp
            rw [hetyp]
            apply guardlessIfCleanClosureEnv.arrow
            · rfl
            · apply hvars
          | parrow _ env hetyp hvars =>
            dsimp at hetyp
            rw [hetyp]
            apply guardlessIfCleanClosureEnv.parrow
            · rfl
            · apply hvars

/-- Updating a memory environment at a location with a guardless-qualified type preserves the invariant. -/
private lemma guardlessIfCleanMem.updateMemEnv
    {locs : MemoryTypeEnv} {l : Address} {qt : QTyp} :
    guardlessIfCleanMem locs →
    guardlessIfCleanQTypDeep qt →
    guardlessIfCleanMem (updateMemEnv locs l qt) := by
  classical
  intro hmem hqt
  cases hmem with
  | intro locs hlocs =>
      refine guardlessIfCleanMem.intro _ ?_
      intro l' qt' hlookup
      by_cases hbeq : l == l'
      · have hlookup_if :
            (if l == l then some qt else locs[l]?) = some qt' := by
          simp [_root_.updateMemEnv, MemoryTypeEnv.lookup] at hlookup
          simp [Std.HashMap.getElem?_insert] at hlookup
          simp [beq_iff_eq] at hbeq
          simp [hbeq] at hlookup
          simp [hlookup]
        have : qt = qt' := by
          simpa using hlookup_if
        subst this
        simpa using hqt
      · have hlookup_if :
            (if l == l' then some qt else locs[l']?) = some qt' := by
          simpa [MemoryTypeEnv.lookup, _root_.updateMemEnv, Std.HashMap.getElem?_insert] using hlookup
        have hlookup_old' : locs[l']? = some qt' := by
          simpa [hbeq] using hlookup_if
        have hlookup_old : locs.lookup l' = some qt' := by
          simpa [MemoryTypeEnv.lookup] using hlookup_old'
        exact hlocs hlookup_old

/-- Removing a location from a memory environment preserves the guardless invariant. -/
private lemma guardlessIfCleanMem.erase
    {locs : MemoryTypeEnv} {l : Address} :
    guardlessIfCleanMem locs →
    guardlessIfCleanMem (Std.HashMap.erase locs l) := by
  classical
  intro hmem
  cases hmem with
  | intro locs hlookup =>
      refine guardlessIfCleanMem.intro _ ?_
      intro l' qt hlookup'
      have hlookup_if :
          (if l' == l then none else locs[l']?) = some qt := by
        simp [MemoryTypeEnv.lookup, Std.HashMap.getElem?_erase] at hlookup'
        simp
        constructor
        · intro h
          apply hlookup'.1
          rw [h]
        · apply hlookup'.2
      by_cases hbeq : l' == l
      · have : (if l' == l then none else locs[l']?) = none := by
          simp [hbeq]
        simp [hbeq] at hlookup_if
      · have hlookup_old : locs.lookup l' = some qt := by
          simpa [MemoryTypeEnv.lookup, hbeq] using hlookup_if
        exact hlookup hlookup_old

/-- The empty memory environment trivially satisfies the guardless invariant. -/
private lemma guardlessIfCleanMem.empty :
    guardlessIfCleanMem ({} : MemoryTypeEnv) := by
  refine guardlessIfCleanMem.intro _ ?_
  intro l qt hlookup
  have : (({} : MemoryTypeEnv).lookup l) = none := by
    simp [MemoryTypeEnv.lookup]
  simp at hlookup
  rw [this] at hlookup
  cases hlookup

private def joinMemEnvsPred : Predicate → Predicate → Predicate
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

private def joinMemEnvsFn (_ : Address) (oq₁ oq₂ : Option QTyp) : Option QTyp :=
  match oq₁, oq₂ with
  | some qt₁, none => some qt₁
  | none, some qt₂ => some qt₂
  | some ⟨t₁, p₁, pred₁⟩, some ⟨t₂, p₂, pred₂⟩ =>
      if t₁ == t₂ then some ⟨t₁, joinPoison p₁ p₂, joinMemEnvsPred pred₁ pred₂⟩
      else none
  | none, none => none

private lemma joinPoison_eq_false {p₁ p₂ : Poison} :
    joinPoison p₁ p₂ = false ↔ p₁ = false ∧ p₂ = false := by
  cases p₁ <;> cases p₂ <;> simp [joinPoison]

private lemma qtypGuardTag_eq_none_iff {qt : QTyp} :
    qtypGuardTag qt = none ↔ qt.pred = Predicate.noPred := by
  cases h : qt.pred <;> simp [h, qtypGuardTag]

private lemma joinMemEnvsPred_of_noPred_left {pred : Predicate} :
    joinMemEnvsPred Predicate.noPred pred = Predicate.noPred := by
  simp [joinMemEnvsPred]

private lemma guardless_joinMemEnvsFn_some
    {locs₁ locs₂ : MemoryTypeEnv}
    (hmem₁ : guardlessIfCleanMem locs₁)
    (hmem₂ : guardlessIfCleanMem locs₂)
    {l : Address} {qt : QTyp}
    (hres :
      joinMemEnvsFn l (locs₁.get? l) (locs₂.get? l) = some qt) :
    guardlessIfCleanQTypDeep qt := by
  classical
  unfold joinMemEnvsFn at hres
  cases h₁ : locs₁[l]? with
  | none =>
      cases h₂ : locs₂[l]? with
      | none =>
          simp [h₁, h₂] at hres
      | some qt₂ =>
          have hlookup₂ : locs₂.lookup l = some qt₂ := by
            simpa [MemoryTypeEnv.lookup] using h₂
          have hqt₂ :=
            guardlessIfCleanMem.lookup hmem₂ hlookup₂
          have hqt_eq : qt = qt₂ := by
            have := hres
            simp [h₁, h₂] at this
            exact Option.some.inj (by rw [this])
          simpa [hqt_eq]
  | some qt₁ =>
      cases h₂ : locs₂[l]? with
      | none =>
          have hlookup₁ : locs₁.lookup l = some qt₁ := by
            simpa [MemoryTypeEnv.lookup] using h₁
          have hqt₁ :=
            guardlessIfCleanMem.lookup hmem₁ hlookup₁
          have hqt_eq : qt = qt₁ := by
            have := hres
            simp [h₁, h₂] at this
            exact Option.some.inj (by rw [this])
          simpa [hqt_eq]
      | some qt₂ =>
          have hlookup₁ : locs₁.lookup l = some qt₁ := by
            simpa [MemoryTypeEnv.lookup] using h₁
          have hqt₁ := guardlessIfCleanMem.lookup hmem₁ hlookup₁
          cases qt₁ with
          | mk t₁ p₁ pred₁ =>
              cases qt₂ with
              | mk t₂ p₂ pred₂ =>
                  by_cases hteq : t₁ == t₂
                  · have hqt_eq :
                      qt =
                        ⟨t₁, joinPoison p₁ p₂, joinMemEnvsPred pred₁ pred₂⟩ := by
                        have := hres
                        simp [h₁, h₂, hteq] at this
                        exact Option.some.inj (by rw [this])
                    have hguard₁ :=
                      guardlessIfCleanQTypDeep.guardless hqt₁
                    have hclosure₁ :=
                      guardlessIfCleanQTypDeep.closure hqt₁
                    have hnew :
                        guardlessIfCleanQTypDeep
                          ⟨t₁, joinPoison p₁ p₂, joinMemEnvsPred pred₁ pred₂⟩ := by
                      refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                      · intro hclean
                        have hp_false :
                            p₁ = false := (joinPoison_eq_false.mp hclean).1
                        have htag_none :
                            qtypGuardTag ⟨t₁, p₁, pred₁⟩ = none :=
                          hguard₁ hp_false
                        have hpred₁ :
                            pred₁ = Predicate.noPred :=
                          (qtypGuardTag_eq_none_iff.mp htag_none)
                        have hpred_join :
                            joinMemEnvsPred pred₁ pred₂ = Predicate.noPred := by
                          simpa [hpred₁] using
                            joinMemEnvsPred_of_noPred_left (pred := pred₂)
                        simp [qtypGuardTag, hpred_join]
                      · have : (⟨t₁, p₁, pred₁⟩ : QTyp).etyp =
                            (⟨t₁, joinPoison p₁ p₂,
                              joinMemEnvsPred pred₁ pred₂⟩ : QTyp).etyp := rfl
                        exact guardlessIfCleanClosureEnv.congr this hclosure₁
                    simpa [hqt_eq] using hnew
                  · have := hres
                    simp [h₁, h₂, hteq] at this

private lemma guardlessIfCleanMem_joinMemEnvs_go
    {locs₁ locs₂ : MemoryTypeEnv}
    (hmem₁ : guardlessIfCleanMem locs₁)
    (hmem₂ : guardlessIfCleanMem locs₂)
    {ks : List Address}
    {acc : MemoryTypeEnv}
    (hacc : guardlessIfCleanMem acc) :
    guardlessIfCleanMem
      (combineMaps.go locs₁ locs₂ joinMemEnvsFn ks acc) := by
  classical
  induction ks generalizing acc with
  | nil =>
      simpa [combineMaps.go] using hacc
  | cons k ks ih =>
      dsimp [combineMaps.go]
      cases hres :
          joinMemEnvsFn k (locs₁.get? k) (locs₂.get? k) with
      | none =>
          have hacc' :
              guardlessIfCleanMem (Std.HashMap.erase acc k) :=
            guardlessIfCleanMem.erase hacc
          exact ih hacc'
      | some qt =>
          have hqt :
              guardlessIfCleanQTypDeep qt :=
            guardless_joinMemEnvsFn_some hmem₁ hmem₂ hres
          have hacc' :
              guardlessIfCleanMem (Std.HashMap.insert acc k qt) := by
            simpa [updateMemEnv] using
              guardlessIfCleanMem.updateMemEnv hacc hqt
          exact ih hacc'

/-- Joining two memory environments that both satisfy the guardless invariant results in a guardless environment. -/
private lemma guardlessIfCleanMem_joinMemEnvs
    {locs₁ locs₂ : MemoryTypeEnv} :
    guardlessIfCleanMem locs₁ →
    guardlessIfCleanMem locs₂ →
    guardlessIfCleanMem (joinMemEnvs locs₁ locs₂) := by
  classical
  intro hmem₁ hmem₂
  have hbase : guardlessIfCleanMem ({} : MemoryTypeEnv) :=
    guardlessIfCleanMem.empty
  simp [joinMemEnvs, combineMaps]
  have h := guardlessIfCleanMem_joinMemEnvs_go hmem₁ hmem₂
      (ks := (locs₁.keys ++ locs₂.keys).dedup)
      (acc := ({} : MemoryTypeEnv))
      hbase
  unfold joinMemEnvsFn at h
  unfold joinMemEnvsPred at h
  convert h with l q1 q2
  ext x
  rcases q1 with _ | ⟨q1⟩ <;> rcases q2 with _ | ⟨q2⟩ <;> try (dsimp; rfl)
  · cases q1; dsimp; rfl
  · cases q1; cases q2; dsimp
    simp only [Option.ite_none_right_eq_some, Option.some.injEq]
    simp only [beq_iff_eq, and_congr_right_iff]
    intro h
    rw [h]
    rfl

/-- Updating a variable environment with a guardless-qualified type preserves the invariant. -/
private lemma guardlessIfCleanVars_update
    {vars : VarTypeEnv} {x : Name} {qt : QTyp} :
    guardlessIfCleanVars vars →
    guardlessIfCleanQTypDeep qt →
    guardlessIfCleanVars (VarTypeEnv.update vars x qt) := by
  classical
  intro hvars hqt
  cases hvars with
  | intro vars hlookup_old =>
      refine guardlessIfCleanVars.intro _ ?_
      intro y qt' hlookup
      have hlookup_if :
          (match y == x with
            | true => some qt
            | false => vars.lookup y) = some qt' := by
        simpa [VarTypeEnv.lookup, VarTypeEnv.update, List.lookup] using hlookup
      by_cases hbeq : y == x
      · have hqt_eq : qt = qt' := by
          have : some qt = some qt' := by
            simpa [hbeq] using hlookup_if
          simpa using Option.some.inj this
        subst hqt_eq
        simpa using hqt
      · have hlookup_old' : vars.lookup y = some qt' := by
          simpa [hbeq] using hlookup_if
        exact hlookup_old hlookup_old'

private lemma guardlessIfClean_runWhileFixpoint
    {fuelBound : Nat}
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuelBound →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (e₁ e₂ : Expr) :
    ∀ {ctx : TypeContext} {fuelFix : Nat} {pureGuard : Bool}
      {guardOpt : Option (Tag × Deps)}
      {pcFinal memFinal tagFinal : _} {nextLocFinal : Address} {nextTagFinal : Tag},
      guardlessIfCleanMem ctx.memEnv →
      guardlessIfCleanVars ctx.varEnv →
      fuelFix < fuelBound →
      runWhileFixpoint ctx e₁ e₂ fuelFix pureGuard guardOpt =
          .ok (pcFinal, memFinal, tagFinal, nextLocFinal, nextTagFinal) →
      guardlessIfCleanMem memFinal := by
  classical
  intro ctx fuelFix
  induction fuelFix generalizing ctx with
  | zero =>
      intro pureGuard guardOpt pcFinal memFinal tagFinal nextLocFinal nextTagFinal hmem hvars hfuel_lt hfix
      have hcontr := hfix
      simp [runWhileFixpoint] at hcontr
  | succ fuelInner ih =>
      intro pureGuard guardOpt pcFinal memFinal tagFinal nextLocFinal nextTagFinal hmem hvars hfuel_lt hfix
      have hfuel_inner_lt :
          fuelInner < fuelBound :=
        Nat.lt_trans (Nat.lt_succ_self _) hfuel_lt
      set ctxForGuard : TypeContext :=
        if pureGuard then { ctx with pureCtx := true } else ctx with hctxForGuard
      have hmem_ctxForGuard : guardlessIfCleanMem ctxForGuard.memEnv := by
        by_cases hp : pureGuard
        · simp [ctxForGuard, hp, hmem]
        · simp [ctxForGuard, hp, hmem]
      have hvars_ctxForGuard : guardlessIfCleanVars ctxForGuard.varEnv := by
        by_cases hp : pureGuard
        · simp [ctxForGuard, hp, hvars]
        · simp [ctxForGuard, hp, hvars]
      cases hguard : typecheckExpr ctxForGuard e₁ fuelInner with
      | error err =>
          have hcontr := hfix
          simp [runWhileFixpoint] at hcontr
          simp [bind, Except.bind, pure, Except.pure] at hcontr
          simp [hctxForGuard] at hguard
          simp [hguard] at hcontr
      | ok guardRes =>
          cases guardRes with
          | mk qtGuard memGuard tagGuard nextLocGuard nextTagGuard =>
              cases qtGuard with
              | mk etypGuard poisonGuard predGuard =>
                  cases hcheckGuard : etypGuard != ETyp.bool with
                  | true =>
                      have hcontr := hfix
                      simp [runWhileFixpoint] at hcontr
                      simp [bind, Except.bind, pure, Except.pure] at hcontr
                      simp [hctxForGuard] at hguard
                      simp [hguard] at hcontr
                      simp [bne_iff_ne, ne_eq] at hcheckGuard
                      simp [hcheckGuard] at hcontr
                  | false =>
                      have hguard_result :
                          guardlessIfCleanMem memGuard ∧
                            guardlessIfCleanQTypDeep ⟨etypGuard, poisonGuard, predGuard⟩ :=
                        IH (fuel' := fuelInner) hfuel_inner_lt (ctx := ctxForGuard)
                          (e' := e₁)
                          (res' :=
                            { qualType := ⟨etypGuard, poisonGuard, predGuard⟩,
                              memEnv' := memGuard, tagEnv' := tagGuard,
                              nextLoc' := nextLocGuard, nextTag' := nextTagGuard })
                          hmem_ctxForGuard
                          hvars_ctxForGuard
                          (by simpa [typecheck] using hguard)
                      have hguard_mem : guardlessIfCleanMem memGuard :=
                        hguard_result.left
                      set bodyPcCtx : TypeContext :=
                        { ctx with pc := joinPoison ctx.pc poisonGuard } with hbodyPcCtx
                      set bodyTagEnv : TagEnv :=
                        if pureGuard then ctx.tagEnv else tagGuard with hbodyTagEnv
                      set bodyEnvCtx : TypeContext :=
                        { bodyPcCtx with memEnv := memGuard, tagEnv := bodyTagEnv } with hbodyEnvCtx
                      set bodyCtxBase : TypeContext :=
                        { bodyEnvCtx with
                            nextLoc := nextLocGuard,
                            nextTag := nextTagGuard,
                            pureCtx := ctx.pureCtx } with hbodyCtxBase
                      set bodyCtx : TypeContext :=
                        match guardOpt with
                        | some (k, deps) =>
                            { bodyCtxBase with
                                tagEnv := bodyCtxBase.tagEnv.insert k (TagVal.mk true deps) }
                        | none => bodyCtxBase with hbodyCtx
                      have hbody_mem_eq : bodyCtx.memEnv = memGuard := by
                        cases guardOpt with
                        | none => simp [bodyCtx, bodyCtxBase, bodyEnvCtx]
                        | some pair => simp [bodyCtx, bodyCtxBase, bodyEnvCtx]
                      have hbody_var_eq : bodyCtx.varEnv = ctx.varEnv := by
                        cases guardOpt with
                        | none => simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx]
                        | some pair => simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx]
                      have hmem_bodyCtx : guardlessIfCleanMem bodyCtx.memEnv := by
                        simpa [hbody_mem_eq] using hguard_mem
                      have hvars_bodyCtx : guardlessIfCleanVars bodyCtx.varEnv := by
                        simpa [hbody_var_eq] using hvars
                      cases hbody : typecheckExpr bodyCtx e₂ fuelInner with
                      | error err =>
                          have hcontr := hfix
                          simp [runWhileFixpoint] at hcontr
                          simp [bind, pure, Except.bind, Except.pure] at hcontr
                          simp [hctxForGuard] at hguard
                          simp  [bne_eq_false_iff_eq] at hcheckGuard
                          simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx, bodyTagEnv] at hbody
                          simp [hguard, hcheckGuard] at hcontr
                          cases guardOpt <;> dsimp at hcontr <;> dsimp at hbody <;> simp [hbody] at hcontr
                      | ok bodyRes =>
                          cases bodyRes with
                          | mk qtBody memBody tagBody nextLocBody nextTagBody =>
                              cases qtBody with
                              | mk etypBody poisonBody predBody =>
                                  cases hcheckBody : etypBody != ETyp.unit with
                                  | true =>
                                      have hcontr := hfix
                                      simp [runWhileFixpoint] at hcontr
                                      simp [bind, pure, Except.bind, Except.pure] at hcontr
                                      simp [hctxForGuard] at hguard
                                      simp  [bne_eq_false_iff_eq] at hcheckGuard
                                      simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx, bodyTagEnv] at hbody
                                      simp [hguard, hcheckGuard] at hcontr
                                      cases guardOpt <;> dsimp at hbody <;> dsimp at hcontr
                                      · simp [hbody] at hcontr
                                        simp [bne_iff_ne, ne_eq] at hcheckBody
                                        simp [hcheckBody] at hcontr
                                      · simp [hbody] at hcontr
                                        simp [bne_iff_ne, ne_eq] at hcheckBody
                                        simp [hcheckBody] at hcontr
                                  | false =>
                                      have hbody_result :
                                          guardlessIfCleanMem memBody ∧
                                            guardlessIfCleanQTypDeep
                                              ⟨etypBody, poisonBody, predBody⟩ :=
                                        IH (fuel' := fuelInner) hfuel_inner_lt (ctx := bodyCtx)
                                          (e' := e₂)
                                          (res' :=
                                            { qualType := ⟨etypBody, poisonBody, predBody⟩,
                                              memEnv' := memBody, tagEnv' := tagBody,
                                              nextLoc' := nextLocBody, nextTag' := nextTagBody })
                                          hmem_bodyCtx
                                          hvars_bodyCtx
                                          (by simpa [typecheck] using hbody)
                                      have hbody_mem : guardlessIfCleanMem memBody :=
                                        hbody_result.left
                                      let newPc := joinPoison ctx.pc poisonBody
                                      let newMemEnv := joinMemEnvs ctx.memEnv memBody
                                      have hnew_mem : guardlessIfCleanMem newMemEnv :=
                                        guardlessIfCleanMem_joinMemEnvs hmem hbody_mem
                                      let newTagEnv := joinTagEnvs ctx.tagEnv tagBody
                                      cases hfixpoint :
                                        (newMemEnv == ctx.memEnv &&
                                         newPc == ctx.pc &&
                                         newTagEnv == ctx.tagEnv) with
                                      | true =>
                                          have hfix_eq := hfix
                                          simp [runWhileFixpoint] at hfix_eq
                                          simp [bind, pure, Except.bind, Except.pure] at hfix_eq
                                          simp [hctxForGuard] at hguard
                                          simp  [bne_eq_false_iff_eq] at hcheckGuard
                                          simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx, bodyTagEnv] at hbody
                                          simp [hguard, hcheckGuard] at hfix_eq
                                          cases guardOpt <;> dsimp at hbody <;> dsimp at hfix_eq
                                          · simp [hbody] at hfix_eq
                                            simp [bne_eq_false_iff_eq] at hcheckBody
                                            simp [hcheckBody] at hfix_eq
                                            simp [Bool.and_eq_true, beq_iff_eq] at hfixpoint
                                            simp [newMemEnv, newPc, newTagEnv] at hfixpoint
                                            simp [hfixpoint] at hfix_eq
                                            simp [newMemEnv] at hnew_mem
                                            rcases hfix_eq with ⟨hfix_eq_pc, hfix_eq_menv, hfix_eq_tenv, hfix_eq_loc, hfix_eq_tag⟩
                                            rw [← hfix_eq_menv]
                                            exact hnew_mem
                                          · simp [hbody] at hfix_eq
                                            simp [bne_eq_false_iff_eq] at hcheckBody
                                            simp [hcheckBody] at hfix_eq
                                            simp [Bool.and_eq_true, beq_iff_eq] at hfixpoint
                                            simp [newMemEnv, newPc, newTagEnv] at hfixpoint
                                            simp [hfixpoint] at hfix_eq
                                            simp [newMemEnv] at hnew_mem
                                            rcases hfix_eq with ⟨hfix_eq_pc, hfix_eq_menv, hfix_eq_tenv, hfix_eq_loc, hfix_eq_tag⟩
                                            rw [← hfix_eq_menv]
                                            exact hnew_mem
                                      | false =>
                                          set nextCtx : TypeContext :=
                                            { ctx with
                                                pc := newPc,
                                                memEnv := newMemEnv,
                                                tagEnv := newTagEnv,
                                                nextLoc := nextLocBody,
                                                nextTag := nextTagBody } with hnextCtx
                                          have hfix_rec :
                                              runWhileFixpoint nextCtx e₁ e₂ fuelInner pureGuard guardOpt =
                                                .ok
                                                  (pcFinal, memFinal, tagFinal, nextLocFinal,
                                                    nextTagFinal) := by
                                            have hfix_rec' := hfix
                                            simp [runWhileFixpoint] at hfix_rec'
                                            simp [bind, pure, Except.bind, Except.pure] at hfix_rec'
                                            simp [hctxForGuard] at hguard
                                            simp  [bne_eq_false_iff_eq] at hcheckGuard
                                            simp [bodyCtx, bodyCtxBase, bodyEnvCtx, bodyPcCtx, bodyTagEnv] at hbody
                                            simp [hguard, hcheckGuard] at hfix_rec'
                                            cases guardOpt <;> dsimp at hbody <;> dsimp at hfix_rec'
                                            · simp [hbody] at hfix_rec'
                                              simp [bne_eq_false_iff_eq] at hcheckBody
                                              simp [hcheckBody] at hfix_rec'
                                              simp only [Bool.and_eq_false_iff] at hfixpoint
                                              simp [newMemEnv, newPc, newTagEnv] at hfixpoint
                                              simp [nextCtx]
                                              rcases hfixpoint with (hf | hf) | hf <;> simp [hf] at hfix_rec' <;> exact hfix_rec'
                                            · simp [hbody] at hfix_rec'
                                              simp [bne_eq_false_iff_eq] at hcheckBody
                                              simp [hcheckBody] at hfix_rec'
                                              simp only [Bool.and_eq_false_iff] at hfixpoint
                                              simp [newMemEnv, newPc, newTagEnv] at hfixpoint
                                              simp [nextCtx]
                                              rcases hfixpoint with (hf | hf) | hf <;> simp [hf] at hfix_rec' <;> exact hfix_rec'
                                          have hmem_next : guardlessIfCleanMem nextCtx.memEnv := by
                                            simpa [nextCtx, hnextCtx] using hnew_mem
                                          have hvars_next : guardlessIfCleanVars nextCtx.varEnv := by
                                            simpa [nextCtx, hnextCtx] using hvars
                                          exact ih hmem_next hvars_next hfuel_inner_lt hfix_rec

end GuardlessIfCleanLemmas

section GuardlessIfCleanInvariant

private lemma guardlessIfClean_invariant_unit
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (htc : typecheck ctx Expr.unit fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuel =>
      simp [typecheck, typecheckExpr, typecheckUnit] at htc
      cases htc
      constructor
      · exact hmem
      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
        · intro hpoison
          simp [qtypGuardTag]
        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_num
    (n : Int)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (htc : typecheck ctx (Expr.num n) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuel =>
      simp [typecheck, typecheckExpr, typecheckInt] at htc
      cases htc
      constructor
      · exact hmem
      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
        · intro hpoison
          simp [qtypGuardTag]
        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_bool
    (b : Bool)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (htc : typecheck ctx (Expr.bool b) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuel =>
      simp [typecheck, typecheckExpr, typecheckBool] at htc
      cases htc
      constructor
      · exact hmem
      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
        · intro hpoison
          simp [qtypGuardTag]
        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_str
    (s : String)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (htc : typecheck ctx (Expr.str s) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuel =>
      simp [typecheck, typecheckExpr, typecheckString] at htc
      cases htc
      constructor
      · exact hmem
      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
        · intro hpoison
          simp [qtypGuardTag]
        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_var
    (x : Name)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.var x) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuel =>
      simp [typecheck, typecheckExpr] at htc
      cases hlookup : ctx.varEnv.lookup x with
      | none =>
          have htc' := htc
          simp [typecheckVar, hlookup] at htc'
      | some qt =>
          have hqt := guardlessIfCleanVars.lookup hvars hlookup
          cases qt with
          | mk etyp poison pred =>
              have hqt_guard := guardlessIfCleanQTypDeep.guardless hqt
              have hqt_closure := guardlessIfCleanQTypDeep.closure hqt
              cases pred with
              | noPred =>
                  have htc' := htc
                  simp [typecheckVar, hlookup] at htc'
                  cases htc'
                  constructor
                  · exact hmem
                  ·
                    refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                    · intro _hclean
                      simp [qtypGuardTag]
                    ·
                      exact
                        guardlessIfCleanClosureEnv.congr
                          (qt₁ := ⟨etyp, poison, Predicate.noPred⟩)
                          (qt₂ :=
                            ⟨etyp, joinPoison ctx.pc poison, Predicate.noPred⟩)
                          rfl
                          hqt_closure
              | guardClosure k arg body varEnv' =>
                  cases htag : ctx.tagEnv.get? k with
                  | none =>
                      have htag' : ctx.tagEnv[k]? = none := by
                        simpa using htag
                      have htc' := htc
                      simp [typecheckVar, hlookup, htag'] at htc'
                      cases htc'
                      constructor
                      · exact hmem
                      ·
                        refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                        · intro hpoison_clean
                          have hpoison_false : poison = false := by
                            have : ctx.pc = false ∧ poison = false := by
                              simpa [joinPoison] using hpoison_clean
                            exact this.2
                          have : False := by
                            have := hqt_guard hpoison_false
                            simp [qtypGuardTag] at this
                          exact False.elim this
                        ·
                          exact
                            guardlessIfCleanClosureEnv.congr
                              (qt₁ :=
                                ⟨etyp, poison,
                                  Predicate.guardClosure k arg body varEnv'⟩)
                              (qt₂ :=
                                ⟨etyp, joinPoison ctx.pc poison,
                                  Predicate.guardClosure k arg body varEnv'⟩)
                              rfl
                              hqt_closure
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          cases b with
                          | false =>
                              have htag' : ctx.tagEnv[k]? = some { value := false, deps := deps } := by
                                simpa using htag
                              have htc' := htc
                              simp [typecheckVar, hlookup, htag'] at htc'
                              cases htc'
                              constructor
                              · exact hmem
                              ·
                                refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                · intro hpoison_clean
                                  simp at hpoison_clean
                                ·
                                  exact
                                    guardlessIfCleanClosureEnv.congr
                                      (qt₁ :=
                                        ⟨etyp, poison,
                                          Predicate.guardClosure k arg body
                                            varEnv'⟩)
                                      (qt₂ :=
                                        ⟨etyp, true, Predicate.noPred⟩)
                                      rfl
                                      hqt_closure
                          | true =>
                              have htag' : ctx.tagEnv[k]? = some { value := true, deps := deps } := by
                                simpa using htag
                              have htc' := htc
                              simp [typecheckVar, hlookup, htag'] at htc'
                              cases htc'
                              constructor
                              · exact hmem
                              ·
                                refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                · intro _hclean
                                  simp [qtypGuardTag]
                                ·
                                  exact
                                    guardlessIfCleanClosureEnv.congr
                                      (qt₁ :=
                                        ⟨etyp, poison,
                                          Predicate.guardClosure k arg body
                                            varEnv'⟩)
                                      (qt₂ :=
                                        ⟨etyp, ctx.pc, Predicate.noPred⟩)
                                      rfl
                                      hqt_closure
              | guardOnly k =>
                  cases htag : ctx.tagEnv.get? k with
                  | none =>
                      have htag' : ctx.tagEnv[k]? = none := by
                        simpa using htag
                      have htc' := htc
                      simp [typecheckVar, hlookup, htag'] at htc'
                      cases htc'
                      constructor
                      · exact hmem
                      ·
                        refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                        · intro hpoison_clean
                          have hpoison_false : poison = false := by
                            have : ctx.pc = false ∧ poison = false := by
                              simpa [joinPoison] using hpoison_clean
                            exact this.2
                          have : False := by
                            have := hqt_guard hpoison_false
                            simp [qtypGuardTag] at this
                          exact False.elim this
                        ·
                          exact
                            guardlessIfCleanClosureEnv.congr
                              (qt₁ := ⟨etyp, poison, Predicate.guardOnly k⟩)
                              (qt₂ :=
                                ⟨etyp, joinPoison ctx.pc poison,
                                  Predicate.guardOnly k⟩)
                              rfl
                              hqt_closure
                  | some tv =>
                      cases tv with
                      | mk b deps =>
                          cases b with
                          | false =>
                              have htag' : ctx.tagEnv[k]? = some { value := false, deps := deps } := by
                                simpa using htag
                              have htc' := htc
                              simp [typecheckVar, hlookup, htag'] at htc'
                              cases htc'
                              constructor
                              · exact hmem
                              ·
                                refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                · intro hpoison_clean
                                  simp at hpoison_clean
                                ·
                                  exact
                                    guardlessIfCleanClosureEnv.congr
                                      (qt₁ :=
                                        ⟨etyp, poison, Predicate.guardOnly k⟩)
                                      (qt₂ :=
                                        ⟨etyp, true, Predicate.noPred⟩)
                                      rfl
                                      hqt_closure
                          | true =>
                              have htag' : ctx.tagEnv[k]? = some { value := true, deps := deps } := by
                                simpa using htag
                              have htc' := htc
                              simp [typecheckVar, hlookup, htag'] at htc'
                              cases htc'
                              constructor
                              · exact hmem
                              ·
                                refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                · intro _hclean
                                  simp [qtypGuardTag]
                                ·
                                  exact
                                    guardlessIfCleanClosureEnv.congr
                                      (qt₁ :=
                                        ⟨etyp, poison, Predicate.guardOnly k⟩)
                                      (qt₂ :=
                                        ⟨etyp, ctx.pc, Predicate.noPred⟩)
                                      rfl
                                      hqt_closure

private lemma guardlessIfClean_invariant_op
    (e₁ e₂ : Expr) (op : Op)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄  ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.op e₁ op e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcOp : typecheckOp ctx e₁ e₂ fuelPred op = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckOp] at htcOp
      | succ fuelInner =>
          cases hres₁ : typecheckExpr ctx e₁ fuelInner with
          | error err =>
              have hcontr := htcOp
              simp [typecheckOp, hres₁] at hcontr
              cases hcontr
          | ok result₁ =>
              cases result₁ with
              | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                  cases qt₁ with
                  | mk etyp₁ poison₁ pred₁ =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hguard₁_both :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e₁)
                          (res' :=
                            { qualType := ⟨etyp₁, poison₁, pred₁⟩, memEnv' := memEnv₁,
                              tagEnv' := tagEnv₁, nextLoc' := nextLoc₁,
                              nextTag' := nextTag₁ })
                          hmem hvars
                          (by simpa [typecheck] using hres₁)
                      have hguard₁ : guardlessIfCleanMem memEnv₁ := hguard₁_both.left
                      let ctx' : TypeContext :=
                        { ctx with
                          memEnv := memEnv₁,
                          tagEnv := tagEnv₁,
                          nextLoc := nextLoc₁,
                          nextTag := nextTag₁ }
                      cases hres₂ :
                          typecheckExpr ctx' e₂ fuelInner with
                      | error err =>
                          have hcontr := htcOp
                          simp [typecheckOp, hres₁] at hcontr
                          simp [bind, pure, Except.bind, Except.pure] at hcontr
                          simp [ctx'] at hres₂
                          rw [hres₂] at hcontr
                          dsimp at hcontr
                          cases hcontr
                      | ok result₂ =>
                          cases result₂ with
                          | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                            have hguardCtx' : guardlessIfCleanMem ctx'.memEnv := by
                              simpa [ctx'] using hguard₁
                            have hvarsCtx' : guardlessIfCleanVars ctx'.varEnv := by
                              simpa [ctx'] using hvars
                            have hguard₂_both :=
                              IH (fuel' := fuelInner) hfuel (ctx := ctx')
                                (e' := e₂)
                                (res' :=
                                  { qualType := qt₂, memEnv' := memEnv₂,
                                    tagEnv' := tagEnv₂, nextLoc' := nextLoc₂,
                                    nextTag' := nextTag₂ })
                                hguardCtx'
                                hvarsCtx'
                                (by simpa [typecheck] using hres₂)
                            have hguard₂ : guardlessIfCleanMem memEnv₂ := hguard₂_both.left
                            cases qt₂ with
                            | mk etyp₂ poison₂ pred₂ =>
                                cases hop : opEType? op etyp₁ etyp₂ with
                                | none =>
                                    have hcontr := htcOp
                                    simp [typecheckOp, hres₁, ctx', hres₂, hop,
                                      bind, Except.bind] at hcontr
                                | some r =>
                                    have hres_eq :
                                        Except.ok
                                            { qualType :=
                                                { etyp := r,
                                                  poison :=
                                                    joinPoison ctx.pc
                                                      (joinPoison poison₁ poison₂),
                                                  pred := Predicate.noPred },
                                              memEnv' := memEnv₂,
                                              tagEnv' := tagEnv₂,
                                              nextLoc' := nextLoc₂,
                                              nextTag' := nextTag₂ } =
                                          @Except.ok String TypeResult res := by
                                      rw [← htcOp]
                                      unfold typecheckOp
                                      simp [bind, Except.bind, pure, Except.pure,
                                        hres₁, ctx', hres₂, hop]
                                    cases hres_eq
                                    dsimp
                                    have hopOp :
                                        OpEType op etyp₁ etyp₂ r :=
                                      (opEType?_iff op etyp₁ etyp₂ r).1 hop
                                    have hnonClosure :
                                        nonClosureQTyp
                                          { etyp := r,
                                            poison :=
                                              joinPoison ctx.pc
                                                (joinPoison poison₁ poison₂),
                                            pred := Predicate.noPred } := by
                                      cases hopOp <;> simp [nonClosureQTyp]
                                    constructor
                                    · exact hguard₂
                                    · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ hnonClosure
                                      · intro hpoison_clean
                                        simp [qtypGuardTag]

private lemma guardlessIfClean_invariant_unaryop
    (op : UnaryOp) (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.unaryop op e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcUnary : typecheckUnaryOp ctx op e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckUnaryOp] at htcUnary
      | succ fuelInner =>
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcUnary
              simp [typecheckUnaryOp, hres] at hcontr
              cases hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) :=
                    Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                  have hguard_both :=
                    IH (fuel' := fuelInner) hfuel (e' := e)
                      (res' := { qualType := qt, memEnv' := memEnv',
                                  tagEnv' := tagEnv', nextLoc' := nextLoc',
                                  nextTag' := nextTag' })
                      hmem hvars
                      (by simpa [typecheck] using hres)
                  have hguard : guardlessIfCleanMem memEnv' := hguard_both.left
                  cases qt with
                  | mk etyp poison pred =>
                      cases hop : opUnaryEType? op etyp with
                      | none =>
                          have hcontr :
                              Except.error
                                  (s!"Operation argument types do not match.\n  Expression Type: {etyp}\n  UnaryOp: {op}") =
                                Except.ok res := by
                            rw [← htcUnary]
                            unfold typecheckUnaryOp
                            simp [bind, Except.bind]
                            rw [hres]
                            dsimp
                            rw [hop]
                            dsimp
                            rfl
                          cases hcontr
                      | some r =>
                          have hres_eq :
                        Except.ok { qualType :=
                                      { etyp := r, poison := joinPoison ctx.pc poison,
                                        pred := Predicate.noPred },
                                    memEnv' := memEnv',
                                    tagEnv' := tagEnv',
                                    nextLoc' := nextLoc',
                                    nextTag' := nextTag' } =
                                  @Except.ok String TypeResult res := by
                            rw [← htcUnary]
                            unfold typecheckUnaryOp
                            simp [bind, Except.bind, pure, Except.pure]
                            rw [hres]
                            dsimp
                            rw [hop]
                          cases hres_eq
                          dsimp
                          have hr : r = ETyp.bool := by
                            revert hop
                            cases op with
                            | not =>
                                cases etyp <;> intro hop <;> cases hop
                                rfl
                          have hnonClosure :
                              nonClosureQTyp
                                { etyp := r,
                                  poison := joinPoison ctx.pc poison,
                                  pred := Predicate.noPred } := by
                            subst hr
                            simp [nonClosureQTyp]
                          constructor
                          · exact hguard
                          · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ hnonClosure
                            · intro hpoison_clean
                              simp [qtypGuardTag]

private lemma guardlessIfClean_invariant_ite
    (e₁ e₂ e₃ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.ite e₁ e₂ e₃) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcIf : typecheckIf ctx e₁ e₂ e₃ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases hguard : matchGuard e₁ ctx.memEnv ctx.varEnv with
      | error err =>
        unfold typecheckIf at htcIf
        cases fuelPred with
        | zero =>
            cases htcIf
        | succ fuelInner =>
            dsimp at htcIf
            rw [hguard] at htcIf
            dsimp at htcIf
            simp [bind, pure, Except.bind, Except.pure] at htcIf
            have hfuel :
                fuelInner < Nat.succ (Nat.succ fuelInner) :=
              Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
            cases hres₁ : typecheckExpr ctx e₁ fuelInner with
            | error err₁ =>
                have : False := by
                  have hcontr := htcIf
                  simp [hres₁] at hcontr
                exact this.elim
            | ok result₁ =>
                cases result₁ with
                | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                    cases qt₁ with
                    | mk etyp₁ poison₁ pred₁ =>
                        have hbool_bne : (etyp₁ != ETyp.bool) = false := by
                          classical
                          have hcontr := htcIf
                          revert hcontr
                          generalize hboolCheck :
                              (etyp₁ != ETyp.bool) = b
                          intro hcontr
                          cases b with
                          | false => rfl
                          | true =>
                              simp [hres₁] at hcontr
                              have heq : etyp₁ ≠ ETyp.bool := by
                                intro h
                                subst h
                                simp [bne] at hboolCheck
                              rw [if_neg heq] at hcontr
                              cases hcontr
                        have hbool : etyp₁ = ETyp.bool := by
                          rw [← bne_eq_false_iff_eq]
                          exact hbool_bne
                        let ctx' : TypeContext :=
                          { ctx with
                            memEnv := memEnv₁,
                            tagEnv := tagEnv₁,
                            nextLoc := nextLoc₁,
                            nextTag := nextTag₁ }
                        let ctx'' : TypeContext :=
                          { ctx' with
                            pc := joinPoison ctx.pc poison₁ }
                        have hguard₁ :
                            guardlessIfCleanMem memEnv₁ := by
                          have ⟨h1, h2⟩ :=
                            IH
                              (fuel' := fuelInner) hfuel
                              (ctx := ctx) (e' := e₁)
                              (res' :=
                                { qualType := ⟨etyp₁, poison₁, pred₁⟩,
                                  memEnv' := memEnv₁,
                                  tagEnv' := tagEnv₁,
                                  nextLoc' := nextLoc₁,
                                  nextTag' := nextTag₁ })
                              hmem hvars
                              hres₁
                          dsimp at h1
                          apply h1
                        have hmem_ctx'' : guardlessIfCleanMem ctx''.memEnv := by
                          simpa [ctx''] using hguard₁
                        have hvars_ctx'' : guardlessIfCleanVars ctx''.varEnv := by
                          simpa [ctx'', ctx'] using hvars
                        cases hres₂ : typecheckExpr ctx'' e₂ fuelInner with
                        | error err₂ =>
                            have : False := by
                              have hcontr := htcIf
                              simp [hres₁, ctx', ctx'', hres₂] at hcontr
                              rw [if_pos hbool] at hcontr
                              cases hcontr
                            exact this.elim
                        | ok result₂ =>
                            cases result₂ with
                            | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                                cases qt₂ with
                                | mk etyp₂ poison₂ pred₂ =>
                                    let ctxForE3 : TypeContext :=
                                      { ctx'' with
                                        nextLoc := nextLoc₂,
                                        nextTag := nextTag₂ }
                                    have hmem_ctxForE3 :
                                        guardlessIfCleanMem ctxForE3.memEnv := by
                                      simpa [ctxForE3, ctx''] using hguard₁
                                    have hvars_ctxForE3 :
                                        guardlessIfCleanVars ctxForE3.varEnv := by
                                      simpa [ctxForE3, ctx'', ctx'] using hvars
                                    cases hres₃ :
                                        typecheckExpr ctxForE3 e₃ fuelInner with
                                    | error err₃ =>
                                        have : False := by
                                          have hcontr := htcIf
                                          simp [hres₁, ctx', ctx'', hres₂, ctxForE3, hres₃] at hcontr
                                          rw [if_pos hbool] at hcontr
                                          cases hcontr
                                        exact this.elim
                                    | ok result₃ =>
                                        cases result₃ with
                                            | mk qt₃ memEnv₃ tagEnv₃ nextLoc₃ nextTag₃ =>
                                                cases qt₃ with
                                                | mk etyp₃ poison₃ pred₃ =>
                                                    classical
                                                    have hbeq :
                                                        beqETypSignature etyp₂ etyp₃ = true := by
                                                      cases hbeq_case : beqETypSignature etyp₂ etyp₃ with
                                                      | false =>
                                                          have hcontr := htcIf
                                                          simp [hres₁, ctx', ctx'', hres₂, ctxForE3, hres₃, hbeq_case] at hcontr
                                                          rw [if_pos hbool] at hcontr
                                                          cases hcontr
                                                      | true => rfl
                                                    obtain ⟨hguard₂, hqt₂⟩ :=
                                                      IH
                                                        (fuel' := fuelInner) hfuel
                                                        (ctx := ctx'') (e' := e₂)
                                                        (res' :=
                                                          { qualType := ⟨etyp₂, poison₂, pred₂⟩,
                                                            memEnv' := memEnv₂,
                                                            tagEnv' := tagEnv₂,
                                                            nextLoc' := nextLoc₂,
                                                            nextTag' := nextTag₂ })
                                                        hmem_ctx'' hvars_ctx''
                                                        hres₂
                                                    obtain ⟨hguard₃, hqt₃⟩ :=
                                                      IH
                                                        (fuel' := fuelInner) hfuel
                                                        (ctx := ctxForE3) (e' := e₃)
                                                        (res' :=
                                                          { qualType := ⟨etyp₃, poison₃, pred₃⟩,
                                                            memEnv' := memEnv₃,
                                                            tagEnv' := tagEnv₃,
                                                            nextLoc' := nextLoc₃,
                                                            nextTag' := nextTag₃ })
                                                        hmem_ctxForE3 hvars_ctxForE3
                                                        hres₃
                                                    dsimp at hguard₂ hqt₂ hguard₃ hqt₃
                                                    have hres_eq₀ :
                                                        Except.ok
                                                            { qualType :=
                                                                { etyp := etyp₂,
                                                                  poison :=
                                                                    joinPoison ctx.pc
                                                                      (joinPoison poison₁
                                                                        (joinPoison poison₂ poison₃)),
                                                                  pred := Predicate.noPred },
                                                              memEnv' :=
                                                                joinMemEnvs memEnv₂ memEnv₃,
                                                              tagEnv' := tagEnv₁,
                                                              nextLoc' := max nextLoc₂ nextLoc₃,
                                                              nextTag' := max nextTag₂ nextTag₃ } =
                                                      @Except.ok String TypeResult res := by
                                                      rw [← htcIf]
                                                      simp [hres₁, ctx', ctx'', hres₂, ctxForE3, hres₃]
                                                      rw [if_pos hbool]
                                                      rw [hbeq]
                                                      simp
                                                    have hres_eq :
                                                        res =
                                                          { qualType :=
                                                              { etyp := etyp₂,
                                                                poison :=
                                                                  joinPoison ctx.pc
                                                                    (joinPoison poison₁
                                                                      (joinPoison poison₂ poison₃)),
                                                                pred := Predicate.noPred },
                                                            memEnv' :=
                                                              joinMemEnvs memEnv₂ memEnv₃,
                                                            tagEnv' := tagEnv₁,
                                                            nextLoc' := max nextLoc₂ nextLoc₃,
                                                            nextTag' := max nextTag₂ nextTag₃ } := by
                                                      have h := hres_eq₀
                                                      cases h
                                                      rfl
                                                    subst hres_eq
                                                    dsimp
                                                    constructor
                                                    · exact guardlessIfCleanMem_joinMemEnvs hguard₂ hguard₃
                                                    ·
                                                      refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                                      · intro _hpoison_clean
                                                        simp [qtypGuardTag]
                                                      ·
                                                        have hclosure₂ :=
                                                          guardlessIfCleanQTypDeep.closure hqt₂
                                                        exact
                                                          guardlessIfCleanClosureEnv.congr
                                                            (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                                            (qt₂ :=
                                                              ⟨etyp₂,
                                                                joinPoison ctx.pc
                                                                  (joinPoison poison₁
                                                                    (joinPoison poison₂ poison₃)),
                                                                Predicate.noPred⟩)
                                                            rfl
                                                            hclosure₂
      | ok guardInfo =>
          cases guardInfo with
          | mk k deps =>
              cases fuelPred with
              | zero =>
                  simp [typecheckIf] at htcIf
              | succ fuelInner =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) :=
                    Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                  let pureCtx : TypeContext := { ctx with pureCtx := true }
                  cases hres₁ :
                      typecheckExpr pureCtx e₁ fuelInner with
                  | error err =>
                      have hcontr := htcIf
                      simp [typecheckIf, hguard] at hcontr
                      simp [bind, pure, Except.bind, Except.pure] at hcontr
                      rw [hres₁] at hcontr
                      dsimp at hcontr
                      cases hcontr
                  | ok result₁ =>
                      cases result₁ with
                      | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                          cases qt₁ with
                          | mk etyp₁ poison₁ pred₁ =>
                              have hbool_bne : (etyp₁ != ETyp.bool) = false := by
                                classical
                                have hcontr := htcIf
                                revert hcontr
                                generalize hboolCheck :
                                    (etyp₁ != ETyp.bool) = b
                                intro hcontr
                                cases b with
                                | false => rfl
                                | true =>
                                    simp [typecheckIf, hguard] at hcontr
                                    simp [bind, pure, Except.bind, Except.pure] at hcontr
                                    simp [pureCtx] at hres₁
                                    simp [hres₁] at hcontr
                                    have heq : etyp₁ ≠ ETyp.bool := by
                                      intro h
                                      subst h
                                      simp [bne] at hboolCheck
                                    rw [if_neg heq] at hcontr
                                    cases hcontr
                              have hbool : etyp₁ = ETyp.bool := by
                                rw [← bne_eq_false_iff_eq]
                                exact hbool_bne
                              let ctxTrue :
                                  TypeContext :=
                                { ctx with
                                  tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
                              let ctxFalse :
                                  TypeContext :=
                                { ctx with
                                  tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩ }
                              cases hres₂ :
                                  typecheckExpr ctxTrue e₂ fuelInner with
                              | error err =>
                                  have : False := by
                                    have hcontr := htcIf
                                    simp [typecheckIf, hguard, ctxTrue, hres₂] at hcontr
                                    simp [bind, Except.bind] at hcontr
                                    rw [hres₁] at hcontr
                                    dsimp at hcontr
                                    rw [if_pos hbool] at hcontr
                                    cases hcontr
                                  exact this.elim
                              | ok result₂ =>
                                  cases result₂ with
                                  | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                                      cases qt₂ with
                                      | mk etyp₂ poison₂ pred₂ =>
                                          let ctxFalse' :
                                              TypeContext :=
                                            { ctxFalse with
                                              nextLoc := nextLoc₂,
                                              nextTag := nextTag₂ }
                                          cases hres₃ :
                                              typecheckExpr ctxFalse' e₃ fuelInner with
                                          | error err =>
                                              have : False := by
                                                have hcontr := htcIf
                                                simp [typecheckIf, hguard, ctxTrue, hres₂] at hcontr
                                                simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                rw [hres₁] at hcontr
                                                dsimp at hcontr
                                                rw [if_pos hbool] at hcontr
                                                rw [hres₃] at hcontr
                                                dsimp at hcontr
                                                cases hcontr
                                              exact this.elim
                                          | ok result₃ =>
                                              cases result₃ with
                                              | mk qt₃ memEnv₃ tagEnv₃ nextLoc₃ nextTag₃ =>
                                                  cases qt₃ with
                                                  | mk etyp₃ poison₃ pred₃ =>
                                                      classical
                                                      have hbeq :
                                                          beqETypSignature etyp₂ etyp₃ = true := by
                                                        cases hbeq_case : beqETypSignature etyp₂ etyp₃ with
                                                        | false =>
                                                            have hcontr := htcIf
                                                            simp [typecheckIf, hguard, ctxTrue, hres₂] at hcontr
                                                            simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                            rw [hres₁] at hcontr
                                                            dsimp at hcontr
                                                            rw [if_pos hbool] at hcontr
                                                            rw [hres₃] at hcontr
                                                            dsimp at hcontr
                                                            rw [hbeq_case] at hcontr
                                                            simp [Functor.map, Except.map] at hcontr
                                                        | true => rfl
                                                      have hmem_ctxTrue : guardlessIfCleanMem ctxTrue.memEnv := by
                                                        simpa [ctxTrue] using hmem
                                                      have hvars_ctxTrue : guardlessIfCleanVars ctxTrue.varEnv := by
                                                        simpa [ctxTrue] using hvars
                                                      obtain ⟨hguard₂, hqt₂⟩ := IH
                                                        (fuel' := fuelInner) hfuel
                                                        (ctx := ctxTrue) (e' := e₂)
                                                        (res' :=
                                                          { qualType := ⟨etyp₂, poison₂, pred₂⟩,
                                                            memEnv' := memEnv₂, tagEnv' := tagEnv₂,
                                                            nextLoc' := nextLoc₂, nextTag' := nextTag₂ })
                                                        hmem_ctxTrue hvars_ctxTrue
                                                        hres₂
                                                      have hmem_ctxFalse' : guardlessIfCleanMem ctxFalse'.memEnv := by
                                                        simpa [ctxFalse', ctxFalse] using hmem
                                                      have hvars_ctxFalse' : guardlessIfCleanVars ctxFalse'.varEnv := by
                                                        simpa [ctxFalse', ctxFalse] using hvars
                                                      obtain ⟨hguard₃, hqt₃⟩ := IH
                                                        (fuel' := fuelInner) hfuel
                                                        (ctx := ctxFalse') (e' := e₃)
                                                        (res' :=
                                                          { qualType := ⟨etyp₃, poison₃, pred₃⟩,
                                                            memEnv' := memEnv₃, tagEnv' := tagEnv₃,
                                                            nextLoc' := nextLoc₃, nextTag' := nextTag₃ })
                                                        hmem_ctxFalse' hvars_ctxFalse'
                                                        hres₃
                                                      dsimp at hguard₂ hqt₂ hguard₃ hqt₃
                                                      have hres_eq :
                                                          Except.ok
                                                              { qualType :=
                                                                  { etyp := etyp₂,
                                                                    poison :=
                                                                      joinPoison ctx.pc
                                                                        (joinPoison poison₂ poison₃),
                                                                    pred := Predicate.noPred },
                                                                memEnv' :=
                                                                  joinMemEnvs memEnv₂ memEnv₃,
                                                                tagEnv' := ctx.tagEnv,
                                                                nextLoc' := max nextLoc₂ nextLoc₃,
                                                                nextTag' := max nextTag₂ nextTag₃ } =
                                                            @Except.ok String TypeResult res := by
                                                        rw [← htcIf]
                                                        unfold typecheckIf
                                                        simp [bind, pure, Except.bind, Except.pure, hguard,
                                                          pureCtx, hres₁, ctxTrue, hres₂,
                                                          ctxFalse, ctxFalse', hres₃]
                                                        rw [if_pos hbool]
                                                        rw [hbeq]
                                                        simp
                                                      cases hres_eq
                                                      dsimp
                                                      constructor
                                                      · exact guardlessIfCleanMem_joinMemEnvs hguard₂ hguard₃
                                                      ·
                                                        refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                                        · intro _hpoison_clean
                                                          simp [qtypGuardTag]
                                                        ·
                                                          have hclosure₂ :=
                                                            guardlessIfCleanQTypDeep.closure hqt₂
                                                          exact
                                                            guardlessIfCleanClosureEnv.congr
                                                              (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                                              (qt₂ :=
                                                                ⟨etyp₂,
                                                                  joinPoison ctx.pc
                                                                    (joinPoison poison₂ poison₃),
                                                                  Predicate.noPred⟩)
                                                              rfl
                                                              hclosure₂
private lemma guardlessIfClean_invariant_newRef
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.newRef e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcNewRef : typecheckNewRef ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckNewRef] at htcNewRef
      | succ fuelInner =>
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcNewRef
              simp [typecheckNewRef, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  cases qt with
                  | mk etyp poison pred =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hres_guard :
                          guardlessIfCleanMem memEnv' ∧
                            guardlessIfCleanQTypDeep ⟨etyp, poison, pred⟩ :=
                        IH (fuel' := fuelInner) hfuel (e' := e)
                          (res' := { qualType := ⟨etyp, poison, pred⟩, memEnv' := memEnv',
                                      tagEnv' := tagEnv', nextLoc' := nextLoc',
                                      nextTag' := nextTag' })
                          hmem hvars
                          (by simpa [typecheck] using hres)
                      have hguard : guardlessIfCleanMem memEnv' := hres_guard.left
                      have hqt : guardlessIfCleanQTypDeep ⟨etyp, poison, pred⟩ := hres_guard.right
                      have hguard_qt : guardlessIfCleanQTyp ⟨etyp, poison, pred⟩ :=
                        guardlessIfCleanQTypDeep.guardless hqt
                      have hclosure_qt : guardlessIfCleanClosureEnv ⟨etyp, poison, pred⟩ :=
                        guardlessIfCleanQTypDeep.closure hqt
                      let storedQt : QTyp := ⟨etyp, joinPoison ctx.pc poison, pred⟩
                      have hstored_guard : guardlessIfCleanQTypDeep storedQt := by
                        refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                        · intro hjoin_false
                          have hjoin_false' := hjoin_false
                          simp [storedQt] at hjoin_false'
                          have hpoison_false : poison = false := by
                            cases hpoison : poison with
                            | false => exact rfl
                            | true =>
                                exfalso
                                have hcontr := hjoin_false'
                                simp [joinPoison, hpoison] at hcontr
                          have hpred_guardless :
                              qtypGuardTag ⟨etyp, poison, pred⟩ = none :=
                            hguard_qt hpoison_false
                          simpa [storedQt, qtypGuardTag] using hpred_guardless
                        · exact
                            guardlessIfCleanClosureEnv.congr
                              (qt₁ := ⟨etyp, poison, pred⟩)
                              (qt₂ := storedQt)
                              rfl
                              hclosure_qt
                      have hres_eq :
                          res =
                            { qualType := ⟨ETyp.ref etyp nextLoc', ctx.pc, Predicate.noPred⟩,
                              memEnv' := updateMemEnv memEnv' nextLoc' storedQt,
                              tagEnv' := tagEnv', nextLoc' := nextLoc' + 1,
                              nextTag' := nextTag' } := by
                        unfold typecheckNewRef at htcNewRef
                        simp [bind, Except.bind, pure, Except.pure,
                          hres, freshTLocRes] at htcNewRef
                        cases htcNewRef
                        rfl
                      subst hres_eq
                      dsimp [storedQt]
                      constructor
                      · exact guardlessIfCleanMem.updateMemEnv hguard hstored_guard
                      ·
                        refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                        · intro hpoison_clean
                          simp [qtypGuardTag]
                        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_assign
    (e₁ e₂ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.assign e₁ e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcAssign : typecheckAssign ctx e₁ e₂ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckAssign] at htcAssign
      | succ fuelInner =>
          cases hres₁ : typecheckExpr ctx e₁ fuelInner with
          | error err =>
              have hcontr := htcAssign
              simp [typecheckAssign, hres₁, bind, Except.bind] at hcontr
          | ok result₁ =>
              cases result₁ with
              | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                  cases qt₁ with
                  | mk etyp₁ poison₁ pred₁ =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hguard₁_pair :
                          guardlessIfCleanMem memEnv₁ ∧
                            guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e₁)
                          (res' :=
                            { qualType := ⟨etyp₁, poison₁, pred₁⟩, memEnv' := memEnv₁,
                              tagEnv' := tagEnv₁, nextLoc' := nextLoc₁,
                              nextTag' := nextTag₁ })
                          hmem hvars
                          (by simpa [typecheck] using hres₁)
                      have hguard₁ : guardlessIfCleanMem memEnv₁ := hguard₁_pair.left
                      have ⟨t, l, hetyp⟩ : ∃ t l, etyp₁ = ETyp.ref t l := by
                        unfold typecheckAssign at htcAssign
                        simp [bind, pure, Except.bind, Except.pure] at htcAssign
                        rw [hres₁] at htcAssign
                        dsimp at htcAssign
                        cases etyp₁ <;> try simp at htcAssign
                        simp
                      let ctx' : TypeContext :=
                        { ctx with
                          memEnv := memEnv₁,
                          tagEnv := tagEnv₁,
                          nextLoc := nextLoc₁,
                          nextTag := nextTag₁ }
                      have hmem_ctx' : guardlessIfCleanMem ctx'.memEnv := by
                        simpa [ctx'] using hguard₁
                      have hvars_ctx' : guardlessIfCleanVars ctx'.varEnv := by
                        simpa [ctx'] using hvars
                      cases hres₂ : typecheckExpr ctx' e₂ fuelInner with
                      | error err =>
                          have hcontr := htcAssign
                          simp [typecheckAssign, hres₁, hetyp, ctx', hres₂, bind,
                            Except.bind] at hcontr
                      | ok result₂ =>
                          cases result₂ with
                          | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                              cases qt₂ with
                              | mk etyp₂ poison₂ pred₂ =>
                                  have hguard₂_pair :
                                      guardlessIfCleanMem memEnv₂ ∧
                                        guardlessIfCleanQTypDeep
                                          ⟨etyp₂, poison₂, pred₂⟩ :=
                                    IH (fuel' := fuelInner) hfuel (ctx := ctx') (e' := e₂)
                                      (res' :=
                                        { qualType := ⟨etyp₂, poison₂, pred₂⟩,
                                          memEnv' := memEnv₂, tagEnv' := tagEnv₂,
                                          nextLoc' := nextLoc₂, nextTag' := nextTag₂ })
                                      hmem_ctx' hvars_ctx'
                                      (by simpa [typecheck] using hres₂)
                                  have hguard₂ : guardlessIfCleanMem memEnv₂ :=
                                    hguard₂_pair.left
                                  have hqt₂ :
                                      guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                    hguard₂_pair.right
                                  have hguard_qt₂ :
                                      guardlessIfCleanQTyp ⟨etyp₂, poison₂, pred₂⟩ :=
                                    guardlessIfCleanQTypDeep.guardless hqt₂
                                  have hclosure_qt₂ :
                                      guardlessIfCleanClosureEnv ⟨etyp₂, poison₂, pred₂⟩ :=
                                    guardlessIfCleanQTypDeep.closure hqt₂
                                  cases hcheck : (etyp₂ != t) with
                                  | true =>
                                      have hcontr := htcAssign
                                      simp [typecheckAssign, hres₁, hetyp, ctx', hres₂,
                                        hcheck, bind, Except.bind] at hcontr
                                  | false =>
                                      have het : etyp₂ = t := by
                                        simpa [bne_eq_false_iff_eq] using hcheck
                                      let storedQt : QTyp :=
                                        ⟨t, joinPoison ctx.pc (joinPoison poison₁ poison₂),
                                          pred₂⟩
                                      have hstored_guard :
                                          guardlessIfCleanQTyp storedQt := by
                                        intro hpoison_clean
                                        have hctx_pc_false : ctx.pc = false := by
                                          cases hpc : ctx.pc with
                                          | false => rfl
                                          | true =>
                                              have : False := by
                                                have := hpoison_clean
                                                simp [storedQt, joinPoison, hpc] at this
                                              exact this.elim
                                        have hjoin_inner :
                                            joinPoison poison₁ poison₂ = false := by
                                          simp [storedQt, joinPoison, hctx_pc_false] at hpoison_clean
                                          rw [hpoison_clean.1, hpoison_clean.2]
                                          rfl
                                        have hpoison₁_false : poison₁ = false := by
                                          cases hp₁ : poison₁ with
                                          | false => rfl
                                          | true =>
                                              have : False := by
                                                have := hjoin_inner
                                                simp [joinPoison, hp₁] at this
                                              exact this.elim
                                        have hpoison₂_false : poison₂ = false := by
                                          have := hjoin_inner
                                          simp [joinPoison, hpoison₁_false] at this
                                          simpa using this
                                        have hpred_guardless :
                                            qtypGuardTag ⟨etyp₂, poison₂, pred₂⟩ = none :=
                                          hguard_qt₂ hpoison₂_false
                                        simpa [storedQt, qtypGuardTag] using hpred_guardless
                                      have hstored_closure :
                                          guardlessIfCleanClosureEnv storedQt :=
                                        guardlessIfCleanClosureEnv.congr
                                          (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                          (qt₂ := storedQt)
                                          het
                                          hclosure_qt₂
                                      have hstored_qt :
                                          guardlessIfCleanQTypDeep storedQt :=
                                        guardlessIfCleanQTypDeep.intro storedQt
                                          hstored_guard
                                          hstored_closure
                                      let resultPoison := joinPoison ctx.pc poison₁
                                      have hres_eq :
                                          res =
                                            { qualType :=
                                                ⟨ETyp.unit, resultPoison,
                                                  Predicate.noPred⟩,
                                              memEnv' :=
                                                updateMemEnv memEnv₂ l storedQt,
                                              tagEnv' := invalidateTagDeps tagEnv₂ l,
                                              nextLoc' := nextLoc₂,
                                              nextTag' := nextTag₂ } := by
                                        unfold typecheckAssign at htcAssign
                                        simp [bind, Except.bind, pure, Except.pure, hres₁, hetyp, ctx', hres₂, hcheck] at htcAssign
                                        cases htcAssign
                                        rfl
                                      subst hres_eq
                                      constructor
                                      · exact guardlessIfCleanMem.updateMemEnv hguard₂ hstored_qt
                                      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                                        · intro _
                                          simp [qtypGuardTag]
                                        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_deref
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.deref e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcDeref : typecheckDeref ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckDeref] at htcDeref
      | succ fuelInner =>
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcDeref
              simp [typecheckDeref, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  cases qt with
                  | mk etyp poison pred =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hguard_pair :
                          guardlessIfCleanMem memEnv' ∧
                            guardlessIfCleanQTypDeep ⟨etyp, poison, pred⟩ :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e)
                          (res' :=
                            { qualType := ⟨etyp, poison, pred⟩, memEnv' := memEnv',
                              tagEnv' := tagEnv', nextLoc' := nextLoc',
                              nextTag' := nextTag' })
                          hmem hvars
                          (by simpa [typecheck] using hres)
                      have hguard_mem_res : guardlessIfCleanMem memEnv' :=
                        hguard_pair.left
                      have hguard_qt_res :
                          guardlessIfCleanQTypDeep ⟨etyp, poison, pred⟩ :=
                        hguard_pair.right
                      have hguard_qt :
                          guardlessIfCleanQTyp ⟨etyp, poison, pred⟩ :=
                        guardlessIfCleanQTypDeep.guardless hguard_qt_res
                      have hguard_closure :
                          guardlessIfCleanClosureEnv ⟨etyp, poison, pred⟩ :=
                        guardlessIfCleanQTypDeep.closure hguard_qt_res
                      cases etyp with
                      | int =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | bool =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | unit =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | string =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | arrow st₁ st₂ pc cl =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | parrow st₁ st₂ pc cl =>
                          have hcontr := htcDeref
                          unfold typecheckDeref at hcontr
                          simp [bind, Except.bind, hres] at hcontr
                      | ref t l =>
                          cases hlookup : memEnv'[l]? with
                          | none =>
                              have hcontr := htcDeref
                              unfold typecheckDeref at hcontr
                              simp [bind, Except.bind, hres, hlookup] at hcontr
                          | some storedQt =>
                              cases storedQt with
                              | mk storedEtyp storedPoison storedPred =>
                                  cases hcheck : (storedEtyp != t) with
                                  | true =>
                                      have hcontr := htcDeref
                                      unfold typecheckDeref at hcontr
                                      simp [bind, Except.bind, hres, hlookup, hcheck] at hcontr
                                  | false =>
                                      have het :
                                          storedEtyp = t := by
                                            simpa [bne_eq_false_iff_eq] using hcheck
                                      have hstored_qt :
                                          guardlessIfCleanQTypDeep
                                            ⟨storedEtyp, storedPoison, storedPred⟩ :=
                                        guardlessIfCleanMem.lookup hguard_mem_res
                                          (by
                                            simpa [MemoryTypeEnv.lookup] using hlookup)
                                      have hstored_guard :
                                          guardlessIfCleanQTyp
                                            ⟨storedEtyp, storedPoison, storedPred⟩ :=
                                        guardlessIfCleanQTypDeep.guardless hstored_qt
                                      have hstored_closure :
                                          guardlessIfCleanClosureEnv
                                            ⟨storedEtyp, storedPoison, storedPred⟩ :=
                                        guardlessIfCleanQTypDeep.closure hstored_qt
                                      cases hpoison : poison with
                                      | true =>
                                          have hres_eq :
                                              res =
                                                { qualType :=
                                                    ⟨t, true, Predicate.noPred⟩,
                                                  memEnv' := memEnv',
                                                  tagEnv' := tagEnv',
                                                  nextLoc' := nextLoc',
                                                  nextTag' := nextTag' } := by
                                                unfold typecheckDeref at htcDeref
                                                simp [bind, Except.bind, hres, hlookup,
                                                  hcheck, hpoison] at htcDeref
                                                cases htcDeref
                                                rfl
                                          subst hres_eq
                                          constructor
                                          · exact hguard_mem_res
                                          ·
                                            refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                            · intro _hclean
                                              simp [qtypGuardTag]
                                            ·
                                              exact
                                                guardlessIfCleanClosureEnv.congr
                                                  (qt₁ :=
                                                    ⟨storedEtyp, storedPoison,
                                                      storedPred⟩)
                                                  (qt₂ :=
                                                    ⟨t, true, Predicate.noPred⟩)
                                                  (by simp [het])
                                                  hstored_closure
                                      | false =>
                                          cases storedPred with
                                          | noPred =>
                                              have hres_eq :
                                                  res =
                                                    { qualType :=
                                                        ⟨t,
                                                          joinPoison ctx.pc storedPoison,
                                                          Predicate.noPred⟩,
                                                      memEnv' := memEnv',
                                                      tagEnv' := tagEnv',
                                                      nextLoc' := nextLoc',
                                                      nextTag' := nextTag' } := by
                                                    unfold typecheckDeref at htcDeref
                                                    simp [bind, Except.bind, hres, hlookup, hcheck, hpoison] at htcDeref
                                                    cases htcDeref
                                                    rfl
                                              subst hres_eq
                                              constructor
                                              · exact hguard_mem_res
                                              ·
                                                refine guardlessIfCleanQTypDeep.intro
                                                  _ ?_ ?_
                                                · intro _hclean
                                                  simp [qtypGuardTag]
                                                · exact
                                                    guardlessIfCleanClosureEnv.congr
                                                      (qt₁ :=
                                                        ⟨storedEtyp, storedPoison,
                                                          Predicate.noPred⟩)
                                                      (qt₂ :=
                                                        ⟨t,
                                                          joinPoison ctx.pc
                                                            storedPoison,
                                                          Predicate.noPred⟩)
                                                      (by simp [het])
                                                      hstored_closure
                                          | guardClosure k arg body env' =>
                                              cases htag : tagEnv'[k]? with
                                              | none =>
                                                  have hres_eq :
                                                      res =
                                                        { qualType :=
                                                            ⟨t,
                                                              joinPoison ctx.pc
                                                                storedPoison,
                                                              Predicate.guardClosure
                                                                k arg body env'⟩,
                                                          memEnv' := memEnv',
                                                          tagEnv' := tagEnv',
                                                          nextLoc' := nextLoc',
                                                          nextTag' := nextTag' } := by
                                                        unfold typecheckDeref at htcDeref
                                                        simp [bind, Except.bind, pure, Except.pure, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                        cases htcDeref
                                                        rfl
                                                  subst hres_eq
                                                  constructor
                                                  · exact hguard_mem_res
                                                  ·
                                                    refine
                                                      guardlessIfCleanQTypDeep.intro
                                                        _ ?_ ?_
                                                    · intro hpoison_clean
                                                      have hstored_false :
                                                          storedPoison = false := by
                                                            have :
                                                                ctx.pc = false ∧
                                                                  storedPoison = false :=
                                                              by
                                                                simpa [joinPoison]
                                                                  using
                                                                    hpoison_clean
                                                            exact this.2
                                                      have : False := by
                                                        have :=
                                                          hstored_guard
                                                            hstored_false
                                                        simp [qtypGuardTag] at this
                                                      exact this.elim
                                                    ·
                                                      exact
                                                        guardlessIfCleanClosureEnv.congr
                                                          (qt₁ :=
                                                            ⟨storedEtyp,
                                                              storedPoison,
                                                              Predicate.guardClosure
                                                                k arg body env'⟩)
                                                          (qt₂ :=
                                                            ⟨t,
                                                              joinPoison ctx.pc
                                                                storedPoison,
                                                              Predicate.guardClosure
                                                                k arg body env'⟩)
                                                          (by simp [het])
                                                          hstored_closure
                                              | some tv =>
                                                  cases tv with
                                                  | mk b deps =>
                                                      cases b with
                                                      | false =>
                                                          have hres_eq :
                                                              res =
                                                                { qualType :=
                                                                    ⟨t, true,
                                                                      Predicate.noPred⟩,
                                                                  memEnv' :=
                                                                    memEnv',
                                                                  tagEnv' :=
                                                                    tagEnv',
                                                                  nextLoc' :=
                                                                    nextLoc',
                                                                  nextTag' :=
                                                                    nextTag' } := by
                                                                unfold typecheckDeref at htcDeref
                                                                simp [bind, Except.bind, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                                cases htcDeref
                                                                rfl
                                                          subst hres_eq
                                                          constructor
                                                          · exact hguard_mem_res
                                                          ·
                                                            refine
                                                              guardlessIfCleanQTypDeep.intro
                                                                _ ?_ ?_
                                                            · intro _hclean
                                                              simp [qtypGuardTag]
                                                            ·
                                                              exact
                                                                guardlessIfCleanClosureEnv.congr
                                                                  (qt₁ :=
                                                                    ⟨storedEtyp,
                                                                      storedPoison,
                                                                      Predicate.guardClosure
                                                                        k arg body
                                                                        env'⟩)
                                                                  (qt₂ :=
                                                                    ⟨t, true,
                                                                      Predicate.noPred⟩)
                                                                  (by simp [het])
                                                                  hstored_closure
                                                      | true =>
                                                          have hres_eq :
                                                              res =
                                                                { qualType :=
                                                                    ⟨t, ctx.pc,
                                                                      Predicate.noPred⟩,
                                                                  memEnv' :=
                                                                    memEnv',
                                                                  tagEnv' :=
                                                                    tagEnv',
                                                                  nextLoc' :=
                                                                    nextLoc',
                                                                  nextTag' :=
                                                                    nextTag' } := by
                                                                unfold typecheckDeref at htcDeref
                                                                simp [bind, Except.bind, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                                cases htcDeref
                                                                rfl
                                                          subst hres_eq
                                                          constructor
                                                          · exact hguard_mem_res
                                                          ·
                                                            refine
                                                              guardlessIfCleanQTypDeep.intro
                                                                _ ?_ ?_
                                                            · intro _hclean
                                                              simp [qtypGuardTag]
                                                            ·
                                                              exact
                                                                guardlessIfCleanClosureEnv.congr
                                                                  (qt₁ :=
                                                                    ⟨storedEtyp,
                                                                      storedPoison,
                                                                      Predicate.guardClosure
                                                                        k arg body
                                                                        env'⟩)
                                                                  (qt₂ :=
                                                                    ⟨t, ctx.pc,
                                                                      Predicate.noPred⟩)
                                                                  (by simp [het])
                                                                  hstored_closure
                                          | guardOnly k =>
                                              cases htag : tagEnv'[k]? with
                                              | none =>
                                                  have hres_eq :
                                                      res =
                                                        { qualType :=
                                                            ⟨t,
                                                              joinPoison ctx.pc
                                                                storedPoison,
                                                              Predicate.guardOnly
                                                                k⟩,
                                                          memEnv' := memEnv',
                                                          tagEnv' := tagEnv',
                                                          nextLoc' := nextLoc',
                                                          nextTag' := nextTag' } := by
                                                        unfold typecheckDeref at htcDeref
                                                        simp [bind, Except.bind, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                        cases htcDeref
                                                        rfl
                                                  subst hres_eq
                                                  constructor
                                                  · exact hguard_mem_res
                                                  ·
                                                    refine
                                                      guardlessIfCleanQTypDeep.intro
                                                        _ ?_ ?_
                                                    · intro hpoison_clean
                                                      have hstored_false :
                                                          storedPoison = false := by
                                                            have :
                                                                ctx.pc = false ∧
                                                                  storedPoison = false :=
                                                              by
                                                                simpa [joinPoison]
                                                                  using
                                                                    hpoison_clean
                                                            exact this.2
                                                      have : False := by
                                                        have :=
                                                          hstored_guard
                                                            hstored_false
                                                        simp [qtypGuardTag] at this
                                                      exact this.elim
                                                    ·
                                                      exact
                                                        guardlessIfCleanClosureEnv.congr
                                                          (qt₁ :=
                                                            ⟨storedEtyp,
                                                              storedPoison,
                                                              Predicate.guardOnly
                                                                k⟩)
                                                          (qt₂ :=
                                                            ⟨t,
                                                              joinPoison ctx.pc
                                                                storedPoison,
                                                              Predicate.guardOnly
                                                                k⟩)
                                                          (by simp [het])
                                                          hstored_closure
                                              | some tv =>
                                                  cases tv with
                                                  | mk b deps =>
                                                      cases b with
                                                      | false =>
                                                          have hres_eq :
                                                              res =
                                                                { qualType :=
                                                                    ⟨t, true,
                                                                      Predicate.noPred⟩,
                                                                  memEnv' :=
                                                                    memEnv',
                                                                  tagEnv' :=
                                                                    tagEnv',
                                                                  nextLoc' :=
                                                                    nextLoc',
                                                                  nextTag' :=
                                                                    nextTag' } := by
                                                                unfold typecheckDeref at htcDeref
                                                                simp [bind, Except.bind, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                                cases htcDeref
                                                                rfl
                                                          subst hres_eq
                                                          constructor
                                                          · exact hguard_mem_res
                                                          ·
                                                            refine
                                                              guardlessIfCleanQTypDeep.intro
                                                                _ ?_ ?_
                                                            · intro _hclean
                                                              simp [qtypGuardTag]
                                                            ·
                                                              exact
                                                                guardlessIfCleanClosureEnv.congr
                                                                  (qt₁ :=
                                                                    ⟨storedEtyp,
                                                                      storedPoison,
                                                                      Predicate.guardOnly
                                                                        k⟩)
                                                                  (qt₂ :=
                                                                    ⟨t, true,
                                                                      Predicate.noPred⟩)
                                                                  (by simp [het])
                                                                  hstored_closure
                                                      | true =>
                                                          have hres_eq :
                                                              res =
                                                                { qualType :=
                                                                    ⟨t, ctx.pc,
                                                                      Predicate.noPred⟩,
                                                                  memEnv' :=
                                                                    memEnv',
                                                                  tagEnv' :=
                                                                    tagEnv',
                                                                  nextLoc' :=
                                                                    nextLoc',
                                                                  nextTag' :=
                                                                    nextTag' } := by
                                                                unfold typecheckDeref at htcDeref
                                                                simp [bind, Except.bind, hres, hlookup, hcheck, hpoison, htag] at htcDeref
                                                                cases htcDeref
                                                                rfl
                                                          subst hres_eq
                                                          constructor
                                                          · exact hguard_mem_res
                                                          ·
                                                            refine
                                                              guardlessIfCleanQTypDeep.intro
                                                                _ ?_ ?_
                                                            · intro _hclean
                                                              simp [qtypGuardTag]
                                                            ·
                                                              exact
                                                                guardlessIfCleanClosureEnv.congr
                                                                  (qt₁ :=
                                                                    ⟨storedEtyp,
                                                                      storedPoison,
                                                                      Predicate.guardOnly
                                                                        k⟩)
                                                                  (qt₂ :=
                                                                    ⟨t, ctx.pc,
                                                                      Predicate.noPred⟩)
                                                                  (by simp [het])
                                                                  hstored_closure

private lemma guardlessIfClean_invariant_seq
    (e₁ e₂ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.seq e₁ e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcSeq : typecheckSeq ctx e₁ e₂ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckSeq] at htcSeq
      | succ fuelInner =>
          cases hres₁ : typecheckExpr ctx e₁ fuelInner with
          | error err =>
              have hcontr := htcSeq
              simp [typecheckSeq, hres₁, bind, Except.bind] at hcontr
          | ok result₁ =>
              cases result₁ with
              | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                  cases qt₁ with
                  | mk etyp₁ poison₁ pred₁ =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hresult₁_guard :
                          guardlessIfCleanMem memEnv₁ ∧
                            guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e₁)
                          (res' :=
                            { qualType := ⟨etyp₁, poison₁, pred₁⟩, memEnv' := memEnv₁,
                              tagEnv' := tagEnv₁, nextLoc' := nextLoc₁,
                              nextTag' := nextTag₁ })
                          hmem hvars
                          (by simpa [typecheck] using hres₁)
                      have hguard₁ : guardlessIfCleanMem memEnv₁ :=
                        hresult₁_guard.left
                      let ctx' : TypeContext :=
                        { ctx with
                          memEnv := memEnv₁,
                          tagEnv := tagEnv₁,
                          nextLoc := nextLoc₁,
                          nextTag := nextTag₁ }
                      have hmem_ctx' : guardlessIfCleanMem ctx'.memEnv := by
                        simpa [ctx'] using hguard₁
                      have hvars_ctx' : guardlessIfCleanVars ctx'.varEnv := by
                        simpa [ctx'] using hvars
                      cases hres₂ : typecheckExpr ctx' e₂ fuelInner with
                      | error err =>
                          have hcontr := htcSeq
                          simp [typecheckSeq, hres₁, ctx', hres₂, bind, Except.bind] at hcontr
                      | ok result₂ =>
                          cases result₂ with
                          | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                              cases qt₂ with
                              | mk etyp₂ poison₂ pred₂ =>
                                  have hresult₂_guard :
                                      guardlessIfCleanMem memEnv₂ ∧
                                        guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                    IH (fuel' := fuelInner) hfuel (ctx := ctx') (e' := e₂)
                                      (res' :=
                                        { qualType := ⟨etyp₂, poison₂, pred₂⟩, memEnv' := memEnv₂,
                                          tagEnv' := tagEnv₂, nextLoc' := nextLoc₂,
                                          nextTag' := nextTag₂ })
                                      hmem_ctx'
                                      hvars_ctx'
                                      (by simpa [typecheck, ctx'] using hres₂)
                                  have hguard₂ : guardlessIfCleanMem memEnv₂ :=
                                    hresult₂_guard.left
                                  have hqt₂_deep :
                                      guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                    hresult₂_guard.right
                                  have hres_eq :
                                      Except.ok
                                          { qualType :=
                                              { etyp := etyp₂,
                                                poison := joinPoison poison₁ poison₂,
                                                pred := pred₂ },
                                            memEnv' := memEnv₂,
                                            tagEnv' := tagEnv₂,
                                            nextLoc' := nextLoc₂,
                                            nextTag' := nextTag₂ } =
                                        @Except.ok String TypeResult res := by
                                    rw [← htcSeq]
                                    unfold typecheckSeq
                                    simp [bind, Except.bind, pure, Except.pure,
                                      hres₁, ctx', hres₂]
                                  cases hres_eq
                                  dsimp
                                  constructor
                                  · exact hguard₂
                                  · have hqt₂_guard :
                                        guardlessIfCleanQTyp ⟨etyp₂, poison₂, pred₂⟩ :=
                                      guardlessIfCleanQTypDeep.guardless hqt₂_deep
                                    have hqt₂_closure :
                                        guardlessIfCleanClosureEnv ⟨etyp₂, poison₂, pred₂⟩ :=
                                      guardlessIfCleanQTypDeep.closure hqt₂_deep
                                    refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                    · intro hpoison_clean
                                      cases poison₂ with
                                      | false =>
                                          have hguard_tag :=
                                            hqt₂_guard (by rfl)
                                          simpa [qtypGuardTag] using hguard_tag
                                      | true =>
                                          have hcontr : False := by
                                            cases poison₁ with
                                            | false =>
                                                simp [joinPoison] at hpoison_clean
                                            | true =>
                                                simp [joinPoison] at hpoison_clean
                                          exact False.elim hcontr
                                    · exact
                                        guardlessIfCleanClosureEnv.congr
                                          (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                          (qt₂ := ⟨etyp₂, joinPoison poison₁ poison₂, pred₂⟩)
                                          rfl
                                          hqt₂_closure

private lemma guardlessIfClean_invariant_while
    (e₁ e₂ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.kwhile e₁ e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcWhile : typecheckWhile ctx e₁ e₂ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckWhile] at htcWhile
      | succ fuelFix =>
          cases hguard : matchGuard e₁ ctx.memEnv ctx.varEnv with
          | ok guardInfo =>
              rcases guardInfo with ⟨k, deps⟩
              have htcDepoison :
                  typecheckWhileDepoison ctx e₁ e₂ fuelFix k deps = .ok res := by
                simpa [typecheckWhile, hguard] using htcWhile
              cases fuelFix with
              | zero =>
                  simp [typecheckWhileDepoison] at htcDepoison
              | succ fuelInner =>
                  cases hfix :
                      runWhileFixpoint ctx e₁ e₂ fuelInner true (some (k, deps)) with
                  | error err =>
                      have hcontr := htcDepoison
                      simp [typecheckWhileDepoison, hfix, bind, Except.bind] at hcontr
                  | ok result =>
                      rcases result with
                        ⟨pcFinal, memFinal, tagFinal, nextLocFinal, nextTagFinal⟩
                      set fuel := Nat.succ (Nat.succ (Nat.succ fuelInner))
                      have hfuel_lt : fuelInner < fuel := by
                        simp [fuel]
                        exact Nat.lt_of_le_of_lt
                          (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
                          (Nat.lt_succ_self _)
                      have hmem_final :
                          guardlessIfCleanMem memFinal :=
                        guardlessIfClean_runWhileFixpoint
                          (fuelBound := fuel) IH e₁ e₂
                          (ctx := ctx) (fuelFix := fuelInner)
                          (pureGuard := true)
                          (guardOpt := some (k, deps))
                          (pcFinal := pcFinal) (memFinal := memFinal)
                          (tagFinal := tagFinal)
                          (nextLocFinal := nextLocFinal)
                          (nextTagFinal := nextTagFinal)
                          hmem hvars hfuel_lt hfix
                      have hres_eq := htcDepoison
                      simp [typecheckWhileDepoison, hfix, bind, Except.bind,
                        pure, Except.pure] at hres_eq
                      cases hres_eq
                      dsimp
                      constructor
                      · exact hmem_final
                      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                        · intro _; simp [qtypGuardTag]
                        · simp [nonClosureQTyp]
          | error err =>
              have htcStd :
                  typecheckWhileStd ctx e₁ e₂ fuelFix = .ok res := by
                simpa [typecheckWhile, hguard] using htcWhile
              cases fuelFix with
              | zero =>
                  simp [typecheckWhileStd] at htcStd
              | succ fuelInner =>
                  cases hfix :
                      runWhileFixpoint ctx e₁ e₂ fuelInner false none with
                  | error err₂ =>
                      have hcontr := htcStd
                      simp [typecheckWhileStd, hfix, bind, Except.bind] at hcontr
                  | ok result =>
                      rcases result with
                        ⟨pcFinal, memFinal, tagFinal, nextLocFinal, nextTagFinal⟩
                      set fuel := Nat.succ (Nat.succ (Nat.succ fuelInner))
                      have hfuel_lt : fuelInner < fuel := by
                        simp [fuel]
                        exact Nat.lt_of_le_of_lt
                          (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
                          (Nat.lt_succ_self _)
                      have hmem_final :
                          guardlessIfCleanMem memFinal :=
                        guardlessIfClean_runWhileFixpoint
                          (fuelBound := fuel) IH e₁ e₂
                          (ctx := ctx) (fuelFix := fuelInner)
                          (pureGuard := false)
                          (guardOpt := none)
                          (pcFinal := pcFinal) (memFinal := memFinal)
                          (tagFinal := tagFinal)
                          (nextLocFinal := nextLocFinal)
                          (nextTagFinal := nextTagFinal)
                          hmem hvars hfuel_lt hfix
                      have hres_eq := htcStd
                      simp [typecheckWhileStd, hfix, bind, Except.bind,
                        pure, Except.pure] at hres_eq
                      cases hres_eq
                      dsimp
                      constructor
                      · exact hmem_final
                      · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                        · intro _; simp [qtypGuardTag]
                        · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_vlet
    (x : Name) (e₁ e₂ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.vlet x e₁ e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  classical
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcVlet : typecheckVlet ctx x e₁ e₂ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckVlet] at htcVlet
      | succ fuelInner =>
          cases hres₁ : typecheckExpr ctx e₁ fuelInner with
          | error err =>
              have hcontr := htcVlet
              simp [typecheckVlet, hres₁] at hcontr
              cases hcontr
          | ok result₁ =>
              cases result₁ with
              | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                  cases qt₁ with
                  | mk etyp₁ poison₁ pred₁ =>
                      have hfuel :
                          fuelInner < Nat.succ (Nat.succ fuelInner) :=
                        Nat.lt_succ_of_lt (Nat.lt_succ_self fuelInner)
                      have hresult₁_guard :
                          guardlessIfCleanMem memEnv₁ ∧
                            guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e₁)
                          (res' :=
                            { qualType := ⟨etyp₁, poison₁, pred₁⟩, memEnv' := memEnv₁,
                              tagEnv' := tagEnv₁, nextLoc' := nextLoc₁,
                              nextTag' := nextTag₁ })
                          hmem hvars
                          (by simpa [typecheck] using hres₁)
                      have hguard₁ : guardlessIfCleanMem memEnv₁ :=
                        hresult₁_guard.left
                      have hqt₁_deep :
                          guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        hresult₁_guard.right
                      let varEnv' := ctx.varEnv.update x ⟨etyp₁, poison₁, pred₁⟩
                      have hvars' : guardlessIfCleanVars varEnv' :=
                        guardlessIfCleanVars_update hvars hqt₁_deep
                      let ctx' : TypeContext :=
                        { ctx with
                          memEnv := memEnv₁,
                          varEnv := varEnv',
                          tagEnv := tagEnv₁,
                          nextLoc := nextLoc₁,
                          nextTag := nextTag₁ }
                      have hmem_ctx' : guardlessIfCleanMem ctx'.memEnv := by
                        simpa [ctx'] using hguard₁
                      have hvars_ctx' : guardlessIfCleanVars ctx'.varEnv := by
                        simpa [ctx', varEnv'] using hvars'
                      cases hres₂ :
                          typecheckExpr ctx' e₂ fuelInner with
                      | error err =>
                          have hcontr := htcVlet
                          simp [typecheckVlet, hres₁] at hcontr
                          simp [bind, pure, Except.bind, Except.pure] at hcontr
                          simp [varEnv', ctx', hres₂] at hcontr
                      | ok result₂ =>
                          cases result₂ with
                          | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                              cases qt₂ with
                              | mk etyp₂ poison₂ pred₂ =>
                                  have hresult₂_guard :
                                      guardlessIfCleanMem memEnv₂ ∧
                                        guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                    IH (fuel' := fuelInner) hfuel (ctx := ctx') (e' := e₂)
                                      (res' :=
                                        { qualType := ⟨etyp₂, poison₂, pred₂⟩, memEnv' := memEnv₂,
                                          tagEnv' := tagEnv₂, nextLoc' := nextLoc₂,
                                          nextTag' := nextTag₂ })
                                      hmem_ctx'
                                      hvars_ctx'
                                      (by simpa [typecheck, ctx'] using hres₂)
                                  have hguard₂ : guardlessIfCleanMem memEnv₂ :=
                                    hresult₂_guard.left
                                  have hqt₂_deep :
                                      guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                    hresult₂_guard.right
                                  have hres_eq := htcVlet
                                  simp [typecheckVlet, hres₁, varEnv', ctx', hres₂,
                                    bind, Except.bind, pure, Except.pure] at hres_eq
                                  cases hres_eq
                                  dsimp
                                  constructor
                                  · exact hguard₂
                                  · have hqt₂_guard :
                                        guardlessIfCleanQTyp ⟨etyp₂, poison₂, pred₂⟩ :=
                                      guardlessIfCleanQTypDeep.guardless hqt₂_deep
                                    have hqt₂_closure :
                                        guardlessIfCleanClosureEnv ⟨etyp₂, poison₂, pred₂⟩ :=
                                      guardlessIfCleanQTypDeep.closure hqt₂_deep
                                    refine guardlessIfCleanQTypDeep.intro _ ?_ ?_
                                    · intro hpoison_clean
                                      cases hpc : ctx.pc with
                                      | false =>
                                          have hpoison₂_false : poison₂ = false := by
                                            simp [joinPoison, hpc] at hpoison_clean
                                            apply hpoison_clean
                                          have hguard_tag := hqt₂_guard (by simp [hpoison₂_false])
                                          simpa [joinPoison, hpc, hpoison₂_false, qtypGuardTag] using hguard_tag
                                      | true =>
                                          simp [joinPoison, hpc] at hpoison_clean
                                    · exact
                                        guardlessIfCleanClosureEnv.congr
                                          (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                          (qt₂ := ⟨etyp₂, joinPoison ctx.pc poison₂, pred₂⟩)
                                          rfl
                                          hqt₂_closure

private lemma guardlessIfClean_invariant_fn
    (x : Name) (st₁ st₂ : Typ) (body : Expr)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (_hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.fn x st₁ body st₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero => simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      simp [typecheck, typecheckExpr, typecheckFn] at htc
      cases htc
      dsimp
      constructor
      · exact hmem
      · have hvars : guardlessIfCleanVars ctx.varEnv := _hvars
        let qt : QTyp :=
          ⟨ETyp.arrow st₁ st₂ false (FnTClosure.mk x body ctx.varEnv), ctx.pc,
            Predicate.noPred⟩
        refine guardlessIfCleanQTypDeep.intro qt ?_ ?_
        · intro _hpoison_clean
          simp [qt, qtypGuardTag]
        · have hclosureEq :  qt.etyp = ETyp.arrow st₁ st₂ false (FnTClosure.mk x body ctx.varEnv) := by
            simp [qt]
          exact guardlessIfCleanClosureEnv.arrow (qt := qt) (env := ctx.varEnv) hclosureEq hvars

private lemma guardlessIfClean_invariant_pfn
    (x : Name) (st₁ st₂ : Typ) (body : Expr)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (_hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.pfn x st₁ body st₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero => simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      cases hto : body.toPExpr with
      | error err =>
          have hcontr := htc
          simp [typecheck, typecheckExpr, typecheckPfn, hto] at hcontr
      | ok pbody =>
          simp [typecheck, typecheckExpr, typecheckPfn, hto] at htc
          cases htc
          dsimp
          constructor
          · exact hmem
          · have hvars : guardlessIfCleanVars ctx.varEnv := _hvars
            let qt : QTyp :=
              ⟨ETyp.parrow st₁ st₂ false (PFnTClosure.mk x pbody ctx.varEnv), ctx.pc,
                Predicate.noPred⟩
            refine guardlessIfCleanQTypDeep.intro qt ?_ ?_
            · intro _hpoison_clean
              simp [qt, qtypGuardTag]
            · have hclosureEq : qt.etyp = ETyp.parrow st₁ st₂ false (PFnTClosure.mk x pbody ctx.varEnv) := by
                simp [qt]
              exact guardlessIfCleanClosureEnv.parrow (qt := qt) (env := ctx.varEnv) hclosureEq hvars

private lemma guardlessIfClean_invariant_app
    (e₁ e₂ : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.app e₁ e₂) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcApp : typecheckApp ctx e₁ e₂ fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          simp [typecheckApp] at htcApp
      | succ fuelInner =>
          classical
          have hfuel :
              fuelInner < Nat.succ (Nat.succ fuelInner) := by
            exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ (Nat.lt_succ_self _))
          cases hres₁ : typecheckExpr ctx e₁ fuelInner with
          | error err =>
              have hcontr := htcApp
              simp [typecheckApp, hres₁] at hcontr
              cases hcontr
          | ok result₁ =>
              cases result₁ with
              | mk qt₁ memEnv₁ tagEnv₁ nextLoc₁ nextTag₁ =>
                  cases qt₁ with
                  | mk etyp₁ poison₁ pred₁ =>
                      have hresult₁_guard :
                          guardlessIfCleanMem memEnv₁ ∧
                            guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e₁)
                          (res' :=
                            { qualType := ⟨etyp₁, poison₁, pred₁⟩,
                              memEnv' := memEnv₁, tagEnv' := tagEnv₁,
                              nextLoc' := nextLoc₁, nextTag' := nextTag₁ })
                          hmem hvars (by simpa [typecheck] using hres₁)
                      have hmem₁ : guardlessIfCleanMem memEnv₁ := hresult₁_guard.left
                      have hqt₁_deep :
                          guardlessIfCleanQTypDeep ⟨etyp₁, poison₁, pred₁⟩ :=
                        hresult₁_guard.right
                      have hqt₁_closure :
                          guardlessIfCleanClosureEnv ⟨etyp₁, poison₁, pred₁⟩ :=
                        guardlessIfCleanQTypDeep.closure hqt₁_deep
                      cases etyp₁ with
                      | int =>
                          have hcontr := htcApp
                          simp [typecheckApp, hres₁] at hcontr
                          cases hcontr
                      | bool =>
                          have hcontr := htcApp
                          simp [typecheckApp, hres₁] at hcontr
                          cases hcontr
                      | unit =>
                          have hcontr := htcApp
                          simp [typecheckApp, hres₁] at hcontr
                          cases hcontr
                      | string =>
                          have hcontr := htcApp
                          simp [typecheckApp, hres₁] at hcontr
                          cases hcontr
                      | ref t l =>
                          have hcontr := htcApp
                          simp [typecheckApp, hres₁] at hcontr
                          cases hcontr
                      | arrow st₁ st₂ p tcl =>
                          cases hpc : ctx.pureCtx with
                          | true =>
                              have hcontr := htcApp
                              simp [typecheckApp, hres₁, hpc] at hcontr
                              cases hcontr
                          | false =>
                              let ctx' :=
                                { ctx with
                                    memEnv := memEnv₁,
                                    tagEnv := tagEnv₁,
                                    nextLoc := nextLoc₁,
                                    nextTag := nextTag₁ }
                              have hmem_ctx' : guardlessIfCleanMem ctx'.memEnv := by
                                simpa [ctx'] using hmem₁
                              have hvars_ctx' : guardlessIfCleanVars ctx'.varEnv := by
                                simpa [ctx'] using hvars
                              cases hres₂ : typecheckExpr ctx' e₂ fuelInner with
                              | error err =>
                                  have hcontr := htcApp
                                  simp [typecheckApp, hres₁, hpc] at hcontr
                                  simp [bind, pure, Except.bind, Except.pure] at hcontr
                                  simp [ctx', hpc] at hres₂
                                  simp [hres₂] at hcontr
                              | ok result₂ =>
                                  cases result₂ with
                                  | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                                      cases qt₂ with
                                      | mk etyp₂ poison₂ pred₂ =>
                                          have hresult₂_guard :
                                              guardlessIfCleanMem memEnv₂ ∧
                                                guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                            IH (fuel' := fuelInner) hfuel (ctx := ctx') (e' := e₂)
                                              (res' :=
                                                { qualType := ⟨etyp₂, poison₂, pred₂⟩,
                                                  memEnv' := memEnv₂,
                                                  tagEnv' := tagEnv₂,
                                                  nextLoc' := nextLoc₂,
                                                  nextTag' := nextTag₂ })
                                              hmem_ctx'
                                              hvars_ctx'
                                              (by simpa [typecheck, ctx'] using hres₂)
                                          have hmem₂ : guardlessIfCleanMem memEnv₂ := hresult₂_guard.left
                                          have hqt₂_deep :
                                              guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                            hresult₂_guard.right
                                          have hqt₂_guard :
                                              guardlessIfCleanQTyp ⟨etyp₂, poison₂, pred₂⟩ :=
                                            guardlessIfCleanQTypDeep.guardless hqt₂_deep
                                          have hqt₂_closure :
                                              guardlessIfCleanClosureEnv ⟨etyp₂, poison₂, pred₂⟩ :=
                                            guardlessIfCleanQTypDeep.closure hqt₂_deep
                                          cases hsub : isSubtype st₁ ⟨etyp₂, poison₂, pred₂⟩ with
                                          | false =>
                                              have hcontr := htcApp
                                              simp [typecheckApp, hres₁, hpc] at hcontr
                                              simp [bind, pure, Except.bind, Except.pure] at hcontr
                                              simp [ctx', hpc] at hres₂
                                              simp [hres₂, hsub] at hcontr
                                          | true =>
                                              cases tcl with
                                              | mk x body env =>
                                                  have hvars_env :
                                                      guardlessIfCleanVars env := by
                                                    cases hqt₁_closure with
                                                    | arrow qt env' heq hvars_env' =>
                                                        cases heq
                                                        simpa using hvars_env'
                                                    | parrow qt env' heq _ =>
                                                        cases heq
                                                    | other _ hnc =>
                                                        cases hnc
                                                  let argQt : QTyp :=
                                                    ⟨etyp₂, joinPoison ctx.pc poison₂, pred₂⟩
                                                  have harg_guardless :
                                                      guardlessIfCleanQTypDeep argQt := by
                                                    refine guardlessIfCleanQTypDeep.intro argQt ?_ ?_
                                                    · intro hpoison_clean
                                                      cases poison₂ with
                                                      | false =>
                                                          have hguard_tag := hqt₂_guard (by rfl)
                                                          simpa [argQt, qtypGuardTag] using hguard_tag
                                                      | true =>
                                                          have hcontr : False := by
                                                            cases ctx.pc with
                                                            | false =>
                                                                simp [argQt, joinPoison] at hpoison_clean
                                                            | true =>
                                                                simp [argQt, joinPoison] at hpoison_clean
                                                          exact False.elim hcontr
                                                    · exact
                                                        guardlessIfCleanClosureEnv.congr
                                                          (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                                          (qt₂ := argQt)
                                                          rfl
                                                          hqt₂_closure
                                                  let env' := VarTypeEnv.update env x argQt
                                                  have hvars_env' :
                                                      guardlessIfCleanVars env' :=
                                                    guardlessIfCleanVars_update hvars_env harg_guardless
                                                  let ctx'' :=
                                                    { ctx with
                                                        pc := joinPoison p (joinPoison ctx.pc poison₁),
                                                        memEnv := memEnv₂,
                                                        varEnv := env',
                                                        tagEnv := tagEnv₂,
                                                        nextTag := nextTag₂,
                                                        nextLoc := nextLoc₂ }
                                                  have hmem_ctx'' : guardlessIfCleanMem ctx''.memEnv := by
                                                    simpa [ctx''] using hmem₂
                                                  have hvars_ctx'' : guardlessIfCleanVars ctx''.varEnv := by
                                                    simpa [ctx'', env'] using hvars_env'
                                                  cases hres₃ : typecheckExpr ctx'' body fuelInner with
                                                  | error err =>
                                                      have hcontr := htcApp
                                                      simp [typecheckApp, hres₁, hpc] at hcontr
                                                      simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                      simp [ctx', hpc] at hres₂
                                                      simp [ctx'', env', argQt, hpc] at hres₃
                                                      simp [hres₂, hsub, hres₃] at hcontr
                                                  | ok result₃ =>
                                                      cases result₃ with
                                                      | mk qt₃ memEnv₃ tagEnv₃ nextLoc₃ nextTag₃ =>
                                                          cases qt₃ with
                                                          | mk etyp₃ poison₃ pred₃ =>
                                                              have hresult₃_guard :
                                                                  guardlessIfCleanMem memEnv₃ ∧
                                                                    guardlessIfCleanQTypDeep
                                                                      ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                IH (fuel' := fuelInner) hfuel
                                                                  (ctx := ctx'') (e' := body)
                                                                  (res' :=
                                                                    { qualType := ⟨etyp₃, poison₃, pred₃⟩,
                                                                      memEnv' := memEnv₃,
                                                                      tagEnv' := tagEnv₃,
                                                                      nextLoc' := nextLoc₃,
                                                                      nextTag' := nextTag₃ })
                                                                  hmem_ctx'' hvars_ctx''
                                                                  (by simpa [typecheck, ctx''] using hres₃)
                                                              have hmem₃ : guardlessIfCleanMem memEnv₃ :=
                                                                hresult₃_guard.left
                                                              cases hsub₂ :
                                                                  isSubtype st₂ ⟨etyp₃, poison₃, pred₃⟩ with
                                                              | false =>
                                                                  have hcontr := htcApp
                                                                  simp [typecheckApp, hres₁, hpc] at hcontr
                                                                  simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                                  simp [ctx', hpc] at hres₂
                                                                  simp [ctx'', env', argQt, hpc] at hres₃
                                                                  simp [hres₂, hsub, hres₃, hsub₂] at hcontr
                                                                  simp [Functor.map, Except.map] at hcontr
                                                              | true =>
                                                                  have hres_eq :
                                                                      Except.ok
                                                                          { qualType :=
                                                                              { etyp := etyp₃,
                                                                                poison := joinPoison ctx.pc poison₃,
                                                                                pred := pred₃ },
                                                                            memEnv' := memEnv₃,
                                                                            tagEnv' := tagEnv₃,
                                                                            nextLoc' := nextLoc₃,
                                                                            nextTag' := nextTag₃ } =
                                                                        @Except.ok String TypeResult res := by
                                                                    rw [← htcApp]
                                                                    simp [typecheckApp, bind, Except.bind, pure, Except.pure]
                                                                    simp [ctx', hpc] at hres₂
                                                                    simp [ctx'', env', argQt, hpc] at hres₃
                                                                    simp [hres₁, hpc, hres₂, hsub, hres₃, hsub₂]
                                                                  cases hres_eq
                                                                  constructor
                                                                  · exact hmem₃
                                                                  · dsimp
                                                                    have hqt₃_deep :
                                                                        guardlessIfCleanQTypDeep
                                                                          ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                      hresult₃_guard.right
                                                                    have hqt₃_guard :
                                                                        guardlessIfCleanQTyp
                                                                          ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                      guardlessIfCleanQTypDeep.guardless
                                                                        hqt₃_deep
                                                                    have hqt₃_closure :
                                                                        guardlessIfCleanClosureEnv
                                                                          ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                      guardlessIfCleanQTypDeep.closure
                                                                        hqt₃_deep
                                                                    refine guardlessIfCleanQTypDeep.intro
                                                                      ⟨etyp₃, joinPoison ctx.pc poison₃, pred₃⟩
                                                                      ?_ ?_
                                                                    · intro hpoison_clean
                                                                      cases hcpc : ctx.pc with
                                                                      | false =>
                                                                          cases poison₃ with
                                                                          | false =>
                                                                              have hguard := hqt₃_guard rfl
                                                                              simpa [joinPoison, hcpc] using hguard
                                                                          | true =>
                                                                              simp [joinPoison, hcpc] at hpoison_clean
                                                                      | true =>
                                                                          cases poison₃ with
                                                                          | false =>
                                                                              simp [joinPoison, hcpc] at hpoison_clean
                                                                          | true =>
                                                                              simp [joinPoison, hcpc] at hpoison_clean
                                                                    · exact
                                                                        guardlessIfCleanClosureEnv.congr
                                                                          (qt₁ := ⟨etyp₃, poison₃, pred₃⟩)
                                                                          (qt₂ :=
                                                                            ⟨etyp₃, joinPoison ctx.pc poison₃, pred₃⟩)
                                                                          rfl
                                                                          hqt₃_closure
                      | parrow st₁ st₂ p tcl =>
                          let ctx' :=
                            { ctx with
                                memEnv := memEnv₁,
                                tagEnv := tagEnv₁,
                                nextLoc := nextLoc₁,
                                nextTag := nextTag₁ }
                          have hmem_ctx' : guardlessIfCleanMem ctx'.memEnv := by
                            simpa [ctx'] using hmem₁
                          have hvars_ctx' : guardlessIfCleanVars ctx'.varEnv := by
                            simpa [ctx'] using hvars
                          cases hres₂ : typecheckExpr ctx' e₂ fuelInner with
                          | error err =>
                              have hcontr := htcApp
                              simp [typecheckApp, hres₁] at hcontr
                              simp [bind, pure, Except.bind, Except.pure] at hcontr
                              simp [ctx'] at hres₂
                              simp [hres₂] at hcontr
                          | ok result₂ =>
                              cases result₂ with
                              | mk qt₂ memEnv₂ tagEnv₂ nextLoc₂ nextTag₂ =>
                                  cases qt₂ with
                                  | mk etyp₂ poison₂ pred₂ =>
                                      have hresult₂_guard :
                                          guardlessIfCleanMem memEnv₂ ∧
                                            guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                        IH (fuel' := fuelInner) hfuel (ctx := ctx') (e' := e₂)
                                          (res' :=
                                            { qualType := ⟨etyp₂, poison₂, pred₂⟩,
                                              memEnv' := memEnv₂,
                                              tagEnv' := tagEnv₂,
                                              nextLoc' := nextLoc₂,
                                              nextTag' := nextTag₂ })
                                          hmem_ctx'
                                          hvars_ctx'
                                          (by simpa [typecheck, ctx'] using hres₂)
                                      have hmem₂ : guardlessIfCleanMem memEnv₂ := hresult₂_guard.left
                                      have hqt₂_deep :
                                          guardlessIfCleanQTypDeep ⟨etyp₂, poison₂, pred₂⟩ :=
                                        hresult₂_guard.right
                                      have hqt₂_guard :
                                          guardlessIfCleanQTyp ⟨etyp₂, poison₂, pred₂⟩ :=
                                        guardlessIfCleanQTypDeep.guardless hqt₂_deep
                                      have hqt₂_closure :
                                          guardlessIfCleanClosureEnv ⟨etyp₂, poison₂, pred₂⟩ :=
                                        guardlessIfCleanQTypDeep.closure hqt₂_deep
                                      cases hsub : isSubtype st₁ ⟨etyp₂, poison₂, pred₂⟩ with
                                      | false =>
                                          have hcontr := htcApp
                                          simp [typecheckApp, hres₁] at hcontr
                                          simp [bind, pure, Except.bind, Except.pure] at hcontr
                                          simp [ctx'] at hres₂
                                          simp [hres₂, hsub] at hcontr
                                      | true =>
                                          cases tcl with
                                          | mk x body env =>
                                              have hvars_env :
                                                  guardlessIfCleanVars env := by
                                                cases hqt₁_closure with
                                                | arrow _ _ heq _ =>
                                                    cases heq
                                                | parrow qt env' heq hvars_env' =>
                                                    cases heq
                                                    simpa using hvars_env'
                                                | other _ hnc =>
                                                    cases hnc
                                              let argQt : QTyp :=
                                                ⟨etyp₂, joinPoison ctx.pc poison₂, pred₂⟩
                                              have harg_guardless :
                                                  guardlessIfCleanQTypDeep argQt := by
                                                refine guardlessIfCleanQTypDeep.intro argQt ?_ ?_
                                                · intro hpoison_clean
                                                  cases poison₂ with
                                                  | false =>
                                                      have hguard_tag := hqt₂_guard (by rfl)
                                                      simpa [argQt, qtypGuardTag] using hguard_tag
                                                  | true =>
                                                      have hcontr : False := by
                                                        cases ctx.pc with
                                                        | false =>
                                                            simp [argQt, joinPoison] at hpoison_clean
                                                        | true =>
                                                            simp [argQt, joinPoison] at hpoison_clean
                                                      exact False.elim hcontr
                                                · exact
                                                    guardlessIfCleanClosureEnv.congr
                                                      (qt₁ := ⟨etyp₂, poison₂, pred₂⟩)
                                                      (qt₂ := argQt)
                                                      rfl
                                                      hqt₂_closure
                                              let env' := VarTypeEnv.update env x argQt
                                              have hvars_env' :
                                                  guardlessIfCleanVars env' :=
                                                guardlessIfCleanVars_update hvars_env harg_guardless
                                              let ctx'' :=
                                                { ctx with
                                                    pc := joinPoison p (joinPoison ctx.pc poison₁),
                                                    memEnv := memEnv₂,
                                                    varEnv := env',
                                                    tagEnv := tagEnv₂,
                                                    pureCtx := true,
                                                    nextTag := nextTag₂,
                                                    nextLoc := nextLoc₂ }
                                              have hmem_ctx'' : guardlessIfCleanMem ctx''.memEnv := by
                                                simpa [ctx''] using hmem₂
                                              have hvars_ctx'' : guardlessIfCleanVars ctx''.varEnv := by
                                                simpa [ctx'', env'] using hvars_env'
                                              cases hres₃ :
                                                  typecheckExpr ctx'' (PExpr.toExpr body) fuelInner with
                                              | error err =>
                                                  have hcontr := htcApp
                                                  simp [typecheckApp, hres₁] at hcontr
                                                  simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                  simp [ctx'] at hres₂
                                                  simp [ctx'', env', argQt] at hres₃
                                                  simp [hres₂, hsub, hres₃] at hcontr
                                              | ok result₃ =>
                                                  cases result₃ with
                                                  | mk qt₃ memEnv₃ tagEnv₃ nextLoc₃ nextTag₃ =>
                                                      cases qt₃ with
                                                      | mk etyp₃ poison₃ pred₃ =>
                                                          have hresult₃_guard :
                                                              guardlessIfCleanMem memEnv₃ ∧
                                                                guardlessIfCleanQTypDeep
                                                                  ⟨etyp₃, poison₃, pred₃⟩ :=
                                                            IH (fuel' := fuelInner) hfuel
                                                              (ctx := ctx'') (e' := PExpr.toExpr body)
                                                              (res' :=
                                                                { qualType := ⟨etyp₃, poison₃, pred₃⟩,
                                                                  memEnv' := memEnv₃,
                                                                  tagEnv' := tagEnv₃,
                                                                  nextLoc' := nextLoc₃,
                                                                  nextTag' := nextTag₃ })
                                                              hmem_ctx'' hvars_ctx''
                                                              (by
                                                                simpa [typecheck, ctx''] using hres₃)
                                                          have hmem₃ : guardlessIfCleanMem memEnv₃ :=
                                                            hresult₃_guard.left
                                                          cases hsub₂ :
                                                            isSubtype st₂ ⟨etyp₃, poison₃, pred₃⟩ with
                                                          | false =>
                                                              have hcontr := htcApp
                                                              simp [typecheckApp, hres₁] at hcontr
                                                              simp [bind, pure, Except.bind, Except.pure] at hcontr
                                                              simp [ctx'] at hres₂
                                                              simp [ctx'', env', argQt] at hres₃
                                                              simp [hres₂, hsub, hres₃, hsub₂] at hcontr
                                                              simp [Functor.map, Except.map] at hcontr
                                                          | true =>
                                                              have hres_eq :
                                                                  Except.ok
                                                                      { qualType :=
                                                                          { etyp := etyp₃,
                                                                            poison := joinPoison ctx.pc poison₃,
                                                                            pred := pred₃ },
                                                                        memEnv' := memEnv₃,
                                                                        tagEnv' := tagEnv₃,
                                                                        nextLoc' := nextLoc₃,
                                                                        nextTag' := nextTag₃ } =
                                                                    @Except.ok String TypeResult res := by
                                                                rw [← htcApp]
                                                                simp [typecheckApp, bind, Except.bind, pure, Except.pure]
                                                                simp [ctx'] at hres₂
                                                                simp [ctx'', env', argQt] at hres₃
                                                                simp [hres₁, hres₂, hsub, hres₃, hsub₂]
                                                              cases hres_eq
                                                              constructor
                                                              · exact hmem₃
                                                              · dsimp
                                                                have hqt₃_deep : guardlessIfCleanQTypDeep ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                  hresult₃_guard.right
                                                                have hqt₃_guard : guardlessIfCleanQTyp ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                  guardlessIfCleanQTypDeep.guardless hqt₃_deep
                                                                have hqt₃_closure : guardlessIfCleanClosureEnv ⟨etyp₃, poison₃, pred₃⟩ :=
                                                                  guardlessIfCleanQTypDeep.closure hqt₃_deep
                                                                refine guardlessIfCleanQTypDeep.intro
                                                                  ⟨etyp₃, joinPoison ctx.pc poison₃, pred₃⟩
                                                                  ?_ ?_
                                                                · intro hpoison_clean
                                                                  cases hcpc : ctx.pc with
                                                                  | false =>
                                                                      cases poison₃ with
                                                                      | false =>
                                                                          have hguard := hqt₃_guard rfl
                                                                          simpa [joinPoison, hcpc] using hguard
                                                                      | true => simp [joinPoison, hcpc] at hpoison_clean
                                                                  | true =>
                                                                      cases poison₃ with
                                                                      | false => simp [joinPoison, hcpc] at hpoison_clean
                                                                      | true => simp [joinPoison, hcpc] at hpoison_clean
                                                                · exact
                                                                    guardlessIfCleanClosureEnv.congr
                                                                      (qt₁ := ⟨etyp₃, poison₃, pred₃⟩)
                                                                      (qt₂ := ⟨etyp₃, joinPoison ctx.pc poison₃, pred₃⟩)
                                                                      rfl
                                                                      hqt₃_closure


private lemma guardlessIfClean_invariant_rand
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.rand e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcRand : typecheckRand ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          have hcontr := htcRand
          simp [typecheckRand] at hcontr
      | succ fuelInner =>
          have htcRand' := htcRand
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcRand'
              simp [typecheckRand, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) := by
                    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ (Nat.lt_succ_self _))
                  have hresult_guard :
                      guardlessIfCleanMem memEnv' ∧
                        guardlessIfCleanQTypDeep qt :=
                    IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e)
                      (res' :=
                        { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv',
                          nextLoc' := nextLoc', nextTag' := nextTag' })
                      hmem hvars (by simpa [typecheck] using hres)
                  have hguard : guardlessIfCleanMem memEnv' := hresult_guard.left
                  cases qt with
                  | mk etyp poison pred =>
                      have hqt_deep : guardlessIfCleanQTypDeep ⟨etyp, poison, pred⟩ :=
                        hresult_guard.right
                      cases hcheck : (etyp != ETyp.int) with
                      | true =>
                          have hcontr := htcRand'
                          simp [typecheckRand, hres, hcheck, bind, Except.bind] at hcontr
                      | false =>
                          have hres_eq := htcRand'
                          simp [typecheckRand, hres, hcheck, bind, pure, Except.bind, Except.pure] at hres_eq
                          cases hres_eq
                          dsimp
                          constructor
                          · exact hguard
                          · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                            · intro _hpoison_clean
                              simp [qtypGuardTag]
                            · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_frand
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.frand e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcFrand : typecheckFrand ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          have hcontr := htcFrand
          simp [typecheckFrand] at hcontr
      | succ fuelInner =>
          have htcFrand' := htcFrand
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcFrand'
              simp [typecheckFrand, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) := by
                    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ (Nat.lt_succ_self _))
                  have hresult_guard :
                      guardlessIfCleanMem memEnv' ∧ guardlessIfCleanQTypDeep qt :=
                    IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e)
                      (res' :=
                        { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv',
                          nextLoc' := nextLoc', nextTag' := nextTag' })
                      hmem hvars (by simpa [typecheck] using hres)
                  have hguard : guardlessIfCleanMem memEnv' := hresult_guard.left
                  cases qt with
                  | mk etyp poison pred =>
                      cases hcheck : (etyp != ETyp.int) with
                      | true =>
                          have hcontr := htcFrand'
                          simp [typecheckFrand, hres, hcheck, bind, Except.bind] at hcontr
                      | false =>
                          let varName := generateFreshVar ctx "limit" 0 fuelInner
                          let limitExpr :=
                            Expr.op
                              (Expr.op (Expr.var varName) Op.gte (Expr.num 0))
                              Op.and
                              (Expr.op (Expr.var varName) Op.lte e)
                          cases hpe : Expr.toPExpr limitExpr with
                          | error err =>
                              have hcontr := htcFrand'
                              simp [typecheckFrand, hres, hcheck, bind, Except.bind,
                                varName, limitExpr, hpe] at hcontr
                          | ok predBody =>
                              have hres_eq := htcFrand'
                              simp [typecheckFrand, hres, hcheck, bind, Except.bind,
                                pure, Except.pure, generateFreshTagRes, varName,
                                limitExpr, hpe] at hres_eq
                              cases hres_eq
                              dsimp
                              constructor
                              · exact hguard
                              · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                                · intro hpoison
                                  exact False.elim ((by decide : true ≠ false) hpoison)
                                · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_printString
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.printString e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcPrintString : typecheckPrintString ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          have hcontr := htcPrintString
          simp [typecheckPrintString] at hcontr
      | succ fuelInner =>
          have htcPrintString' := htcPrintString
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcPrintString'
              simp [typecheckPrintString, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) := by
                    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ (Nat.lt_succ_self _))
                  have hresult_guard :
                      guardlessIfCleanMem memEnv' ∧ guardlessIfCleanQTypDeep qt :=
                    IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e)
                      (res' :=
                        { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv',
                          nextLoc' := nextLoc', nextTag' := nextTag' })
                      hmem hvars (by simpa [typecheck] using hres)
                  have hguard : guardlessIfCleanMem memEnv' := hresult_guard.left
                  cases qt with
                  | mk etyp poison pred =>
                      cases hcheck : (etyp != ETyp.string) with
                      | true =>
                          have hcontr := htcPrintString'
                          simp [typecheckPrintString, hres, hcheck, bind, Except.bind] at hcontr
                      | false =>
                          have hres_eq := htcPrintString'
                          simp [typecheckPrintString, hres, hcheck, bind, Except.bind,
                            pure, Except.pure] at hres_eq
                          cases hres_eq
                          dsimp
                          constructor
                          · exact hguard
                          · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                            · intro _hpoison_clean
                              simp [qtypGuardTag]
                            · simp [nonClosureQTyp]

private lemma guardlessIfClean_invariant_printInt
    (e : Expr)
    (IH :
      ∀ ⦃fuel' : Nat⦄,
        fuel' < fuel →
          ∀ ⦃ctx : TypeContext⦄ ⦃e' : Expr⦄ ⦃res' : TypeResult⦄,
            guardlessIfCleanMem ctx.memEnv →
              guardlessIfCleanVars ctx.varEnv →
                typecheck ctx e' fuel' = .ok res' →
                guardlessIfCleanMem res'.memEnv' ∧ guardlessIfCleanQTypDeep res'.qualType)
    (hmem : guardlessIfCleanMem ctx.memEnv)
    (hvars : guardlessIfCleanVars ctx.varEnv)
    (htc : typecheck ctx (Expr.printInt e) fuel = .ok res) :
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheck, typecheckExpr] at htc
  | succ fuelPred =>
      have htcPrintInt : typecheckPrintInt ctx e fuelPred = .ok res := by
        simpa [typecheck, typecheckExpr] using htc
      cases fuelPred with
      | zero =>
          have hcontr := htcPrintInt
          simp [typecheckPrintInt] at hcontr
      | succ fuelInner =>
          have htcPrintInt' := htcPrintInt
          cases hres : typecheckExpr ctx e fuelInner with
          | error err =>
              have hcontr := htcPrintInt'
              simp [typecheckPrintInt, hres, bind, Except.bind] at hcontr
          | ok result =>
              cases result with
              | mk qt memEnv' tagEnv' nextLoc' nextTag' =>
                  have hfuel :
                      fuelInner < Nat.succ (Nat.succ fuelInner) := by
                    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ (Nat.lt_succ_self _))
                  have hresult_guard :
                      guardlessIfCleanMem memEnv' ∧ guardlessIfCleanQTypDeep qt :=
                    IH (fuel' := fuelInner) hfuel (ctx := ctx) (e' := e)
                      (res' :=
                        { qualType := qt, memEnv' := memEnv', tagEnv' := tagEnv',
                          nextLoc' := nextLoc', nextTag' := nextTag' })
                      hmem hvars (by simpa [typecheck] using hres)
                  have hguard : guardlessIfCleanMem memEnv' := hresult_guard.left
                  cases qt with
                  | mk etyp poison pred =>
                      cases hcheck : (etyp != ETyp.int) with
                      | true =>
                          have hcontr := htcPrintInt'
                          simp [typecheckPrintInt, hres, hcheck, bind, Except.bind] at hcontr
                      | false =>
                          have hres_eq := htcPrintInt'
                          simp [typecheckPrintInt, hres, hcheck, bind, Except.bind,
                            pure, Except.pure] at hres_eq
                          cases hres_eq
                          dsimp
                          constructor
                          · exact hguard
                          · refine guardlessIfCleanQTypDeep.of_nonClosure ?_ ?_
                            · intro _hpoison_clean
                              simp [qtypGuardTag]
                            · simp [nonClosureQTyp]

end GuardlessIfCleanInvariant

/-- The top-level typechecker preserves the guardless invariant on the memory environment
    and produces guardless qualified types. -/
lemma guardlessIfClean_invariant
    (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult) :
    guardlessIfCleanMem ctx.memEnv →
    guardlessIfCleanVars ctx.varEnv →
    typecheck ctx e fuel = .ok res →
    guardlessIfCleanMem res.memEnv' ∧ guardlessIfCleanQTypDeep res.qualType := by
  induction fuel using Nat.strong_induction_on generalizing e res ctx with
  | _ n IH =>
    intros hmem hvars htc
    cases e with
    | unit =>
        exact guardlessIfClean_invariant_unit hmem htc
    | num n =>
        exact guardlessIfClean_invariant_num n hmem htc
    | bool b =>
        exact guardlessIfClean_invariant_bool b hmem htc
    | str s =>
        exact guardlessIfClean_invariant_str s hmem htc
    | var x =>
        exact guardlessIfClean_invariant_var x hmem hvars htc
    | op e₁ opName e₂ =>
        exact guardlessIfClean_invariant_op e₁ e₂ opName IH hmem hvars htc
    | unaryop opName e' =>
        exact guardlessIfClean_invariant_unaryop opName e' IH hmem hvars htc
    | ite e₁ e₂ e₃ =>
        exact guardlessIfClean_invariant_ite e₁ e₂ e₃ IH hmem hvars htc
    | newRef e' =>
        exact guardlessIfClean_invariant_newRef e' IH hmem hvars htc
    | assign e₁ e₂ =>
        exact guardlessIfClean_invariant_assign e₁ e₂ IH hmem hvars htc
    | deref e' =>
        exact guardlessIfClean_invariant_deref e' IH hmem hvars htc
    | seq e₁ e₂ =>
        exact guardlessIfClean_invariant_seq e₁ e₂ IH hmem hvars htc
    | kwhile e₁ e₂ =>
        exact guardlessIfClean_invariant_while e₁ e₂ IH hmem hvars htc
    | vlet x e₁ e₂ =>
        exact guardlessIfClean_invariant_vlet x e₁ e₂ IH hmem hvars htc
    | fn x st₁ body st₂ =>
        exact guardlessIfClean_invariant_fn x st₁ st₂ body hmem hvars htc
    | pfn x st₁ body st₂ =>
        exact guardlessIfClean_invariant_pfn x st₁ st₂ body hmem hvars htc
    | app e₁ e₂ =>
        exact guardlessIfClean_invariant_app e₁ e₂ IH hmem hvars htc
    | rand e' =>
        exact guardlessIfClean_invariant_rand e' IH hmem hvars htc
    | frand e' =>
        exact guardlessIfClean_invariant_frand e' IH hmem hvars htc
    | printString e' =>
        exact guardlessIfClean_invariant_printString e' IH hmem hvars htc
    | printInt e' =>
        exact guardlessIfClean_invariant_printInt e' IH hmem hvars htc
