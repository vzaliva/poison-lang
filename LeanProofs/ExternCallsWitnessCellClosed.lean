import LeanProofs.ExternCallsWitnessCell
import LeanProofs.ExternCallsWitnessClosed

/-!
# A trusted entry for an extern with an effect

`rd` is the extern function of `ExternCallsWitnessCell`:

    extern fn @8 r : (ref int :> clean {}) -> (int :> poisoned { 0, w => w >= 0 }),
      effects: { !r :> (int :> poisoned { 0 }) }

Its return guard and the cell it writes through its argument share the tag
index 0. The implementation writes `n / 2` to the cell holding `n` and
returns 0.

This module gives a trusted entry for `rd`, with call contracts proved from
the premises on extern calls, and applies the top-level theorem to two
programs that call it, with every premise proved.

* The entry. `rd_callSingle` and `rd_callFR` are the call contracts of
  `rdDecl` with the implementation `rdI`, `rd_declSingle` and `rd_declFR`
  the declaration contracts; `rdSpec` collects them with operational safety,
  and `rdReg` is the trusted registry that holds `rd` alone. The two-run
  contract uses the clause of *agreement* for cells (`CallAgrees.cells`) in
  `cell_agree`: a cell that the call writes and that is clean after the call
  holds the same content in the two runs. The typing stores the call's guard
  for the cell only when the target has a single location, the reference is
  clean and the pc is clean; the cell is then clean when the call's tag is
  true. A target with several locations (a weak update), a poisoned
  reference or a poisoned pc leaves the cell poisoned without a predicate,
  which is never clean.
* `cell_closed`: the theorem at `rd (ref x)`, nothing observed, for two runs
  whose calls leave the same content in the cell; `cell_closed_4_5` for the
  runs from `x = 4` and `x = 5`.
* `ReadBack`: the theorem at
  `let c = ref x in let ret = rd c in if ret >= 0 then !c else 0`, which
  reads the cell back under the guard of the returned value. The result is a
  clean `int`, and it is observed. `ReadBack.readBack_case`: *match* holds in
  every run, *agreement* holds for the runs from 4 and 5 and fails for 4 and
  6. `ReadBack.same_return`: two runs whose calls leave the same content in
  the cell return the same value. `ReadBack.run_prog`: the run from `x = n`
  returns `n / 2`, so the runs from 4 and 6 return 2 and 3.

Limits. The cell's guard has no predicate, so the clause of *match* for
cells (`CallMatches.cells`) is not used, and a cell whose guard carries a
predicate has no witness here. The proofs of the entry are specific to the
shape of `rd`: one effect, on the argument, whose guard has the tag of the
return guard.
-/

open Std LeanPoison

namespace ExternCallsWitness

namespace Cell

/-- The declaration of `rd`, as the program relation builds it from `rdD`. -/
def rdDecl : ExternDeclaration :=
  { id := 8, kind := .fn, typ := .ref .int, argName := some "r", retSpec := some readRet,
    effects := [rdEff], preds := collectExternPreds readRet [rdEff], argPoison := false,
    captures := [] }

/-- The implementation of `rd`. -/
def rdI : ExternImpl := .fn rdImpl

example : ExternDeclarationInProgram rdD 8 rdDecl := ExternDeclarationInProgram.externFn

/-- A singleton target realizes its location at the address the variable holds. -/
private theorem realize_singleton {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {x : Name} {qtv : QTyp} {ls : LocSet} {l : Loc} {a : Address}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) (hlk : ctx.varEnv.lookup x = some qtv)
    (hety : qtv.etyp = .ref ls) (hls : ls.toList = [l]) (hρ : ρ.lookup x = some (.loc a)) :
    θ.lookup l = some a := by
  obtain ⟨v, hv, hvt⟩ := hric.2 hlk
  rw [hρ, Option.some.injEq] at hv
  subst hv
  rw [hety] at hvt
  cases hvt with
  | loc hθ hin =>
      rename_i l'
      have hl' : l' ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hin
      rw [hls, List.mem_singleton] at hl'
      subst hl'
      exact hθ

/-- **The written cell agrees.** With a single target location, a clean
    reference and a clean pc, the cell `!r` writes is stored with the call's tag
    `k`; when the regime sets `k` true, the two runs leave the same content in
    it. This is where the cell clause of `CallAgrees` is used. -/
theorem cell_agree {predSat : PredSat} {R : Regime} {entry₀ entry₁ : ExternCallEntry}
    {res : TypeResult} {cf₀ cf₁ : Config} {o₀ o₁ : Value} {θ₀ θ₁ : RealizationMap}
    {qtv : QTyp} {ls : LocSet} {l : Loc} {qt : QTyp} {k : Tag} {a₀ a₁ : Address} {n₀ n₁ : Int}
    (hctx : entry₁.bodyCtx = entry₀.bodyCtx)
    (hlk : entry₀.bodyCtx.varEnv.lookup "r" = some qtv) (hety : qtv.etyp = .ref ls)
    (hls : ls.toList = [l]) (hmem : res.memEnv'.lookup l = some qt)
    (htag : qtypGuardTag qt = some k) (hlog : ∃ a ∈ res.tagLog', a.tag = k)
    (hR : res.regime'.lookup? k = some true) (hRk : R.lookup? k = some true)
    (hint : qt.etyp = .int)
    (hu₀ : entry₀.unifiedEnv.lookup "r" = some (.loc a₀))
    (hu₁ : entry₁.unifiedEnv.lookup "r" = some (.loc a₁))
    (hθ₀ : θ₀.lookup l = some a₀) (hθ₁ : θ₁.lookup l = some a₁)
    (hn₀ : cf₀.memory.lookup a₀ = some n₀) (hn₁ : cf₁.memory.lookup a₁ = some n₁)
    (hag : CallAgrees entry₀ entry₁ [rdEff] res cf₀ cf₁ o₀ o₁) :
    agreeLocUnder predSat R cf₀.memory cf₁.memory θ₀ θ₁ (l, qt) := by
  have hc₀ : EffectCell entry₀ [rdEff] res "r" a₀ qt :=
    EffectCell.mk (List.mem_singleton_self _) rfl hlk hety hls hmem hu₀
  have hc₁ : EffectCell entry₁ [rdEff] res "r" a₁ qt :=
    EffectCell.mk (List.mem_singleton_self _) rfl (by rw [hctx]; exact hlk) hety hls hmem hu₁
  obtain ⟨a, ha, hak⟩ := hlog
  have heq : n₀ = n₁ :=
    hag.cells "r" a₀ a₁ qt n₀ n₁ hc₀ hc₁ hn₀ hn₁ a ha (by rw [hak]; exact htag)
      (by rw [hak]; exact hR)
  refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hθ₀ hθ₁ hn₀ hn₁ ?_
  refine agreeValueUnder.withPred_true_eq k htag hRk (by rw [hint]; rfl) ?_ (by rw [heq])
  rintro ⟨_, h⟩
  rw [hint] at h
  cases h

private theorem join_guardOnly_fresh {k : Tag} {q : Predicate}
    (hq : ∀ k', qtypGuardTag ⟨.int, false, q⟩ = some k' → k' ≠ k) :
    joinPredicates (.guardOnly k) q = .noPred := by
  cases q with
  | noPred => simp [joinPredicates, beqPredicate]
  | guardOnly k2 =>
      have hne : k2 ≠ k := hq k2 (by simp [qtypGuardTag])
      have hne' : (k == k2) = false := by simp [Ne.symm hne]
      simp [joinPredicates, beqPredicate, hne']
  | guardClosure k2 a b c =>
      have hne : k2 ≠ k := hq k2 (by simp [qtypGuardTag])
      have hne' : (k == k2) = false := by simp [Ne.symm hne]
      simp [joinPredicates, beqPredicate, hne']

/-- **No cell of a multi-location target is clean.** A weak update from
    `guardOnly k`, with `k` fresh for the old entries, stores `noPred`. -/
private theorem weak_pred_noPred (env : MemoryTypeEnv) (ls : LocSet) (sp : Poison) (k : Tag)
    (l : Loc) (hmem : l ∈ ls) (qt : QTyp)
    (hfresh : ∀ l' qt' k', env.lookup l' = some qt' → qtypGuardTag qt' = some k' → k' ≠ k)
    (hlookup : (updateLocsetWeak env ls sp (.guardOnly k)).lookup l = some qt) :
    qt.pred = .noPred := by
  have fold_pres : ∀ {β : Type} (xs : List Loc) (init : β) (f : β → Loc → β)
      (P : β → Prop), P init → (∀ acc x, P acc → P (f acc x)) → P (xs.foldl f init) := by
    intro β xs init f P hinit hstep
    induction xs generalizing init with
    | nil => exact hinit
    | cons hd tl ih => simp only [List.foldl]; exact ih (f init hd) (hstep init hd hinit)
  set f : Poison × Predicate → Loc → Poison × Predicate := fun (accP, accPred) l =>
    match env.get? l with
    | some e => (joinPoison accP e.poison, joinPredicates accPred e.pred)
    | none => (accP, Predicate.noPred) with hf
  set joined := LocSet.fold ls (sp, .guardOnly k) f with hjoinedDef
  set finalQt : QTyp := ⟨ETyp.int, joined.1, joined.2⟩ with hfinalDef
  have hmemList : l ∈ ls.toList := (Std.ExtTreeSet.mem_toList).2 hmem
  have hval : (updateLocsetWeak env ls sp (.guardOnly k)).lookup l = some finalQt := by
    unfold updateLocsetWeak
    dsimp only []
    unfold LocSet.fold
    rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
    exact list_fold_updateMemEnv_lookup_eq_of_mem ls.toList env l finalQt hmemList (by simp [finalQt])
  rw [hval, Option.some.injEq] at hlookup
  subst hlookup
  show joined.2 = Predicate.noPred
  rw [hjoinedDef]
  unfold LocSet.fold
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList]
  cases hls : ls.toList with
  | nil => rw [hls] at hmemList; cases hmemList
  | cons hd tl =>
      simp only [List.foldl]
      refine fold_pres tl _ f (fun p => p.2 = Predicate.noPred) ?_ ?_
      · show (f (sp, .guardOnly k) hd).2 = .noPred
        rw [hf]
        dsimp only []
        cases he : env.get? hd with
        | none => rfl
        | some e =>
            show joinPredicates (.guardOnly k) e.pred = .noPred
            refine join_guardOnly_fresh fun k' hk' => hfresh hd ⟨.int, e.poison, e.pred⟩ k' ?_ ?_
            · unfold MemoryTypeEnv.lookup; rw [he]; rfl
            · simpa [qtypGuardTag] using hk'
      · rintro ⟨accP, accPred⟩ x hacc
        have h : accPred = Predicate.noPred := hacc
        subst h
        rw [hf]
        dsimp only []
        cases env.get? x with
        | none => rfl
        | some e => simp only [joinPredicates]; split <;> rfl

/-! ## The runtime run and the tag allocation -/

/-- What a run of `rd` does: the argument is a reference to an address `a`
    holding `n`; the call writes `n / 2` there and returns 0. -/
private theorem rd_callRun_output {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hrun : ExternCallBoundaryRun rdDecl rdI entry res cf o) :
    ∃ (a : Address) (n : Int),
      entry.argName = "r" ∧
      entry.argValue = .loc a ∧
      entry.unifiedEnv.lookup "r" = some (.loc a) ∧
      entry.callConfig.memory.lookup a = some n ∧
      o = .num 0 ∧
      cf.memory = entry.callConfig.memory.update a (n / 2) ∧
      cf.nextAddr = entry.callConfig.nextAddr ∧
      cf = { entry.callConfig with memory := cf.memory, nextAddr := cf.nextAddr } := by
  cases hrun with
  | pfn hfacts => have h := hfacts.kind_pfn; simp [rdDecl] at h
  | fn hfacts =>
      have hname : entry.argName = "r" := by
        have h := hfacts.argName; simp only [rdDecl] at h; exact (Option.some.inj h).symm
      rcases hfacts.impl_success with ⟨implFn, retSpec, vRaw, himpl, hretSpec, _hm, hrunImpl, hval⟩
      simp only [rdI, ExternImpl.fn.injEq] at himpl
      subst himpl
      have hret : retSpec = readRet := by
        simp only [rdDecl] at hretSpec; exact (Option.some.inj hretSpec).symm
      subst hret
      obtain ⟨a, harg⟩ : ∃ a, entry.argValue = .loc a := by
        cases h : entry.argValue with
        | loc a => exact ⟨a, rfl⟩
        | _ => rw [h] at hrunImpl; simp [rdImpl] at hrunImpl
      rw [harg] at hrunImpl
      cases hn : entry.callConfig.memory.lookup a with
      | none => simp [rdImpl, hn] at hrunImpl
      | some n =>
          simp only [rdImpl, hn, Except.ok.injEq, Prod.mk.injEq] at hrunImpl
          obtain ⟨hv, hmem, hnext⟩ := hrunImpl
          subst hv
          have ho : o = .num 0 := by
            simp [readRet, validateExternReturn, valueMatchesTyp] at hval; exact hval.symm
          refine ⟨a, n, hname, harg, ?_, hn, ho, hmem.symm, hnext.symm, hfacts.output_config⟩
          rw [hfacts.unifiedEnv_eq, hname, harg]
          simp [VarEnv.update, VarEnv.lookup]

/-- The tag mapping of a call of `rd` at cursor `c`: index 0 gets `c`. -/
private def rdMap (c : Tag) : TagMapping := (∅ : TagMapping).insert ⟨0⟩ c

/-- The call allocates one tag, at the cursor, for the shared index 0. -/
private theorem rd_alloc (c : Tag) :
    collectAndAllocExternTags (collectExternPreds readRet [rdEff]) c = .ok (rdMap c, c + 1) := by
  rfl

/-- The tag of the call is logged. -/
private theorem rd_log (env : VarTypeEnv) (c : Tag) :
    ∃ a ∈ externTagLog (collectExternPreds readRet [rdEff]) env (rdMap c), a.tag = c := by
  simp [externTagLog, collectExternPreds, readRet, geGuard, rdEff, rdMap]
  exact ⟨_, rfl, rfl⟩

/-- How the typechecker types a call of `rd`, in terms of the body context. -/
private theorem rd_call_shape {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call rdDecl typedExpr entry res) :
    ∃ (fuel' : Nat) (resolvedPred : Predicate),
      applyExternEffect rdEff entry.bodyCtx.varEnv (rdMap entry.bodyCtx.nextTag) entry.bodyCtx.pc
        entry.bodyCtx.memEnv = .ok res.memEnv' ∧
      resolveSyntaxPred geGuard entry.bodyCtx.varEnv (rdMap entry.bodyCtx.nextTag) =
        .ok resolvedPred ∧
      res.nextTag' = entry.bodyCtx.nextTag + 1 ∧
      res.nextLoc' = entry.bodyCtx.nextLoc ∧
      res.declared' = entry.bodyCtx.declaredExternRefs ∧
      res.regime' = applyExternRegimePolicy
        (invalidateRegimeDepsEffect entry.bodyCtx.regime entry.bodyCtx.tagEnv
          (effectTargetLocs [rdEff] entry.bodyCtx.varEnv))
        8 entry.bodyCtx.externRegime (rdMap entry.bodyCtx.nextTag) ∧
      res.tagEnv' = installReturnGuard
        (invalidateTagDeps entry.bodyCtx.tagEnv (effectTargetLocs [rdEff] entry.bodyCtx.varEnv))
        resolvedPred res.regime' fuel' ∧
      res.tagLog' = externTagLog (collectExternPreds readRet [rdEff]) entry.bodyCtx.varEnv
        (rdMap entry.bodyCtx.nextTag) ∧
      res.qualType.etyp = .int ∧ res.qualType.poison = true ∧
      (res.qualType.pred = .noPred ∨ res.qualType.pred = resolvedPred) := by
  cases htyped with
  | pfnExternMember _ hkind => simp [rdDecl] at hkind
  | fnExternMember hid _hkind _htyp harg hret heff hcap _hpin hbody happly =>
    rename_i ctx bodyState cursor fuel st1 st2 p p1 argEtyp argPoison argPred
      id x y argTyp argPoisonAst argPredAst declaredArgQt retSpec effects captures tenv
    have hid' : id = 8 := by simpa [rdDecl] using hid.symm
    subst hid'
    have hcap' : captures = [] := by simpa [rdDecl] using hcap.symm
    subst hcap'
    have heff' : effects = [rdEff] := by simpa [rdDecl] using heff.symm
    subst heff'
    have hx : x = "r" := by
      have h : some x = some "r" := by simpa [rdDecl] using harg.symm
      exact Option.some.inj h
    subst hx
    have hrs : retSpec = readRet := by
      have h : some retSpec = some readRet := by simpa [rdDecl] using hret.symm
      exact Option.some.inj h
    subst hrs
    rw [hbody]
    cases fuel with
    | zero => simp [applyFnTClosureAtCursor] at happly
    | succ fuel' =>
        simp only [applyFnTClosureAtCursor, bind, Except.bind] at happly
        split at happly
        · simp at happly
        · rw [rd_alloc] at happly
          simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at happly
          cases heffr : applyExternEffect rdEff
              ((VarTypeEnv.ofCaptured tenv).update "r"
                { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred })
              (rdMap cursor.1) (joinPoison p (joinPoison p1 ctx.pc)) bodyState.memEnv' with
          | error e => simp [heffr] at happly
          | ok memEnv' =>
              simp only [heffr, readRet] at happly
              cases hres : resolveSyntaxPred geGuard
                  ((VarTypeEnv.ofCaptured tenv).update "r"
                    { etyp := argEtyp, poison := joinPoison ctx.pc argPoison, pred := argPred })
                  (rdMap cursor.1) with
              | error e => simp [hres] at happly
              | ok rp =>
                  simp only [hres] at happly
                  cases hrq : returnSpecToQTyp Typ.int true rp cursor.2 with
                  | error e => simp [hrq] at happly
                  | ok rq =>
                      simp only [hrq] at happly
                      split at happly
                      · exact nomatch happly
                      simp only [Except.ok.injEq] at happly
                      subst happly
                      have hrq' : rq = (⟨ETyp.int, true, rp⟩, cursor.2) := by
                        simp [returnSpecToQTyp, bind, Except.bind, pure, Except.pure] at hrq
                        exact hrq.symm
                      subst hrq'
                      refine ⟨fuel', rp, rfl, rfl, rfl, rfl, rfl, rfl,
                        installEffectGuards_eq_self _ _ _ _ _ _ _ (by simp [rdEff]), rfl, ?_, ?_, ?_⟩
                      · simp only [normalizeAppResultByProvenance]; split <;> rfl
                      · simp only [normalizeAppResultByProvenance]; split <;> simp [joinPoison]
                      · simp only [normalizeAppResultByProvenance]; split
                        · exact Or.inl rfl
                        · exact Or.inr rfl


/-- The return guard resolves to a closure on the call's tag. -/
private theorem rd_resolve {env : VarTypeEnv} {c : Tag} {rp : Predicate}
    (h : resolveSyntaxPred geGuard env (rdMap c) = .ok rp) :
    ∃ arg body cap, rp = .guardClosure c arg body cap := by
  have hget : (rdMap c).get? ⟨0⟩ = some c := rfl
  simp only [geGuard, resolveSyntaxPred, hget, bind, Except.bind, pure, Except.pure] at h
  cases hp : ((Expr.var "w").op Op.gte (Expr.num 0)).toPExpr with
  | error e => simp [hp] at h
  | ok pb =>
      simp only [hp, Except.ok.injEq] at h
      exact ⟨_, _, _, h.symm⟩

/-- The policy step of a call of `rd` touches only the call's tag. -/
private theorem rdPolicy_lookup (R : Regime) (pol : ExternId → Tag → Option Bool) (c k : Tag) :
    (applyExternRegimePolicy R 8 pol (rdMap c)).lookup? k =
      if k = c then (match R.lookup? c with | some b => some b | none => pol 8 c)
      else R.lookup? k := by
  have hR : applyExternRegimePolicy R 8 pol (rdMap c) =
      (match pol 8 c with
       | some b => match R.lookup? c with
                   | none => R.insert c b
                   | some _ => R
       | none => R) := rfl
  rw [hR]
  by_cases hk : k = c
  · subst hk
    simp only [↓reduceIte]
    cases hp : pol 8 k with
    | none => cases R.lookup? k <;> simp
    | some b =>
        cases hR' : R.lookup? k with
        | none => simp [Regime.lookup?, ExtTreeMap.get?_eq_getElem?]
        | some b' => simp [hR']
  · simp only [hk, ↓reduceIte]
    cases pol 8 c with
    | none => rfl
    | some b =>
        cases R.lookup? c with
        | none =>
            have hcmp : compare c k ≠ .eq := by
              intro h; exact hk ((Nat.compare_eq_eq).1 h).symm
            simp [Regime.lookup?, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, hcmp]
        | some _ => rfl

/-! ## The effect and the written cells -/

/-- The cells written by a call of `rd`: the target `r` of the body context
    is a reference to `ls`; the written cells are poisoned, with the guard of
    the call's tag when the target and the pc are clean, without predicate
    otherwise. -/
private theorem rd_effect_shape {ctx : TypeContext} {c : Tag} {memEnv' : MemoryTypeEnv}
    (h : applyExternEffect rdEff ctx.varEnv (rdMap c) ctx.pc ctx.memEnv = .ok memEnv') :
    ∃ qtv ls, ctx.varEnv.lookup "r" = some qtv ∧ qtv.etyp = .ref ls ∧
      memEnv' = (match ls.toList with
        | [l] => updateMemEnv ctx.memEnv l
            ⟨.int, true, if qtv.poison || ctx.pc then .noPred else .guardOnly c⟩
        | _ => updateLocsetWeak ctx.memEnv ls true
            (if qtv.poison || ctx.pc then .noPred else .guardOnly c)) := by
  unfold applyExternEffect at h
  simp only [rdEff, bind, Except.bind] at h
  cases hlk : ctx.varEnv.lookup "r" with
  | none => simp only [hlk] at h; simp at h
  | some qtv =>
      simp only [hlk] at h
      cases hety : qtv.etyp with
      | ref ls =>
          simp only [hety] at h
          have hres : resolveSyntaxPred (.guardOnly ⟨0⟩) ctx.varEnv (rdMap c) = .ok (.guardOnly c) :=
            rfl
          simp only [hres, pure, Except.pure, Except.ok.injEq, effectSpecToQTyp] at h
          refine ⟨qtv, ls, rfl, hety, ?_⟩
          rw [← h]
          have hp : joinPoison ctx.pc (joinPoison qtv.poison true) = true := by
            simp [joinPoison]
          rw [hp]
          generalize ExtTreeSet.toList ls = xs
          rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
      | _ => simp only [hety] at h; simp at h

/-- The cells of a target are the cells the effect writes. -/
private theorem rd_targetLocs {env : VarTypeEnv} {qtv : QTyp} {ls : LocSet}
    (hlk : env.lookup "r" = some qtv) (hety : qtv.etyp = .ref ls) (l : Loc) :
    (effectTargetLocs [rdEff] env).contains l = ls.contains l := by
  simp only [effectTargetLocs, rdEff, List.foldl, hlk, hety, LocSet.union]
  simp [ExtTreeSet.contains_union]

/-- What a written cell holds. -/
private theorem rd_written {ctx : TypeContext} {qtv : QTyp} {ls : LocSet} {memEnv' : MemoryTypeEnv}
    (htb : TagBoundedCtx ctx)
    (hmem : memEnv' = (match ls.toList with
        | [l] => updateMemEnv ctx.memEnv l
            ⟨.int, true, if qtv.poison || ctx.pc then .noPred else .guardOnly ctx.nextTag⟩
        | _ => updateLocsetWeak ctx.memEnv ls true
            (if qtv.poison || ctx.pc then .noPred else .guardOnly ctx.nextTag)))
    (l : Loc) (hin : l ∈ ls) (qt : QTyp) (hlk : memEnv'.lookup l = some qt) :
    qt.poison = true ∧
      (qt.pred = .noPred ∨
        (ls.toList = [l] ∧ qtv.poison = false ∧ ctx.pc = false ∧
          qt.pred = .guardOnly ctx.nextTag)) := by
  subst hmem
  have hprops := assign_memEnv_formula_lookup_mem_props ctx.memEnv ls true _ l hin qt hlk
  refine ⟨hprops.1 rfl, ?_⟩
  cases hcond : (qtv.poison || ctx.pc) with
  | true => exact Or.inl (hprops.2 (by simp [hcond]))
  | false =>
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hlk
      have hqp : qtv.poison = false := by simp_all
      have hpc : ctx.pc = false := by simp_all
      have hmemList : l ∈ ls.toList := (ExtTreeSet.mem_toList).2 hin
      cases hls : ls.toList with
      | nil => rw [hls] at hmemList; cases hmemList
      | cons l0 rest =>
          cases rest with
          | nil =>
              rw [hls, List.mem_singleton] at hmemList
              subst hmemList
              simp only [hls] at hlk
              unfold updateMemEnv MemoryTypeEnv.lookup at hlk
              simp [ExtTreeMap.get?_eq_getElem?] at hlk
              exact Or.inr ⟨rfl, hqp, hpc, by rw [← hlk]⟩
          | cons l1 rest' =>
              simp only [hls] at hlk
              refine Or.inl (weak_pred_noPred ctx.memEnv ls true ctx.nextTag l hin qt ?_ hlk)
              intro l' qt' k' hl' hk'
              exact Nat.ne_of_lt (TagBoundedCtx_memEnv_guardTag_lt htb hl' hk')

/-- The return guard enters the tag environment only at the call's tag. -/
private theorem rd_installReturnGuard_cases {env : TagEnv} {c : Tag} {arg : Name} {body : PExpr}
    {cap : CapturedVarEnv} {R : Regime} {fuel : Nat} {k : Tag} {tv : TagVal}
    (h : (installReturnGuard env (.guardClosure c arg body cap) R fuel).get? k = some tv) :
    env.get? k = some tv ∨ (k = c ∧ R.lookup? c = some tv.value) := by
  unfold installReturnGuard at h
  cases hR : R.lookup? c with
  | none => simp only [hR] at h; exact Or.inl h
  | some b =>
      simp only [hR] at h
      cases hd : extractDepsFromPred (.guardClosure c arg body cap) fuel with
      | error e => simp only [hd] at h; exact Or.inl h
      | ok deps =>
          simp only [hd] at h
          by_cases hk : k = c
          · subst hk
            simp [ExtTreeMap.get?_eq_getElem?] at h
            subst h
            exact Or.inr ⟨rfl, rfl⟩
          · have hcmp : compare c k ≠ .eq := by
              intro h'; exact hk ((Nat.compare_eq_eq).1 h').symm
            left
            simpa [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, hcmp] using h

/-! ## What the typing of a call gives, in terms of the body context -/

/-- The facts the two contracts use about the typing of a call of `rd`. -/
private structure RdCallFacts (ctx : TypeContext) (res : TypeResult) : Prop where
  etyp : res.qualType.etyp = .int
  poison : res.qualType.poison = true
  guard : ∀ k, qtypGuardTag res.qualType = some k → k = ctx.nextTag
  logged : ∃ a ∈ res.tagLog', a.tag = ctx.nextTag
  nextTag : res.nextTag' = ctx.nextTag + 1
  nextLoc : res.nextLoc' = ctx.nextLoc
  declared : res.declared' = ctx.declaredExternRefs
  regime : ∀ k, k ≠ ctx.nextTag → res.regime'.lookup? k =
    (invalidateRegimeDepsEffect ctx.regime ctx.tagEnv (effectTargetLocs [rdEff] ctx.varEnv)).lookup? k
  tagEnv_cases : ∀ k tv, res.tagEnv'.get? k = some tv →
    (invalidateTagDeps ctx.tagEnv (effectTargetLocs [rdEff] ctx.varEnv)).get? k = some tv ∨
      (k = ctx.nextTag ∧ res.regime'.lookup? k = some tv.value)
  target : ∃ qtv ls, ctx.varEnv.lookup "r" = some qtv ∧ qtv.etyp = .ref ls ∧
    res.memEnv' = (match ls.toList with
        | [l] => updateMemEnv ctx.memEnv l
            ⟨.int, true, if qtv.poison || ctx.pc then .noPred else .guardOnly ctx.nextTag⟩
        | _ => updateLocsetWeak ctx.memEnv ls true
            (if qtv.poison || ctx.pc then .noPred else .guardOnly ctx.nextTag))
  tagMeaning : ∀ tm, TagMeaningBounded tm ctx.nextTag →
    ∃ tm', tm ⊑ tm' ∧ TagMeaningBounded tm' res.nextTag' ∧
      QTypRespectsTagMeaning tm' res.qualType ∧ WithinLog tm res.tagLog' tm'

private theorem rd_facts {typedExpr : Expr} {entry : ExternCallEntry} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Call rdDecl typedExpr entry res) :
    RdCallFacts entry.bodyCtx res := by
  obtain ⟨_fuel', rp, heff, hres, hnt, hnl, hdecl, hreg, htag, hlog, hety, hpois, hpred⟩ :=
    rd_call_shape htyped
  obtain ⟨arg, body, cap, hrp⟩ := rd_resolve hres
  obtain ⟨qtv, ls, hlk, hqety, hmemEq⟩ := rd_effect_shape heff
  refine ⟨hety, hpois, ?_, ?_, hnt, hnl, hdecl, ?_, ?_, ⟨qtv, ls, hlk, hqety, hmemEq⟩, ?_⟩
  · intro k hk
    rcases hpred with h | h
    · simp [qtypGuardTag, h] at hk
    · simp only [qtypGuardTag, h, hrp, Option.some.injEq] at hk
      exact hk.symm
  · rw [hlog]; exact rd_log _ _
  · intro k hk
    rw [hreg, rdPolicy_lookup]
    simp [hk]
  · intro k tv h
    rw [htag, hrp] at h
    rcases rd_installReturnGuard_cases h with h' | ⟨hkc, hR⟩
    · exact Or.inl h'
    · subst hkc; exact Or.inr ⟨rfl, hR⟩
  · intro tm hbnd
    obtain ⟨tm', hext⟩ := ExternBatchTagMeaningExtension.canonical_general tm
      (collectExternPreds readRet [rdEff]) entry.bodyCtx.varEnv (rdMap entry.bodyCtx.nextTag)
      entry.bodyCtx.nextTag (entry.bodyCtx.nextTag + 1) hbnd (rd_alloc _)
    refine ⟨tm', hext.extends_tm, ?_, ?_, ?_⟩
    · rw [hnt]; exact hext.bounded
    · have hpr : PredRespectsTagMeaning tm' rp :=
        resolveSyntaxPred_respectsTagMeaning tm' geGuard _ _ _ rp hext.2.2.1
          (by simp [collectExternPreds, readRet]) hres
      intro qt' k dsc hin hdesc
      have hq := QTypInQTyp_eq_of_nonFunctionTarget hin (by rw [hety]; rfl)
      subst hq
      have hp := qtypGuardDesc?_eq_some_pred_guardClosure hdesc
      rcases hpred with h | h
      · rw [h] at hp; cases hp
      · rw [h] at hp
        rw [hpr k dsc.argName dsc.body dsc.capEnv hp]
    · rw [hlog]; exact hext.2.2.2.2

namespace RdCallFacts

variable {ctx : TypeContext} {res : TypeResult}

private theorem monotoneExt (hf : RdCallFacts ctx res) :
    Regime.monotoneStepExt ctx.regime res.regime' (fun k => ctx.nextTag ≤ k) := by
  refine ⟨fun k b hknew hk => ?_, fun k hk => ?_⟩
  · have hne : k ≠ ctx.nextTag := fun h => hknew (h ▸ Nat.le_refl _)
    rw [hf.regime k hne]
    exact (invalidateRegimeDepsEffect_monotone _ _ _).1 k b hk
  · by_cases hkc : k = ctx.nextTag
    · right; rw [hkc]
    · left
      rw [hf.regime k hkc] at hk
      exact (invalidateRegimeDepsEffect_monotone _ _ _).2 k hk

private theorem guard_mem (hf : RdCallFacts ctx res) :
    ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k := by
  intro k hk
  rw [hf.guard k hk]
  exact hf.logged

private theorem notfun (hf : RdCallFacts ctx res) : res.qualType.etyp.isFunctionType = false := by
  rw [hf.etyp]; rfl

private theorem notref (hf : RdCallFacts ctx res) : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
  rw [hf.etyp]; rintro ⟨_, h⟩; cases h

private theorem regimeConsistent (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx)
    (hreg : regimeConsistentWithCtx ctx) : regimeConsistentWithCtx (ctxAfter ctx res) := by
  intro k deps h
  rcases hf.tagEnv_cases k _ h with h' | ⟨_, hr⟩
  · have hold := invalidateTagDeps_get?_some_imp _ _ k _ h'
    have hlt : k < ctx.nextTag := htb.1 k (by rw [hold]; exact Option.some_ne_none _)
    show res.regime'.lookup? k = some true
    rw [hf.regime k (Nat.ne_of_lt hlt)]
    exact invalidateRegimeDepsEffect_lookup_preserve_of_survive _ _ _ k true
      (by rw [h']; exact Option.some_ne_none _) (hreg k deps hold)
  · simpa [ctxAfter] using hr

/-- The written cells, the unwritten cells, and the cells of the target. -/
private theorem cells (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx) :
    ∃ qtv ls, ctx.varEnv.lookup "r" = some qtv ∧ qtv.etyp = .ref ls ∧
      (∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
        qt.poison = true ∧
          (qt.pred = .noPred ∨
            (ls.toList = [l] ∧ qtv.poison = false ∧ ctx.pc = false ∧
              qt.pred = .guardOnly ctx.nextTag))) ∧
      (∀ l, l ∉ ls → res.memEnv'.lookup l = ctx.memEnv.lookup l) ∧
      (∀ l, res.memEnv'.contains l = true → ctx.memEnv.contains l = true ∨ l ∈ ls) ∧
      (∀ l, ctx.memEnv.contains l = true → res.memEnv'.contains l = true) := by
  obtain ⟨qtv, ls, hlk, hety, hmem⟩ := hf.target
  refine ⟨qtv, ls, hlk, hety, fun l qt hin hl => rd_written htb hmem l hin qt hl, ?_, ?_, ?_⟩
  · intro l hnin
    rw [hmem]
    exact assign_memEnv_formula_lookup_eq_of_not_mem ctx.memEnv ls _ _ l hnin
  · intro l hc
    rw [hmem] at hc
    exact assign_memEnv_formula_contains_eq_or_mem ctx.memEnv ls _ _ l hc
  · intro l hc
    rw [hmem]
    exact assign_memEnv_formula_contains_of_contains ctx.memEnv ls _ _ l hc

private theorem tagBounded (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx) :
    TagBoundedCtx (ctxAfter ctx res) := by
  obtain ⟨_, ls, _, _, hwr, hunw, _, _⟩ := hf.cells htb
  obtain ⟨hte, ⟨hpv, hpm⟩, hcl⟩ := htb
  have hle : ctx.nextTag ≤ res.nextTag' := by rw [hf.nextTag]; exact Nat.le_succ _
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show tagEnvBounded res.tagEnv' res.nextTag'
    intro k hk
    cases h : res.tagEnv'.get? k with
    | none => exact absurd h hk
    | some tv =>
        rcases hf.tagEnv_cases k tv h with h' | ⟨hkc, _⟩
        · have hold := invalidateTagDeps_get?_some_imp _ _ k _ h'
          exact Nat.lt_of_lt_of_le (hte k (by rw [hold]; exact Option.some_ne_none _)) hle
        · rw [hkc, hf.nextTag]; exact Nat.lt_succ_self _
  · exact predTagsBoundedInVarEnv_mono hpv hle
  · show predTagsBoundedInMemEnv res.memEnv' res.nextTag'
    intro l qt hl
    by_cases hin : l ∈ ls
    · rcases (hwr l qt hin hl).2 with hp | ⟨_, _, _, hp⟩
      · simp only [qtypPredTagBounded, hp]
        trivial
      · simp only [qtypPredTagBounded, hp, hf.nextTag]
        exact Nat.lt_succ_self _
    · rw [hunw l hin] at hl
      exact predTagsBoundedInMemEnv_mono hpm hle l qt hl
  · exact varEnvClosuresCapturedBounded_mono hcl hle

private theorem wfCtx (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx) (hwf : wfTypeContext ctx) :
    wfTypeContext (ctxAfter ctx res) := by
  obtain ⟨qtv, ls, hlk, hety, _, _, hcont, _⟩ := hf.cells htb
  refine ⟨?_, ?_, ?_⟩
  · intro l hc
    show l < res.nextLoc'
    rw [hf.nextLoc]
    rcases hcont l hc with hold | hin
    · exact hwf.1 l hold
    · have hb := hwf.2.1 "r" qtv hlk
      rw [hety] at hb
      exact hb l (by simpa using hin)
  · simp only [ctxAfter]; rw [hf.nextLoc]; exact hwf.2.1
  · simp only [ctxAfter]; rw [hf.nextLoc]; exact hwf.2.2

/-- Move 1: the regime changes, the context and the memory stay. -/
private theorem consistent_regime (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx)
    {predSat : PredSat} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hcons : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    consistentWithRegime predSat res.regime' ctx μ ρ θ :=
  consistentWithRegimeMasked_unmask (masked := fun _ => False) (fun _ h => h.elim)
    (consistentWithRegimeMasked_monotoneExt (fun _ => False) predSat ctx.regime res.regime' ctx
      μ ρ θ hf.monotoneExt (fun _ hk => hk) htb (consistentWithRegime_to_masked hcons))

/-- Move 1 for agreement. -/
private theorem agree_regime (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx)
    {predSat : PredSat} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hagree : agreeOnClean predSat ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat res.regime' ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  refine ⟨fun l qt hl hclean' => ?_, fun x qt hx hclean' => ?_⟩
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hf.monotoneExt (fun _ hk => hk)
        (TagBoundedCtx_memEnv_predTagBounded htb hl) hclean'
    cases hagree.1 l qt hl hclean0 with
    | agree_values _ _ a₀ a₁ n₀ n₁ h0 h1 h2 h3 hv =>
        refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ h0 h1 h2 h3 ?_
        have hb : etypClosuresFullBounded qt.etyp ctx.nextTag := by
          rw [memEnv_lookup_etyp_int ctx.memEnv l qt hl]; trivial
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hf.monotoneExt (fun _ hk => hk) hb
          hclean' hv
    | both_unrealized _ _ h0 h1 => exact agreeLocUnder.both_unrealized l qt h0 h1
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hf.monotoneExt (fun _ hk => hk)
        (TagBoundedCtx_varEnv_predTagBounded htb hx) hclean'
    cases hagree.2 x qt hx hclean0 with
    | agree_values _ _ v₀ v₁ h0 h1 hv =>
        refine agreeVarUnder.agree_values x qt v₀ v₁ h0 h1 ?_
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hf.monotoneExt (fun _ hk => hk)
          (TagBoundedCtx_varEnv_etypClosures htb hx) hclean' hv
    | both_none _ _ h0 h1 => exact agreeVarUnder.both_none x qt h0 h1

end RdCallFacts

/-- Move 2: the memory is written at one address and the memory types of the
    written cells change; the regime stays. -/
private theorem consistent_write {predSat : PredSat} {tm : TagMeaning} {R : Regime}
    {ctx ctx' : TypeContext}
    {μ μ' : Memory} {ρ : VarEnv} {θ : RealizationMap} {ls : LocSet} {a : Address}
    (hvar : ctx'.varEnv = ctx.varEnv)
    (hwritten : ∀ l qt, l ∈ ls → ctx'.memEnv.lookup l = some qt →
      qt.pred = .noPred ∨ ∃ k, qt.pred = .guardOnly k)
    (hunw : ∀ l, l ∉ ls → ctx'.memEnv.lookup l = ctx.memEnv.lookup l)
    (hne : ∀ l a', l ∉ ls → θ.lookup l = some a' → a' ≠ a)
    (hμ : ∀ a', a' ≠ a → μ'.lookup a' = μ.lookup a')
    (hS : PredSatStable predSat tm R θ θ μ μ')
    (hwfTm : wfTagMeaningCtx tm ctx)
    (hcons : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R ctx' μ' ρ θ := by
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hkR
    by_cases hin : l ∈ ls
    · rcases hwritten l qt hin hlookup with hp | ⟨k', hp⟩
      · simp [qtypGuardTag, hp] at hguard
      · exact locsRegime.guardOnly_ok (l, qt) k' hp
    · rw [hunw l hin] at hlookup
      cases hcons.1 l qt k hlookup hguard hkR with
      | noPred_ok hpn => exact locsRegime.noPred_ok (l, qt) hpn
      | guardOnly_ok k' hgo => exact locsRegime.guardOnly_ok (l, qt) k' hgo
      | withPred_ok k' an pb ve a' n' b' hclos hregk hreal hmem hconsist =>
          refine locsRegime.withPred_ok (l, qt) k' an pb ve a' n' b' hclos hregk hreal ?_ ?_
          · rw [hμ a' (hne l a' hin hreal)]; exact hmem
          · have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
            have hc := qtypPredHolds_of_stable (v := Value.num n') hS hclos'
              (QTypRespectsTagMeaning.desc
                (wfTagMeaningCtx_mem_lookup_qtyp tm _ l qt hwfTm hlookup) hclos')
              (by simp [hregk])
            exact ⟨fun hb => hc.1 (hconsist.1 hb), fun hb hh => (hconsist.2 hb) (hc.2 hh)⟩
  · intro x qt k hlookup hguard hkR
    rw [hvar] at hlookup
    cases hcons.2.1 x qt k hlookup hguard hkR with
    | noPred_ok hpn => exact varsRegime.noPred_ok (x, qt) hpn
    | guardOnly_ok k' hgo => exact varsRegime.guardOnly_ok (x, qt) k' hgo
    | withPred_ok k' an pb ve v b' hclos hregk hvar' hconsist =>
        have hclos' : qt.pred = Predicate.guardClosure k' an pb ve := hclos
        have hc := qtypPredHolds_of_stable (v := v) hS hclos'
          (QTypRespectsTagMeaning.desc
            (wfTagMeaningCtx_var_lookup_qtyp tm _ x qt hwfTm hlookup) hclos')
          (by simp [hregk])
        exact varsRegime.withPred_ok (x, qt) k' an pb ve v b' hclos hregk hvar'
          ⟨fun hb => hc.1 (hconsist.1 hb), fun hb hh => (hconsist.2 hb) (hc.2 hh)⟩
  · intro x qt v hlookup hv
    rw [hvar] at hlookup
    exact closureCapturedVarsRegime_transport_μ hS
      (wfTagMeaningCtx_var_lookup_qtyp tm _ x qt hwfTm hlookup) (hcons.2.2 x qt v hlookup hv)

/-- Move 2 for agreement: a written cell is left to `hcell`. -/
private theorem agree_write {predSat : PredSat} {tm : TagMeaning} {R : Regime}
    {ctx ctx' : TypeContext}
    {μ₀ μ₀' μ₁ μ₁' : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap} {ls : LocSet}
    {a₀ a₁ : Address}
    (hvar : ctx'.varEnv = ctx.varEnv)
    (hunw : ∀ l, l ∉ ls → ctx'.memEnv.lookup l = ctx.memEnv.lookup l)
    (hne₀ : ∀ l a', l ∉ ls → θ₀.lookup l = some a' → a' ≠ a₀)
    (hne₁ : ∀ l a', l ∉ ls → θ₁.lookup l = some a' → a' ≠ a₁)
    (hμ₀ : ∀ a', a' ≠ a₀ → μ₀'.lookup a' = μ₀.lookup a')
    (hμ₁ : ∀ a', a' ≠ a₁ → μ₁'.lookup a' = μ₁.lookup a')
    (hS₀ : PredSatStable predSat tm R θ₀ θ₀ μ₀ μ₀')
    (hS₁ : PredSatStable predSat tm R θ₁ θ₁ μ₁ μ₁')
    (hwfTm : wfTagMeaningCtx tm ctx)
    (hcell : ∀ l qt, l ∈ ls → ctx'.memEnv.lookup l = some qt → qtypCleanUnder R qt →
      agreeLocUnder predSat R μ₀' μ₁' θ₀ θ₁ (l, qt))
    (hagree : agreeOnClean predSat R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat R ctx' μ₀' ρ₀ θ₀ μ₁' ρ₁ θ₁ := by
  refine ⟨fun l qt hlookup hclean => ?_, fun x qt hlookup hclean => ?_⟩
  · by_cases hin : l ∈ ls
    · exact hcell l qt hin hlookup hclean
    · rw [hunw l hin] at hlookup
      cases hagree.1 l qt hlookup hclean with
      | agree_values _ _ b₀ b₁ n₀ n₁ h0 h1 h2 h3 hv =>
          refine agreeLocUnder.agree_values l qt b₀ b₁ n₀ n₁ h0 h1 ?_ ?_ ?_
          · rw [hμ₀ b₀ (hne₀ l b₀ hin h0)]; exact h2
          · rw [hμ₁ b₁ (hne₁ l b₁ hin h1)]; exact h3
          · exact agreeValueUnder_clean_extends_transport_mem hS₀ hS₁
              (wfTagMeaningCtx_mem_lookup_qtyp tm _ l qt hwfTm hlookup) hclean
              (fun _ _ h => h) (fun _ _ h => h) hv
      | both_unrealized _ _ h0 h1 => exact agreeLocUnder.both_unrealized l qt h0 h1
  · rw [hvar] at hlookup
    cases hagree.2 x qt hlookup hclean with
    | agree_values _ _ v₀ v₁ h0 h1 hv =>
        exact agreeVarUnder.agree_values x qt v₀ v₁ h0 h1
          (agreeValueUnder_clean_extends_transport_mem hS₀ hS₁
            (wfTagMeaningCtx_var_lookup_qtyp tm _ x qt hwfTm hlookup) hclean
            (fun _ _ h => h) (fun _ _ h => h) hv)
    | both_none _ _ h0 h1 => exact agreeVarUnder.both_none x qt h0 h1

namespace RdCallFacts

variable {ctx : TypeContext} {res : TypeResult}

private theorem wfTm (hf : RdCallFacts ctx res) (htb : TagBoundedCtx ctx) {tm tm' : TagMeaning}
    (hext : tm ⊑ tm') (hwfTm : wfTagMeaningCtx tm ctx) :
    wfTagMeaningCtx tm' (ctxAfter ctx res) := by
  obtain ⟨_, ls, _, _, hwr, hunw, _, _⟩ := hf.cells htb
  have h0 : wfTagMeaningCtx tm (ctxAfter ctx res) := by
    rcases hwfTm with ⟨hwfTm'⟩
    refine EnvRespectsTagMeaning.intro fun ⟨qtDeep, k0, d0, hqte0, hqd0⟩ => ?_
    rcases hqte0 with ⟨_, _, x, _, qtRoot, hlookupVar, hinq⟩ |
        ⟨_, _, loc, _, qtRoot, hlookupMem, hinq⟩
    · exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
        (QTypInEnvs.inVar _ _ x qtDeep qtRoot hlookupVar hinq) hqd0)
    · have hlookupMem' : res.memEnv'.lookup loc = some qtRoot := hlookupMem
      by_cases hin : loc ∈ ls
      · have hint : qtRoot.etyp = ETyp.int := memEnv_lookup_etyp_int _ _ _ hlookupMem'
        have hEq : qtDeep = qtRoot := QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [hint, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
        rw [hEq] at hqd0
        rcases (hwr loc qtRoot hin hlookupMem').2 with hp | ⟨_, _, _, hp⟩ <;>
          simp [qtypGuardDesc?, hp] at hqd0
      · rw [hunw loc hin] at hlookupMem'
        exact hwfTm' (GuardDescInEnvsDeep.intro qtDeep k0 d0
          (QTypInEnvs.inMem _ _ loc qtDeep qtRoot hlookupMem' hinq) hqd0)
  exact EnvRespectsTagMeaning_mono hext h0

end RdCallFacts

/-- From *match*: the value returned by the call is consistent with the regime
    after the call. -/
private theorem valueConsistent_of_callMatches {predSat : PredSat} {entry : ExternCallEntry}
    {effects : List Effect} {res : TypeResult} {cf : Config} {o : Value} {θ : RealizationMap}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hmatch : CallMatches predSat entry effects res cf o)
    (hθ : runtimeInstantiatesCtx entry.bodyCtx entry.bodyConfig.memory entry.unifiedEnv θ)
    (hvt : valueHasETyp θ o res.qualType.etyp)
    (hnotfun : res.qualType.etyp.isFunctionType = false) :
    valueConsistentWithRegime predSat res.regime' res.qualType cf.memory θ o := by
  have hccv : closureCapturedVarsRegime predSat res.regime' res.qualType cf.memory θ o :=
    closureCapturedVarsRegime_nonClosure_of_nonFunctionType hvt hnotfun
  cases hpred : res.qualType.pred with
  | noPred => exact .noTag (by simp [qtypGuardTag, hpred]) hccv
  | guardOnly k => exact .guardOnly_ok k hpred hccv
  | guardClosure k arg body cap =>
      have htag : qtypGuardTag res.qualType = some k := by simp [qtypGuardTag, hpred]
      obtain ⟨a, ha, hak⟩ := hhinge k htag
      cases hR : res.regime'.lookup? k with
      | none => exact .notInRegime k htag hR hccv
      | some b =>
          have hiff := hmatch.ret a ha arg body cap b (by rw [hak]; exact hpred)
            (by rw [hak]; exact hR) θ hθ
          rw [hak] at hiff
          cases b with
          | true => exact .inRegimeTrue k htag hR (.guardClosure_ok hpred (hiff.mpr rfl)) hccv
          | false =>
              refine .inRegimeFalse k htag hR ?_ hccv
              intro hholds
              cases hholds with
              | noPred_ok h => rw [hpred] at h; cases h
              | guardClosure_ok h hSat =>
                  rw [hpred] at h
                  cases h
                  exact absurd (hiff.mp hSat) (by simp)
              | guardOnly_ok h => rw [hpred] at h; cases h

/-- From *agreement*: a poisoned result that is clean through a guard of the
    call agrees in the two runs. -/
private theorem resultAgreesIfClean_of_callAgrees {predSat : PredSat} {μ₀ μ₁ : Memory}
    {θ₀ θ₁ : RealizationMap} {entry₀ entry₁ : ExternCallEntry} {effects : List Effect}
    {res : TypeResult} {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hpoison : res.qualType.poison = true)
    (hnotfun : res.qualType.etyp.isFunctionType = false)
    (hnotref : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls)
    (hagree : CallAgrees entry₀ entry₁ effects res cf₀ cf₁ o₀ o₁) :
    resultAgreesIfClean predSat res.regime' μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
  intro hclean
  cases hclean with
  | clean hp => rw [hpoison] at hp; cases hp
  | guard k htag hR _ =>
      obtain ⟨a, ha, hak⟩ := hhinge k htag
      exact .withPred_true_eq k htag hR hnotfun hnotref
        (hagree.ret a ha (by rw [hak]; exact htag) (by rw [hak]; exact hR) hnotfun hnotref)

/-- The written address is realized at a cell of the target, so no other
    cell is realized there. -/
private theorem written_addr {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {qtv : QTyp} {ls : LocSet} {a : Address}
    (hθwf : wfRealizationMap θ) (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hlk : ctx.varEnv.lookup "r" = some qtv) (hety : qtv.etyp = .ref ls)
    (hρ : ρ.lookup "r" = some (.loc a)) :
    ∀ l a', l ∉ ls → θ.lookup l = some a' → a' ≠ a := by
  obtain ⟨vR, hvR, hvRt⟩ := hric.2 hlk
  rw [hρ, Option.some.injEq] at hvR
  subst hvR
  rw [hety] at hvRt
  obtain ⟨l_e, hθ_le, hle_in⟩ : ∃ l_e, θ.lookup l_e = some a ∧ l_e ∈ ls := by
    cases hvRt with | loc hlk' hin => exact ⟨_, hlk', hin⟩
  intro l a' hnin hθl heq
  apply hnin
  have hl_e : θ.lookup l_e = some a' := by rw [heq]; exact hθ_le
  rw [hθwf _ _ _ hθl hl_e]
  exact hle_in

/-- The run writes only at `a`. -/
private theorem final_lookup {entry : ExternCallEntry} {cf : Config} {a : Address} {n : Int}
    (hcfmem : cf.memory = entry.callConfig.memory.update a (n / 2)) :
    ∀ a', a' ≠ a → cf.memory.lookup a' = entry.bodyConfig.memory.lookup a' := by
  intro a' hne'
  rw [hcfmem]
  have hcmp : compare a a' ≠ Ordering.eq := fun hce => hne' ((Nat.compare_eq_eq).1 hce).symm
  simp [Memory.update, Memory.lookup, Std.ExtTreeMap.getElem?_insert, hcmp,
    ExternCallEntry.bodyConfig]

/-- The write of `rd` at the address that `r` holds keeps the footprint cells of the
    tags of the final regime.

    A tag `k` with a descriptor in `tm` is below the call's tag, so the final regime
    defines it only if the effect invalidation does (`hf.regime`).  The written
    address is realised at a location of the target `ls`
    (`keepsFootprints_write_effect`). -/
private theorem rd_keepsFootprints {tm : TagMeaning} {ctx : TypeContext} {res : TypeResult}
    {μ : Memory} {ρ : VarEnv} {θ : RealizationMap} {qtv : QTyp} {ls : LocSet} {a : Address}
    {n : Int} (μ' : Memory)
    (hf : RdCallFacts ctx res) (hTmBounded : TagMeaningBounded tm ctx.nextTag)
    (hfp : FootprintCtx tm ctx) (hθwf : wfRealizationMap θ)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hlk : ctx.varEnv.lookup "r" = some qtv) (hety : qtv.etyp = .ref ls)
    (hρ : ρ.lookup "r" = some (.loc a)) :
    KeepsFootprints tm res.regime' θ μ' (μ'.update a n) := by
  obtain ⟨vR, hvR, hvRt⟩ := hric.2 hlk
  rw [hρ, Option.some.injEq] at hvR
  subst hvR
  rw [hety] at hvRt
  obtain ⟨l_e, hθ_le, hle_in⟩ : ∃ l_e, θ.lookup l_e = some a ∧ l_e ∈ ls := by
    cases hvRt with | loc hlk' hin => exact ⟨_, hlk', hin⟩
  intro k d hd hR l' hl' a' ha'
  have hkne : k ≠ ctx.nextTag := Nat.ne_of_lt (hTmBounded k d hd)
  have hR' : (invalidateRegimeDepsEffect ctx.regime ctx.tagEnv
      (effectTargetLocs [rdEff] ctx.varEnv)).lookup? k ≠ none := by
    rw [← hf.regime k hkne]; exact hR
  refine keepsFootprints_write_effect hfp.1 hθwf ⟨l_e, ?_, hθ_le⟩ k d hd hR' l' hl' a' ha'
  rw [rd_targetLocs hlk hety]
  exact Std.ExtTreeSet.contains_iff_mem.mpr hle_in

/-! ## The single-run contract -/

theorem rd_callSingle : ExternCallBoundarySingle rdDecl rdI := by
  intro typedExpr res predSat tm entry ctx htyped hpredlaws hframe hwfTm hTmBounded hfp
    θ cf o hθwf _hwfCtx htagBnd hric _hreg hcons _hwfcfg hrdIn hrun hmatch hpc
  have hf : RdCallFacts ctx res := rd_facts htyped
  obtain ⟨a, n, _hname, _harg, hu, _hn, ho, hcfmem, _hcfnext, hcfshape⟩ := rd_callRun_output hrun
  obtain ⟨qtv, ls, hlk, hety, hwr, hunw, _hcont, hcontOf⟩ := hf.cells htagBnd
  obtain ⟨tm', hext, hbnd', hresp', hwithin⟩ := hf.tagMeaning tm hTmBounded
  have hwritten : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      qt.poison = true ∧ qt.pred = .noPred := by
    intro l qt hin hl
    obtain ⟨hp, hpr⟩ := hwr l qt hin hl
    rcases hpr with h | ⟨_, _, hpc', _⟩
    · exact ⟨hp, h⟩
    · have : ctx.pc = true := hpc
      rw [this] at hpc'; cases hpc'
  have hρ : entry.bodyConfig.varEnv.lookup "r" = some (.loc a) := by
    simpa [ExternCallEntry.bodyConfig] using hu
  have hne := written_addr hθwf hric hlk hety hρ
  have hμ := final_lookup (entry := entry) hcfmem
  have hF : KeepsFootprints tm res.regime' θ entry.bodyConfig.memory cf.memory := by
    show KeepsFootprints tm res.regime' θ entry.callConfig.memory cf.memory
    rw [hcfmem]
    exact rd_keepsFootprints _ hf hTmBounded hfp hθwf hric hlk hety hρ
  have hS : PredSatStable predSat tm res.regime' θ θ entry.bodyConfig.memory cf.memory :=
    predSatStable_of_frame hpredlaws hfp.2 (MapKeepsBelow.refl _ _) hF
  have hvt : valueHasETyp θ o res.qualType.etyp := by rw [ho, hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm', ⟨hext, hbnd', hf.wfTm htagBnd hext hwfTm, hresp',
      TagFrame.laws_of_within hframe hwithin, hwithin⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, hvt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- runtimeInstantiatesCtx
    refine ⟨fun l a' hθl => ?_, fun {x qt} hlk' => hric.2 hlk'⟩
    obtain ⟨hmem, hcont⟩ := hric.1 l a' hθl
    refine ⟨hcontOf l hmem, ?_⟩
    show cf.memory.contains a' = true
    rw [hcfmem]
    have hbc : entry.callConfig.memory.contains a' = true := by
      simpa [ExternCallEntry.bodyConfig] using hcont
    simp [Memory.update, Std.ExtTreeMap.contains_insert, hbc]
  · -- consistentWithRegime
    exact consistent_write (ctx := ctx) (ctx' := ctxAfter ctx res) rfl
      (fun l qt hin hl => Or.inl (hwritten l qt hin hl).2) hunw hne hμ hS hwfTm
      (hf.consistent_regime htagBnd hcons)
  · -- valueConsistentWithRegime
    have h := valueConsistent_of_callMatches hf.guard_mem hmatch hric hvt hf.notfun
    simpa [ExternCallEntry.bodyOutputConfig, ctxAfter] using h
  · -- PreservesInheritedFinalCleanLocsOneRun
    refine ⟨?_⟩
    intro l _qt_in qt_out _hlk_in hlk_out hclean_out
    have hnin : l ∉ ls := by
      intro hin
      obtain ⟨hp, hprednp⟩ := hwritten l qt_out hin hlk_out
      cases hclean_out with
      | clean hp' => rw [hp] at hp'; cases hp'
      | guard k htagk _ _ => simp [qtypGuardTag, hprednp] at htagk
    cases hθl : θ.lookup l with
    | none => exact .both_unrealized hθl hθl
    | some a' =>
        obtain ⟨_, hcontA⟩ := hric.1 l a' hθl
        have hsomeA : (entry.bodyConfig.memory[a']?).isSome = true := by
          rw [← Std.ExtTreeMap.contains_eq_isSome_getElem?]
          exact hcontA
        obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hsomeA
        have hn'' : entry.bodyConfig.memory.lookup a' = some n' := by
          rw [Memory.lookup, Std.ExtTreeMap.get?_eq_getElem?]
          exact hn'
        refine .preserve_value a' n' hθl hn'' hθl ?_
        show cf.memory.lookup a' = some n'
        rw [hμ a' (hne l a' hnin hθl)]
        exact hn''
  · -- FreshCleanLocsUnrealizedOneRun
    intro l qt hnc hlk' hclean
    by_cases hin : l ∈ ls
    · cases hclean with
      | clean hp => rw [(hwritten l qt hin hlk').1] at hp; exact absurd hp (by decide)
      | guard k htag _ _ => simp [qtypGuardTag, (hwritten l qt hin hlk').2] at htag
    · rw [hunw l hin] at hlk'
      exact absurd (memEnv_contains_of_lookup_some _ l qt hlk') hnc
  · -- ReservedDiscipline, the map and the frame
    have hreg_eq : (entry.bodyOutputConfig cf).registry = entry.bodyConfig.registry := by
      rw [hcfshape]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
    refine ⟨?_, MapKeepsBelow.refl _ _, ?_⟩
    · rw [hreg_eq, hf.declared]
      exact hrdIn
    · exact hF

/-! ## The two-run contract -/

/-- After a run, the configuration is well formed. -/
private theorem wfConfig_out {entry : ExternCallEntry} {cf : Config} {a : Address} {n : Int}
    (hwf : wfConfig entry.bodyConfig) (hn : entry.callConfig.memory.lookup a = some n)
    (hcfmem : cf.memory = entry.callConfig.memory.update a (n / 2))
    (hcfnext : cf.nextAddr = entry.callConfig.nextAddr) :
    wfConfig (entry.bodyOutputConfig cf) := by
  have hnext : (entry.bodyOutputConfig cf).nextAddr = entry.bodyConfig.nextAddr := by
    show cf.nextAddr = entry.bodyConfig.nextAddr
    rw [hcfnext]; rfl
  refine ⟨fun a' hc => ?_, ?_⟩
  · have hc' : (entry.callConfig.memory.update a (n / 2)).contains a' := by
      have : (entry.bodyOutputConfig cf).memory = cf.memory := rfl
      rw [this, hcfmem] at hc
      exact hc
    rw [Memory.update, Std.ExtTreeMap.contains_insert] at hc'
    rw [hnext]
    have haC : entry.bodyConfig.memory.contains a = true := by
      have hsome : (entry.callConfig.memory[a]?).isSome = true := by
        have h := hn
        rw [Memory.lookup, Std.ExtTreeMap.get?_eq_getElem?] at h
        rw [h]; rfl
      rw [← Std.ExtTreeMap.contains_eq_isSome_getElem?] at hsome
      simpa [ExternCallEntry.bodyConfig] using hsome
    rcases (by simpa using hc' : a = a' ∨ a' ∈ entry.callConfig.memory) with heq | hold
    · rw [← heq]; exact hwf.1 a haC
    · exact hwf.1 a' (by simpa [ExternCallEntry.bodyConfig] using hold)
  · show wfVarEnv (entry.bodyOutputConfig cf).nextAddr (entry.bodyOutputConfig cf).varEnv
    rw [hnext]
    exact hwf.2

/-- After a run, the memory realizes the context after the call. -/
private theorem runtime_out {ctx : TypeContext} {res : TypeResult} {entry : ExternCallEntry} {cf : Config}
    {a : Address} {n : Int} {θ : RealizationMap}
    (hcontOf : ∀ l, ctx.memEnv.contains l = true → res.memEnv'.contains l = true)
    (hcfmem : cf.memory = entry.callConfig.memory.update a (n / 2))
    (hric : runtimeInstantiatesCtx ctx entry.bodyConfig.memory entry.bodyConfig.varEnv θ) :
    runtimeInstantiatesCtx (ctxAfter ctx res) (entry.bodyOutputConfig cf).memory
      (entry.bodyOutputConfig cf).varEnv θ := by
  refine ⟨fun l a' hθl => ?_, fun {x qt} hlk' => hric.2 hlk'⟩
  obtain ⟨hmem, hcont⟩ := hric.1 l a' hθl
  refine ⟨hcontOf l hmem, ?_⟩
  show cf.memory.contains a' = true
  rw [hcfmem]
  have hbc : entry.callConfig.memory.contains a' = true := by
    simpa [ExternCallEntry.bodyConfig] using hcont
  simp [Memory.update, Std.ExtTreeMap.contains_insert, hbc]

private theorem reserved_out {entry : ExternCallEntry} {cf : Config} {ds : List ExternId}
    {θ : RealizationMap}
    (hcfshape : cf = { entry.callConfig with memory := cf.memory, nextAddr := cf.nextAddr })
    (h : ReservedDiscipline entry.bodyConfig.registry ds θ) :
    ReservedDiscipline (entry.bodyOutputConfig cf).registry ds θ := by
  have hreg_eq : (entry.bodyOutputConfig cf).registry = entry.bodyConfig.registry := by
    rw [hcfshape]; simp [ExternCallEntry.bodyOutputConfig, ExternCallEntry.bodyConfig]
  rw [hreg_eq]
  exact h

theorem rd_callFR : ExternCallBoundaryFR rdDecl rdI := by
  intro postExpr typedExpr₀ _typedExpr₁ res predSat tm entry₀ entry₁ ctx hctx₁
    htyped₀ _htyped₁ hpredlaws hframe hwfTm hTmBounded hfp θ₀ θ₁ hbody cf₀ cf₁ o₀ o₁ hrun₀ hrun₁
    hmatch₀ hmatch₁ hagree
  have hf : RdCallFacts ctx res := rd_facts htyped₀
  have htb := hbody.tagBounded
  obtain ⟨a₀, n₀, _, _, hu₀, hn₀, ho₀, hcfmem₀, hcfnext₀, hcfshape₀⟩ := rd_callRun_output hrun₀
  obtain ⟨a₁, n₁, _, _, hu₁, hn₁, ho₁, hcfmem₁, hcfnext₁, hcfshape₁⟩ := rd_callRun_output hrun₁
  obtain ⟨qtv, ls, hlk, hety, hwr, hunw, _hcont, hcontOf⟩ := hf.cells htb
  obtain ⟨tm', hext, hbnd', hresp', hwithin⟩ := hf.tagMeaning tm hTmBounded
  have hlaws' := TagFrame.laws_of_within hframe hwithin
  have hwfTm' := hf.wfTm htb hext hwfTm
  have hρ₀ : entry₀.bodyConfig.varEnv.lookup "r" = some (.loc a₀) := by
    simpa [ExternCallEntry.bodyConfig] using hu₀
  have hρ₁ : entry₁.bodyConfig.varEnv.lookup "r" = some (.loc a₁) := by
    simpa [ExternCallEntry.bodyConfig] using hu₁
  have hne₀ := written_addr hbody.wfRealization₀ hbody.runtime₀ hlk hety hρ₀
  have hne₁ := written_addr hbody.wfRealization₁ hbody.runtime₁ hlk hety hρ₁
  have hμ₀ := final_lookup (entry := entry₀) hcfmem₀
  have hμ₁ := final_lookup (entry := entry₁) hcfmem₁
  have hF₀ : KeepsFootprints tm res.regime' θ₀ entry₀.bodyConfig.memory cf₀.memory := by
    show KeepsFootprints tm res.regime' θ₀ entry₀.callConfig.memory cf₀.memory
    rw [hcfmem₀]
    exact rd_keepsFootprints _ hf hTmBounded hfp hbody.wfRealization₀ hbody.runtime₀ hlk hety hρ₀
  have hF₁ : KeepsFootprints tm res.regime' θ₁ entry₁.bodyConfig.memory cf₁.memory := by
    show KeepsFootprints tm res.regime' θ₁ entry₁.callConfig.memory cf₁.memory
    rw [hcfmem₁]
    exact rd_keepsFootprints _ hf hTmBounded hfp hbody.wfRealization₁ hbody.runtime₁ hlk hety hρ₁
  have hS₀ : PredSatStable predSat tm res.regime' θ₀ θ₀ entry₀.bodyConfig.memory cf₀.memory :=
    predSatStable_of_frame hpredlaws hfp.2 (MapKeepsBelow.refl _ _) hF₀
  have hS₁ : PredSatStable predSat tm res.regime' θ₁ θ₁ entry₁.bodyConfig.memory cf₁.memory :=
    predSatStable_of_frame hpredlaws hfp.2 (MapKeepsBelow.refl _ _) hF₁
  have hvt₀ : valueHasETyp θ₀ o₀ res.qualType.etyp := by
    rw [ho₀, hf.etyp]; exact valueHasETyp.num _
  have hvt₁ : valueHasETyp θ₁ o₁ res.qualType.etyp := by
    rw [ho₁, hf.etyp]; exact valueHasETyp.num _
  have hwritten : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      qt.pred = .noPred ∨ ∃ k, qt.pred = .guardOnly k := by
    intro l qt hin hl
    rcases (hwr l qt hin hl).2 with h | ⟨_, _, _, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, h⟩
  -- The written cell: clean only through the call's tag, and then the cell
  -- clause of agreement gives the same content in the two runs.
  have hcell : ∀ l qt, l ∈ ls → res.memEnv'.lookup l = some qt →
      qtypCleanUnder res.regime' qt →
      agreeLocUnder predSat res.regime' cf₀.memory cf₁.memory θ₀ θ₁ (l, qt) := by
    intro l qt hin hl hclean
    obtain ⟨hp, hpr⟩ := hwr l qt hin hl
    cases hclean with
    | clean hp' => rw [hp] at hp'; cases hp'
    | guard k htagk hRk _ =>
        rcases hpr with hnp | ⟨hls, _hqp, _hpc, hgo⟩
        · simp [qtypGuardTag, hnp] at htagk
        · have hkc : k = ctx.nextTag := by
            simp only [qtypGuardTag, hgo, Option.some.injEq] at htagk
            exact htagk.symm
          subst hkc
          have hfin₀ : cf₀.memory.lookup a₀ = some (n₀ / 2) := by
            rw [hcfmem₀]
            simp [Memory.update, Memory.lookup]
          have hfin₁ : cf₁.memory.lookup a₁ = some (n₁ / 2) := by
            rw [hcfmem₁]
            simp [Memory.update, Memory.lookup]
          exact cell_agree hctx₁ hlk hety hls hl htagk hf.logged hRk hRk
            (memEnv_lookup_etyp_int _ _ _ hl) hu₀ hu₁
            (realize_singleton hbody.runtime₀ hlk hety hls hρ₀)
            (realize_singleton hbody.runtime₁ hlk hety hls hρ₁) hfin₀ hfin₁ hagree
  refine ⟨tm', ⟨hext, hbnd', hwfTm', hresp', hlaws', hwithin⟩, hlaws', hresp',
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩, hvt₀, hvt₁, hwfTm',
    hf.wfCtx htb hbody.wfCtx, hf.tagBounded htb,
    wfConfig_out hbody.wfConfig₀ hn₀ hcfmem₀ hcfnext₀,
    wfConfig_out hbody.wfConfig₁ hn₁ hcfmem₁ hcfnext₁,
    runtime_out hcontOf hcfmem₀ hbody.runtime₀, runtime_out hcontOf hcfmem₁ hbody.runtime₁,
    hf.regimeConsistent htb hbody.regime,
    consistent_write (ctx := ctx) (ctx' := ctxAfter ctx res) rfl hwritten hunw hne₀ hμ₀ hS₀ hwfTm
      (hf.consistent_regime htb hbody.consistent₀),
    consistent_write (ctx := ctx) (ctx' := ctxAfter ctx res) rfl hwritten hunw hne₁ hμ₁ hS₁ hwfTm
      (hf.consistent_regime htb hbody.consistent₁),
    agree_write (ctx := ctx) (ctx' := ctxAfter ctx res) rfl hunw hne₀ hne₁ hμ₀ hμ₁ hS₀ hS₁ hwfTm
      hcell (hf.agree_regime htb hbody.agree),
    valueConsistent_of_callMatches (cf := cf₀) hf.guard_mem hmatch₀ hbody.runtime₀ hvt₀ hf.notfun,
    valueConsistent_of_callMatches (cf := cf₁) hf.guard_mem hmatch₁ (hctx₁ ▸ hbody.runtime₁) hvt₁
      hf.notfun,
    resultAgreesIfClean_of_callAgrees hf.guard_mem hf.poison hf.notfun hf.notref hagree,
    ?_, ?_, MapKeepsBelow.refl _ _, MapKeepsBelow.refl _ _, ?_, ?_⟩
  · rw [hf.declared]; exact reserved_out hcfshape₀ hbody.reserved₀
  · rw [hf.declared]; exact reserved_out hcfshape₁ hbody.reserved₁
  · exact hF₀
  · exact hF₁

/-! ## Operational safety -/

private theorem rdImpl_operationalSafe : ExternOperationalSafe rdDecl rdI := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn himpl env vArg mem addr vRaw mem' addr' hrun
    simp only [rdI, ExternImpl.fn.injEq] at himpl
    subst himpl
    obtain ⟨a, rfl⟩ : ∃ a, vArg = .loc a := by
      cases vArg with
      | loc a => exact ⟨a, rfl⟩
      | _ => simp [rdImpl] at hrun
    cases hn : mem.lookup a with
    | none => simp [rdImpl, hn] at hrun
    | some n =>
        simp only [rdImpl, hn, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        refine ⟨Nat.le_refl _, fun hmem _ _ => ⟨fun a' hc' => ?_, wfValue.num _⟩⟩
        have haC : mem.contains a = true := by
          have hsome : (mem[a]?).isSome = true := by
            have h := hn
            rw [Memory.lookup, Std.ExtTreeMap.get?_eq_getElem?] at h
            rw [h]; rfl
          rw [← Std.ExtTreeMap.contains_eq_isSome_getElem?] at hsome
          exact hsome
        by_cases h_eq : a' = a
        · subst h_eq; exact hmem _ haC
        · have hcmp : compare a a' ≠ Ordering.eq :=
            fun hc => h_eq (LawfulEqCmp.eq_of_compare hc).symm
          exact hmem a' (by
            simpa [Memory.update] using
              ExtTreeMap.contains_of_contains_insert
                (t := mem) (k := a) (a := a') (v := n / 2) hc' hcmp)
  · intro implPfn himpl _ _ _ _ _ _ _ _ _
    simp [rdI] at himpl
  · intro v himpl _ _
    simp [rdI] at himpl
  · intro implFn himpl env vArg mem addr vRaw mem' addr' hrun a' hc
    simp only [rdI, ExternImpl.fn.injEq] at himpl
    subst himpl
    obtain ⟨a, rfl⟩ : ∃ a, vArg = .loc a := by
      cases vArg with
      | loc a => exact ⟨a, rfl⟩
      | _ => simp [rdImpl] at hrun
    cases hn : mem.lookup a with
    | none => simp [rdImpl, hn] at hrun
    | some n =>
        simp only [rdImpl, hn, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, rfl, _⟩ := hrun
        simp only [Memory.update]
        rw [ExtTreeMap.contains_insert]
        simp [hc]

/-! ## The declaration contracts -/

/-- The extern closure stored in the `rd` declaration's `arrow` type. -/
private def rdExternClosure (ctx : TypeContext) (argQt : QTyp) : FnTClosure :=
  FnTClosure.extern 8 "r" readRet [rdEff]
    (VarTypeEnv.toCaptured ctx.varEnv) argQt []

/-- The exact `TypeResult` produced by typechecking `extern fn @8 …` in `ctx`. -/
private def rdDeclResult (ctx : TypeContext) (argQt : QTyp) : TypeResult := {
  qualType :=
    ⟨ETyp.arrow (Typ.ref Typ.int) (parseReturnType readRet) ctx.pc
        [rdExternClosure ctx argQt],
      ctx.pc, Predicate.noPred⟩
  memEnv' := ctx.memEnv
  tagEnv' := ctx.tagEnv
  nextLoc' := ctx.nextLoc
  nextTag' := ctx.nextTag
  regime' := ctx.regime
  declared' := 8 :: (readRet.declIds ++ ctx.declaredExternRefs)
}

/-- Inverting a `rd` declaration typing witness pins the result to
    `rdDeclResult ctx argQt` for some argument precondition `argQt`. -/
private theorem rd_decl_shape
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl rdDecl postExpr ctx res) :
    ∃ argQt : QTyp, res = rdDeclResult ctx argQt := by
  cases htyped with
  | fn htc =>
      rename_i fuel argPred
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ fuel' =>
          have htcFn :
              typecheckExternFn ctx 8 "r" (Typ.ref Typ.int) false argPred readRet
                [rdEff] [] fuel' = .ok res := by
            have h := htc
            simp only [typecheck, typecheckExpr] at h
            exact h
          obtain ⟨argQt, _hpoison, hres⟩ :=
            typecheckExternFn_ok_res_eq ctx 8 "r" (Typ.ref Typ.int) false argPred readRet
              [rdEff] res htcFn
          exact ⟨argQt, hres⟩

/-- The declaration expression typed against `rdDecl` is
    `externFn @8` with the `ref int` argument and the effect `!r`; only its
    argument predicate and captures are free. -/
private theorem rd_decl_postExpr
    {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl rdDecl postExpr ctx res) :
    ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      postExpr = Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet
        [rdEff] captures := by
  cases htyped with
  | fn _htc => exact ⟨_, _, rfl⟩

/-- The `rd` declaration's extern closure value is well-typed at the
    declared `arrow` type (the `fn` mirror of the generic `pfnExternDecl_valueHasETyp`). -/
private theorem rd_decl_valueHasETyp
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    valueHasETyp θ
      (Value.closure "r"
        (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet [rdEff] captures) ρ)
      (rdDeclResult ctx argQt).qualType.etyp := by
  show valueHasETyp θ
      (Value.closure "r"
        (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet [rdEff] captures) ρ)
      (ETyp.arrow (Typ.ref Typ.int) (parseReturnType readRet) ctx.pc
        [rdExternClosure ctx argQt])
  refine valueHasETyp.closure_extern (tenv := VarTypeEnv.toCaptured ctx.varEnv)
      (argQTyp := argQt) (memberCap := []) (htcl := by simp [rdExternClosure])
      (henv := ?_) (hcover := ?_)
  · intro n qt v hlookupσ hlookupρ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, hvtyp⟩ := hric.2 hlookup_ctx
    have hvEq : v' = v := by
      have : some v' = some v := by rw [← hvlookup, hlookupρ]
      exact Option.some.inj this
    subst hvEq; exact hvtyp
  · intro n qt hlookupσ
    have hlookup_ctx : ctx.varEnv.lookup n = some qt :=
      VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv n qt hlookupσ
    obtain ⟨v', hvlookup, _⟩ := hric.2 hlookup_ctx
    exact ⟨v', hvlookup⟩

/-- The `rd` declaration's extern closure value is regime-consistent (the
    `fn` mirror of the generic `pfnExternDecl_valueConsistent`). -/
private theorem rd_decl_valueConsistent
    {predSat : PredSat} {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {argPred : SyntaxPredicate} {argQt : QTyp} {captures : List Capture}
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ) :
    valueConsistentWithRegime predSat ctx.regime (rdDeclResult ctx argQt).qualType μ θ
      (Value.closure "r"
        (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet [rdEff] captures) ρ) := by
  refine valueConsistentWithRegime.noTag (by simp [qtypGuardTag, rdDeclResult]) (.intro ?_)
  apply deepValueQTypProperty.closure_extern (argQt := argQt) (memberCap := []) 8 "r" "r" (Typ.ref Typ.int)
      readRet [rdEff] ρ
      (VarTypeEnv.toCaptured ctx.varEnv) ctx.pc [rdExternClosure ctx argQt]
  · rfl
  · rfl
  · simp [rdExternClosure]
  · refine ⟨?_, ?_⟩
    · intro y qt_y k_y hlookupσ hguard hkR
      exact hcwr.2.1 y qt_y k_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hguard hkR
    · exact ⟨VarTypeEnv_toCaptured_nodup_fst ctx.varEnv,
        fun y qt hlookupσ =>
          let ⟨v, hv, _⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          ⟨v, hv⟩,
        fun y qt v hlookupσ hlookupρ =>
          let ⟨v', hv', htyp⟩ := hric.2 (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt hlookupσ)
          by rw [hlookupρ] at hv'; cases hv'; exact htyp⟩
  · intro y qt_y v_y hlookupσ hlookupρ
    cases hcwr.2.2 y qt_y v_y
        (VarTypeEnv_lookup_of_toCaptured_lookup ctx.varEnv y qt_y hlookupσ) hlookupρ with
    | intro h => exact h

/-- A successful `rd` declaration boundary leaves the config unchanged and
    emits the extern `fn` closure value (`val`/`pfn` impossible by kind). -/
private theorem rd_declRun_shape
    {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config} {o : Value}
    (hrun : ExternDeclBoundaryRun rdDecl rdI ctx res cᵢ cf o) :
    cf = cᵢ ∧ ∃ (argPred : SyntaxPredicate) (captures : List Capture),
      o = Value.closure "r"
        (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet [rdEff] captures)
        cᵢ.varEnv := by
  cases hrun with
  | val hfacts => have h := hfacts.kind_val; simp [rdDecl] at h
  | ref hfacts => have h := hfacts.kind_ref; simp [rdDecl] at h
  | pfn hfacts => have h := hfacts.kind_pfn; simp [rdDecl] at h
  | fn hfacts =>
      refine ⟨hfacts.output_config, ?_⟩
      obtain ⟨x, argPred, retSpec, captures, hargName, hretSpec, hval⟩ := hfacts.value_shape
      have hx : x = "r" := by
        have h := hargName; simp [rdDecl] at h; exact h.symm
      have hretSpec' : retSpec = readRet := by
        have h := hretSpec; simp [rdDecl] at h; exact h.symm
      subst hx; subst hretSpec'
      exact ⟨argPred, captures, by simpa [rdDecl] using hval⟩

/-- The `rd` single-run declaration-boundary field. -/
theorem rd_declSingle :
    ExternDeclBoundarySingle rdDecl rdI := by
  intro postExpr ctx res predSat tm htyped hpredlaws _hframe hwfTm hTmBounded _hfp
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc _hvm
  obtain ⟨argQt, hres⟩ := rd_decl_shape htyped
  obtain ⟨hcf, argPred, captures, ho⟩ := rd_declRun_shape hrun
  have hctxAfter : ctxAfter ctx res = { ctx with declaredExternRefs := res.declared' } := by
    rw [hres]; simp [ctxAfter, rdDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_fn_extern tm ctx 8 "r" (Typ.ref Typ.int) (parseReturnType readRet)
      ctx.pc readRet [rdEff] (argQt := argQt) hwfTm
  have hcfmem : cf.memory = μ := by rw [hcf]
  have hcfvar : cf.varEnv = ρ := by rw [hcf]
  have ho' : o = Value.closure "r"
      (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPred readRet [rdEff] captures) ρ := by
    rw [ho]
  have hd_res : ∀ x, x ∈ ctx.declaredExternRefs → x ∈ res.declared' := by
    intro x hx; rw [hres]; simp [rdDeclResult, hx]
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws,
      WithinLog.refl tm _⟩, θ,
    ⟨fun _ _ h => h, fun h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨(by rw [hcf]; exact ReservedDiscipline.mono_declared hd_res hrdIn), MapKeepsBelow.refl _ _,
      (by rw [hcfmem]; exact KeepsFootprints.refl _ _ _ _)⟩⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho', hres]; exact rd_decl_valueHasETyp hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hric
  · rw [hctxAfter, hcfmem, hcfvar]; exact hcons
  · rw [hctxAfter, hcfmem, hres, ho']; exact rd_decl_valueConsistent hric hcons
  · rw [hcfmem]; exact PreservesInheritedFinalCleanLocsOneRun.refl hric
  · intro l qt hnotContains hlookup _hclean
    rw [hres] at hlookup
    exact absurd (memEnv_contains_of_lookup_some ctx.memEnv l qt hlookup) hnotContains

/-- The `rd` paired declaration-boundary field: both outputs are the `fn`
    closure of the shared declaration expression, so the two clean extern arrows
    agree via `agreeValueUnder.clean_internal_arrow_extern`. -/
theorem rd_declFR :
    ExternDeclBoundaryFR rdDecl rdI := by
  intro postExpr ctx res predSat tm htyped hpredlaws _hframe hwfTm hTmBounded _hfp
    μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg
    hcwr₀ hcwr₁ hagree a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrdIn₀ hrdIn₁ hrun₀ hrun₁
    _hvm₀ _hvm₁
  obtain ⟨argQt, hres⟩ := rd_decl_shape htyped
  obtain ⟨argPredT, capturesT, hpostExpr⟩ := rd_decl_postExpr htyped
  obtain ⟨hcf₀, _⟩ := rd_declRun_shape hrun₀.run
  obtain ⟨hcf₁, _⟩ := rd_declRun_shape hrun₁.run
  have ho₀ : o₀ = Value.closure "r"
      (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPredT readRet [rdEff] capturesT) ρ₀ := by
    have hfe := hrun₀.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have ho₁ : o₁ = Value.closure "r"
      (Expr.externFn 8 "r" (Typ.ref Typ.int) false argPredT readRet [rdEff] capturesT) ρ₁ := by
    have hfe := hrun₁.forExpr; rw [hpostExpr] at hfe
    simpa [declRunOutputMatchesExpr] using hfe
  have hctxAfter : ctxAfter ctx res = { ctx with declaredExternRefs := res.declared' } := by
    rw [hres]; simp [ctxAfter, rdDeclResult]
  have hnt : res.nextTag' = ctx.nextTag := by rw [hres]; rfl
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    rw [hres]
    exact QTypRespectsTagMeaning_fn_extern tm ctx 8 "r" (Typ.ref Typ.int) (parseReturnType readRet)
      ctx.pc readRet [rdEff] (argQt := argQt) hwfTm
  have hcf₀mem : cf₀.memory = μ₀ := by rw [hcf₀]
  have hcf₀var : cf₀.varEnv = ρ₀ := by rw [hcf₀]
  have hcf₁mem : cf₁.memory = μ₁ := by rw [hcf₁]
  have hcf₁var : cf₁.varEnv = ρ₁ := by rw [hcf₁]
  have hd_res : ∀ x, x ∈ ctx.declaredExternRefs → x ∈ res.declared' := by
    intro x hx; rw [hres]; simp [rdDeclResult, hx]
  refine ⟨tm, ⟨TagMeaningExtends.refl tm, ?_, ?_, hresTm, hpredlaws,
      WithinLog.refl tm _⟩, hpredlaws, hresTm,
    θ₀, θ₁, ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [hcf₀]; exact ReservedDiscipline.mono_declared hd_res hrdIn₀),
    (by rw [hcf₁]; exact ReservedDiscipline.mono_declared hd_res hrdIn₁),
    MapKeepsBelow.refl _ _, MapKeepsBelow.refl _ _,
    (by rw [hcf₀mem]; exact KeepsFootprints.refl _ _ _ _),
    (by rw [hcf₁mem]; exact KeepsFootprints.refl _ _ _ _)⟩
  · rw [hnt]; exact hTmBounded
  · rw [hctxAfter]; exact hwfTm
  · rw [ho₀, hres]; exact rd_decl_valueHasETyp hric₀
  · rw [ho₁, hres]; exact rd_decl_valueHasETyp hric₁
  · rw [hctxAfter]; exact hwfTm
  · rw [hctxAfter]; exact hwf
  · rw [hctxAfter]; exact htagBounded
  · rw [hcf₀]; exact hwfcfg₀
  · rw [hcf₁]; exact hwfcfg₁
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hric₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hric₁
  · rw [hctxAfter]; exact hreg
  · rw [hctxAfter, hcf₀mem, hcf₀var]; exact hcwr₀
  · rw [hctxAfter, hcf₁mem, hcf₁var]; exact hcwr₁
  · rw [hctxAfter, hcf₀mem, hcf₀var, hcf₁mem, hcf₁var]; exact hagree
  · rw [hctxAfter, hcf₀mem, hres, ho₀]; exact rd_decl_valueConsistent hric₀ hcwr₀
  · rw [hctxAfter, hcf₁mem, hres, ho₁]; exact rd_decl_valueConsistent hric₁ hcwr₁
  · -- resultAgreesIfClean: the two extern arrows agree (shared argPredT)
    rw [hctxAfter, hcf₀mem, hcf₁mem, hres]
    intro hclean
    cases hclean with
    | clean hpoison =>
        have hetyp : (rdDeclResult ctx argQt).qualType.etyp =
            ETyp.arrow (Typ.ref Typ.int) (parseReturnType readRet) ctx.pc
              [rdExternClosure ctx argQt] := rfl
        have htcl : rdExternClosure ctx argQt ∈ [rdExternClosure ctx argQt] := by simp
        have hpc_clean : ctx.pc = false := by
          have hpoison' : (rdDeclResult ctx argQt).qualType.poison = false := hpoison
          simpa [rdDeclResult] using hpoison'
        have hclean_internal : internalPoisonClean (rdDeclResult ctx argQt).qualType := by
          simp [internalPoisonClean, getInternalPoison, hetyp, hpc_clean]
        have hcap : agreeCapturedEnv predSat ctx.regime μ₀ μ₁ θ₀ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ ρ₁ :=
          agreeCapturedEnv_of_agreeOnClean predSat ctx.regime ctx μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ hric₀ hric₁ hagree
        have hmemberVars₀ : MemberVarsRegimeEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberVars₁ : MemberVarsRegimeEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberVarsRegimeEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have hmemberCvcr₀ : MemberCvcrEvidence predSat ctx.regime μ₀ θ₀
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₀) (ρ := ρ₀) (θ := θ₀) hcwr₀
        have hmemberCvcr₁ : MemberCvcrEvidence predSat ctx.regime μ₁ θ₁
            (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          memberCvcrEvidence_of_toCaptured (predSat := predSat) (R := ctx.regime) (ctx := ctx)
            (μ := μ₁) (ρ := ρ₁) (θ := θ₁) hcwr₁
        have htyping₀ : capturedVarsTypingProperty θ₀ (VarTypeEnv.toCaptured ctx.varEnv) ρ₀ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₀ ρ₀ θ₀ hric₀
        have htyping₁ : capturedVarsTypingProperty θ₁ (VarTypeEnv.toCaptured ctx.varEnv) ρ₁ :=
          capturedVarsTypingProperty_of_toCaptured ctx μ₁ ρ₁ θ₁ hric₁
        exact agreeValueUnder.clean_internal_arrow_extern
          (σcap := VarTypeEnv.toCaptured ctx.varEnv) (argQt := argQt)
          (ρcap₁ := ρ₀) (ρcap₂ := ρ₁) (v₁ := o₀) (v₂ := o₁)
          hclean_internal hetyp htcl rfl hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁
          htyping₀ htyping₁ ho₀ ho₁
    | guard k htag _hregime _hnotfun =>
        have hnone : qtypGuardTag (rdDeclResult ctx argQt).qualType = none := by
          simp [qtypGuardTag, rdDeclResult]
        simp [hnone] at htag


/-- The trusted entry of `rd`. -/
theorem rdSpec : ExternBoundarySpec rdDecl rdI where
  declFR := rd_declFR
  callFR := rd_callFR
  declSingle := rd_declSingle
  callSingle := rd_callSingle
  operational := rdImpl_operationalSafe

/-- The trusted registry that holds `rd` only. -/
def rdReg : TrustedRegistry := [⟨rdDecl, rdI, rdSpec⟩]

/-! ## The theorem at `rd (ref x)` -/

/-- No critical input; the scenario commits the tags of `rd`. -/
def sRd : InputSpec := { locs := ∅, vars := ∅, regimeExterns := [8] }

/-- The runtime registry of `rdReg` is the registry of the runs. -/
theorem rdReg_runtime : rdReg.toRuntimeRegistry = regC := rfl

private theorem regC_noVal {id : ExternId} {v : Value} (h : regC.get? id = some (.val v)) :
    False := by
  by_cases hid : id = 8
  · subst hid; simp [regC] at h
  · simp [regC, emptyExternRegistry, Ne.symm hid] at h

private theorem K0_vars : ∀ x qt, K0.varEnv.lookup x = some qt → qt = pInt := by
  intro x qt h
  by_cases hx : x = "x"
  · subst hx
    simp only [K0, VarTypeEnv_lookup_update_eq, Option.some.injEq] at h
    exact h.symm
  · simp only [K0] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h

private theorem pInt_not_clean (R : Regime) : ¬ qtypCleanUnder R pInt := by
  intro h
  cases h with
  | clean hpoison => simp [pInt] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, pInt] at htag

private theorem externRegimeMatchesK0 : ExternRegimeMatchesInputSpec sRd K0 := by
  refine ⟨fun {id} hid k => ?_, fun {id} hid k => ?_⟩
  · have h8 : id ≠ 8 := by simpa [sRd] using hid
    simp [K0, pol, h8]
  · simp only [sRd, List.mem_singleton] at hid
    subst hid
    exact ⟨true, by simp [K0, pol]⟩

private theorem trustedK0 : InitialContextTrusted rdReg prog K0 := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 8 ∧ d = rdDecl := by
        simp only [prog, rdD, arg] at hp
        cases hp with
        | app_fun h =>
            cases h with
            | externFn => exact ⟨rfl, rfl⟩
            | externFn_return hret => cases hret
        | app_arg h =>
            cases h with
            | newRef h' => cases h'
      obtain ⟨rfl, rfl⟩ := h
      simp [rdReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K0_vars _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

private theorem wfSpecRd : wfInputSpec sRd := by
  unfold wfInputSpec
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l qt h
    simp [sRd, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · refine And.intro ?_ ?_
      · exact Std.ExtTreeMap.nodup_keys
      · intro x qt h
        simp [sRd, VarTypeEnv.lookup] at h
    · intro x qt h
      simp [sRd, VarTypeEnv.lookup] at h
  · intro x qt h
    simp [sRd, VarTypeEnv.lookup] at h

private theorem ctxMatchesK0 : ctxMatchesInputSpec sRd K0 := by
  unfold ctxMatchesInputSpec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l qt h
    simp [sRd, MemoryTypeEnv.lookup] at h
  · intro x qt h
    simp [sRd, VarTypeEnv.lookup] at h
  · intro l qt k h
    simp [K0, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · intro x qt k h htag _
      rw [K0_vars x qt h] at htag
      simp [qtypGuardTag, pInt] at htag
    · intro x qt h
      rw [K0_vars x qt h]
      exact deepQTypProperty.other _ _ trivial

private theorem wfCtxK0 : wfTypeContext K0 := by
  unfold wfTypeContext
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l h
    simp [K0] at h
  · intro x qt h
    rw [K0_vars x qt h]
    exact trivial
  · intro x qt h
    rw [K0_vars x qt h]
    exact trivial

private theorem tagBoundedK0 : TagBoundedCtx K0 := by
  unfold TagBoundedCtx
  refine And.intro ?_ (And.intro (And.intro ?_ ?_) ?_)
  · intro k hk
    simp [K0] at hk
  · intro x qt h
    rw [K0_vars x qt h]
    exact trivial
  · intro l qt h
    simp [K0, MemoryTypeEnv.lookup] at h
  · intro x qt h
    rw [K0_vars x qt h]
    exact trivial

/-- The starting context has no guard: `x` is a poisoned `int` without predicate. -/
private theorem noGuardK0 {k : Tag} {d : GuardDesc} :
    ¬ GuardDescInEnvsDeep K0.varEnv K0.memEnv k d := by
  intro hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
      have hroot := K0_vars x qtRoot hlookup
      subst hroot
      have hqt : qt = pInt :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [pInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, pInt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
      simp [K0, MemoryTypeEnv.lookup] at hlookup

private theorem wfTmK0 : wfTagMeaningCtx ∅ K0 :=
  EnvRespectsTagMeaning.intro (fun hdeep => absurd hdeep noGuardK0)

private theorem guardCapsK0 : GuardCapsBelow K0 :=
  fun _ _ hdeep => absurd hdeep noGuardK0

private theorem tmBoundedK0 : TagMeaningBounded ∅ K0.nextTag := by
  intro k d h
  simp [TagMeaning.lookup] at h

private theorem lawsEmpty : PredSatLaws geSat ∅ :=
  predSatLaws_geSat (fun k d h => by simp [TagMeaning.lookup] at h)

private theorem wfRegimeK0 : wfRegime K0.regime sRd := by
  have htags : inputSpecTags sRd = [] := rfl
  refine And.intro ?_ ?_
  · intro k hk
    rw [htags] at hk
    cases hk
  · intro k hk
    simp [K0, Regime.lookup?] at hk

private theorem wfθ₀ : wfRealizationMap ∅ := by
  intro l₁ l₂ a h
  simp [RealizationMap.lookup] at h

private theorem wfCX (n : Int) : wfConfig (cfgX n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgX] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

private theorem reservedWFC : RegistryReservedWF regC ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regC_noVal h).elim

private theorem disciplineK0 : ReservedDiscipline regC K0.declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regC_noVal h).elim
  · intro id a h _ l
    exact (regC_noVal h).elim

private theorem lookupX (n : Int) :
    (VarEnv.update [] "x" (.num n)).lookup "x" = some (.num n) := by
  simp [VarEnv.update, VarEnv.lookup]

private theorem instantiatesK0 (n : Int) :
    runtimeInstantiatesCtx K0 ∅ (VarEnv.update [] "x" (.num n)) ∅ := by
  refine And.intro ?_ ?_
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    have hq := K0_vars x qt h
    subst hq
    have hx : x = "x" := by
      by_contra hx
      simp only [K0] at h
      rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
      simp [VarTypeEnv.lookup] at h
    subst hx
    exact ⟨_, lookupX n, valueHasETyp.num n⟩

private theorem trustedInitK0 (n : Int) :
    trustedVarsClosureRegimeInit geSat K0.regime sRd K0 ∅ (VarEnv.update [] "x" (.num n)) ∅ := by
  refine trustedVarsClosureRegimeInit.intro ?_
  intro x qt v h _ hv
  have hq := K0_vars x qt h
  subst hq
  have hx : x = "x" := by
    by_contra hx
    simp only [K0] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h
  subst hx
  rw [lookupX n] at hv
  obtain rfl := Option.some.inj hv
  exact closureCapturedVarsRegime.intro
    (deepValueQTypProperty.nonClosure (fun _ _ _ hc => by cases hc)
      (fun _ _ _ hc => by cases hc))

private theorem consistentK0 {ρ : VarEnv} :
    consistentRegimeSpec geSat K0.regime sRd ∅ ρ ∅ := by
  unfold consistentRegimeSpec
  have hnil : memEnvToLocQTypList sRd.locs = [] := rfl
  have hnil' : sRd.vars.toList = [] := rfl
  rw [hnil, hnil']
  exact ⟨trivial, trivial⟩

private theorem agreeCriticalK0 {ρ₁ ρ₂ : VarEnv} :
    agreeOnCriticalInputsUnderRegimeSpec geSat K0.regime sRd ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [sRd, MemoryTypeEnv.lookup] at h
  · intro x qt h _
    simp [sRd, VarTypeEnv.lookup] at h

private theorem agreeTrustedK0 {ρ₁ ρ₂ : VarEnv} :
    agreeOnTrustedInputs geSat K0.regime sRd K0 ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [K0, MemoryTypeEnv.lookup] at h
  · intro x qt h _ hclean
    rw [K0_vars x qt h] at hclean
    exact absurd hclean (pInt_not_clean _)

/-- A run of `rd (ref x)` from `x = n`. -/
theorem run_prog (n : Int) : terminatesTo prog (cfgX n) (cfgF n) (.num 0) := by
  refine ⟨4, false, ?_⟩
  simp [prog, arg, rdD, beval, cfgX, cfgF, cfgR, freshAddr, VarEnv.lookup,
    VarEnv.update, regC, rdImpl, Memory.lookup, Memory.update, validateExternReturn,
    valueMatchesTyp, readRet]

/-- **The theorem at `rd (ref x)`**, for two runs whose calls leave the same
    content in the cell. Nothing is observed. -/
theorem cell_closed (n₀ n₁ : Int) (h : n₀ / 2 = n₁ / 2) :
    ConclusionAt prog (cfgX n₀) (cfgX n₁) := by
  obtain ⟨htc, _, _, _, hmatch, hlaws, _, _⟩ := cell_case
  exact ⟨cfgF n₀, cfgF n₁, .num 0, .num 0, run_prog n₀, run_prog n₁,
    TypeSystemEnforcesFaultRobustness rdReg prog sRd obsNone K0 externRegimeMatchesK0 trustedK0
      wfSpecRd (by simp [wfObsSpec, obsNone]) ctxMatchesK0 wfCtxK0 rfl rfl rfl tagBoundedK0 guardCapsK0
      geSat ∅ wfTmK0 tmBoundedK0 lawsEmpty 60 rootRes htc
      (And.intro (fun _ h => by simp [obsNone] at h)
        (fun _ _ h => by simp [obsNone, MemoryETypEnv.lookup] at h))
      hlaws ∅ ∅ _ _ ∅ ∅ 0 0 false (cfgF n₀) (cfgF n₁) (.num 0) (.num 0) wfRegimeK0 wfθ₀ wfθ₀
      (wfCX n₀) (wfCX n₁) reservedWFC reservedWFC disciplineK0 disciplineK0
      (And.intro (fun h _ => by simp [sRd] at h)
        (fun h _ => by simp [sRd, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sRd] at h)
        (fun h _ => by simp [sRd, VarTypeEnv.lookup] at h))
      (instantiatesK0 n₀) (instantiatesK0 n₁) (trustedInitK0 n₀) (trustedInitK0 n₁)
      consistentK0 consistentK0 (hmatch geSat hlaws n₀) (hmatch geSat hlaws n₁)
      agreeCriticalK0 agreeTrustedK0 ((agree_iff n₀ n₁).2 h) (run_prog n₀) (run_prog n₁)⟩

/-- **The theorem at `rd (ref x)` from `x = 4` and `x = 5`.** -/
theorem cell_closed_4_5 : ConclusionAt prog (cfgX 4) (cfgX 5) :=
  cell_closed 4 5 (by decide)

/-! ## A program that reads the cell back -/

namespace ReadBack

/-! ### The program -/

/-- The body of `let c = ref x`. -/
def inner : Expr :=
  .vlet "ret" (.app rdD (.var "c"))
    (.ite (.op (.var "ret") .gte (.num 0)) (.deref (.var "c")) (.num 0))

/-- `let c = ref x in let ret = rd c in if ret >= 0 then !c else 0` -/
def prog : Expr := .vlet "c" arg inner

/-! ### The typing -/

/-- The typing of `ref x`, the context in which `rd c` is typed, the typing of
    the argument and of the function, the cursor of the member, the member
    result, the body context and the typing of the program. -/
def rRef : TypeResult := okVal (typecheckExpr K0 arg 58)
def K1 : TypeContext := { ctxAfter K0 rRef with varEnv := K0.varEnv.update "c" rRef.qualType }
def rArg : TypeResult := okVal (typecheckExpr K1 (.var "c") 54)
def rFun : TypeResult := okVal (typecheckExpr (ctxAfter K1 rArg) rdD 54)
def cur : Tag × Loc := (rFun.nextTag', rFun.nextLoc')
def callRes : TypeResult :=
  let E := rFun.qualType.etyp
  okVal (fnApply K1 rArg rFun (arrowS1 E) (arrowS2 E) (arrowP E) 54 (arrowM E) cur)
def body : TypeContext :=
  fnBodyCtx K1 rArg rFun (arrowP rFun.qualType.etyp) "r"
    (fExtParts (arrowM rFun.qualType.etyp)).1 cur
def rootRes : TypeResult := okVal (typecheckExpr K0 prog 60)

private def facts : Bool :=
  isOkB (typecheckExpr K0 prog 60) &&
  isOkB (typecheckExpr K0 arg 58) &&
  isOkB (typecheckExpr K1 (.var "c") 54) &&
  isOkB (typecheckExpr (ctxAfter K1 rArg) rdD 54) &&
  isArrow1 rFun.qualType.etyp &&
  (callRes.tagLog'.map (·.tag) == [0]) &&
  (callRes.regime'.lookup? 0 == some true) &&
  (refLocs (body.varEnv.lookup "r") == some [0]) &&
  isCell (callRes.memEnv'.lookup 0) &&
  descGe (programTable ∅ rootRes.tagLog') 0 &&
  allGe rootRes.tagLog' &&
  (rootRes.qualType.etyp == ETyp.int) &&
  (rootRes.qualType.poison == false)

private theorem facts_ok : facts = true := by decide +kernel

private theorem call_chain :
    let E := rFun.qualType.etyp
    arrowM E = .extern 8 "r" readRet [rdEff] (fExtParts (arrowM E)).1 (fExtParts (arrowM E)).2.1
      (fExtParts (arrowM E)).2.2 ∧
    isOkB (fnApply K1 rArg rFun (arrowS1 E) (arrowS2 E) (arrowP E) 54 (arrowM E) cur) =
      true := by
  decide +kernel

/-! ### The run -/

/-- The state after `let c = ref x`, in which `rd c` is evaluated. -/
def cfg1 (n : Int) : Config := { cfgR n with varEnv := (cfgX n).varEnv.update "c" (.loc 0) }

/-- The state after the call. -/
def cfgC (n : Int) : Config :=
  { cfg1 n with memory := Memory.update (Memory.update ∅ 0 n) 0 (n / 2), nextAddr := 1 }

/-- The call entry. -/
def entryOf (n : Int) : ExternCallEntry :=
  ExternCallEntry.ofRuntime body (cfg1 n) (cfg1 n).varEnv "r" (.loc 0)

/-- The steps: the root, the inner `let`, and the call. -/
def U0 (n : Int) : Step := ⟨K0, prog, 60, cfgX n⟩
def U1 (n : Int) : Step := ⟨K1, inner, 58, cfg1 n⟩
def U2 (n : Int) : Step := ⟨K1, .app rdD (.var "c"), 56, cfg1 n⟩

private theorem run_c (n : Int) : terminatesTo (.var "c") (cfg1 n) (cfg1 n) (.loc 0) :=
  ⟨1, false, by simp [beval, cfg1, VarEnv.lookup, VarEnv.update]⟩

/-- A run of the program from `x = n` returns `n / 2`. -/
theorem run_prog (n : Int) : terminatesTo prog (cfgX n) (cfgF n) (.num (n / 2)) := by
  refine ⟨8, false, ?_⟩
  simp [prog, inner, arg, rdD, beval, cfgX, cfgF, cfgR, freshAddr, VarEnv.lookup,
    VarEnv.update, regC, rdImpl, Memory.lookup, Memory.update, validateExternReturn,
    valueMatchesTyp, readRet, evalOp, List.lookup]

/-! ### Inversion -/

/-- The steps the run reaches: the root, the inner `let`, the call, and steps
    without applications. -/
private inductive InSet (n : Int) : Step → Prop
  | u0 : InSet n (U0 n)
  | u1 : InSet n (U1 n)
  | u2 : InSet n (U2 n)
  | leaf {s : Step} : noApp s.e = true → InSet n s

private theorem inSet_step {n : Int} {s s' : Step} (hs : InSet n s) (h : SubStep s s') :
    InSet n s' := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hokRef, _⟩ := hf
  cases hs with
  | u0 =>
      have hh := SubStep.vlet_inv (ctx := K0) (x := "c") (e1 := arg) (e2 := inner) (F := 60)
        (cfg := cfgX n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = rRef := ok_inj htc (eq_okVal hokRef)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_arg n)
        exact InSet.u1
  | u1 =>
      have hh := SubStep.vlet_inv (ctx := K1) (x := "ret") (e1 := .app rdD (.var "c"))
        (e2 := .ite (.op (.var "ret") .gte (.num 0)) (.deref (.var "c")) (.num 0)) (F := 58)
        (cfg := cfg1 n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩
      · exact InSet.u2
      · exact InSet.leaf rfl
  | u2 =>
      have hh := SubStep.app_inv (ctx := K1) (e1 := rdD) (e2 := .var "c") (F := 56)
        (cfg := cfg1 n) h
      clear h
      obtain ⟨G, _, h⟩ := hh
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩ | h | h
      · exact InSet.leaf rfl
      · exact InSet.leaf rfl
      · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, b, env', st1, st2, p, tcls, tenv, cursor,
          hG, h2, hr2, h1, hr1, _, _, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_c n)
        have := terminatesTo_det hr1 (run_rd _ rfl)
        simp only [Value.closure.injEq] at this
        obtain ⟨_, _, rfl, _⟩ := this
        exact InSet.leaf rfl
      · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, b, pb, env', st1, st2, p, tcls, tenv, cursor,
          hG, h2, hr2, h1, hr1, _⟩ := h
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_c n)
        have := terminatesTo_det hr1 (run_rd _ rfl)
        simp at this
  | leaf hl => exact InSet.leaf (SubStep.noApp h hl)

private theorem inSet_reach {n : Int} {s : Step} (h : Reach (U0 n) s) : InSet n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

/-- The run makes one call, at `rd c`: it is typed against `callRes`, has
    the effect `rdEff`, returns 0 and leaves the state `cfgC n`. -/
private theorem inSet_call {n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet n s) (h : ExternCallAt s effects entry res cf o) :
    effects = [rdEff] ∧ entry = entryOf n ∧ res = callRes ∧ cf = cfgC n ∧ o = .num 0 := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, hok2, hok1, hshape, _⟩ := hf
  cases hs with
  | leaf hl => exact absurd h (ExternCallAt.not_of_reach_noApp hl (Reach.refl _))
  | u0 => cases h
  | u1 => cases h
  | u2 =>
  have hh := ExternCallAt.fn_inv (ctx := K1) (e1 := rdD) (e2 := .var "c") (F := 56)
    (cfg := cfg1 n) h
  clear h
  obtain ⟨G, hG, h⟩ := hh
  obtain rfl : G = 54 := by omega
  rcases h with ⟨c2, c1, v2, x, b, env, hr2, hr1⟩ |
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env, id, argTyp, argPoison, argPred, retSpec, effs,
      captures, memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, implFn, mem',
      addr', h2, hr2, h1, hr1, hety, hthr, _, hregl, _, himpl, hval, rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_c n)
    have := terminatesTo_det hr1 (run_rd _ rfl)
    simp at this
  · obtain rfl : r2 = rArg := ok_inj h2 (eq_okVal hok2)
    obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_c n)
    obtain rfl : r1 = rFun := ok_inj h1 (eq_okVal hok1)
    obtain ⟨rfl, hc⟩ := terminatesTo_det hr1 (run_rd _ rfl)
    simp only [rdD, Value.closure.injEq, Expr.externFn.injEq] at hc
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
    have hE := arrow1_eq hshape
    rw [hE] at hety
    simp only [ETyp.arrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨hm, rfl, happ⟩ := ThreadedAt.single_inv hthr
    have hreg : implFn = rdImpl := by
      have hregl' : regC.get? 8 = some (.fn implFn) := hregl
      rw [regC_get] at hregl'
      simpa using hregl'.symm
    subst hreg
    have hc := himpl.symm.trans (rd_ok _ n)
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    refine ⟨rfl, ?_, (okVal_of_eq happ).symm, rfl, ?_⟩
    · simp only [entryOf, body, ← hm, fExtParts, cur]
    · simpa [validateExternReturn, readRet, valueMatchesTyp] using hval.symm

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet n s) : ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp hl (Reach.refl _) h
  | _ => cases h

/-- The call at `rd c`, built from the computed typing. -/
private theorem call_mk (n : Int) :
    ExternCallAt (U2 n) [rdEff] (entryOf n) callRes (cfgC n) (.num 0) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, hok2, hok1, hshape, _⟩ := hf
  obtain ⟨hm, hap⟩ := call_chain
  have hr1 : terminatesTo rdD { cfg1 n with varEnv := (cfg1 n).varEnv }
      { cfg1 n with varEnv := (cfg1 n).varEnv } (.closure "r" rdD (cfg1 n).varEnv) :=
    run_rd _ rfl
  exact ExternCallAt.fn (vRaw := .num 0) (mem' := Memory.update (Memory.update ∅ 0 n) 0 (n / 2))
    (addr' := 1) (eq_okVal hok2) (run_c n) (eq_okVal hok1) hr1 (arrow1_eq hshape)
    (ThreadedAt.here_of_eq (eq_okVal hap) hm) rfl regC_get rfl (rd_ok _ n)
    (by simp [validateExternReturn, readRet, valueMatchesTyp])

/-- The run reaches the call. -/
private theorem reach_call (n : Int) : Reach (U0 n) (U2 n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hokRef, _⟩ := hf
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (SubStep.vletBody (f := 58) (eq_okVal hokRef) (run_arg n)))
    (SubStep.vletBound (f := 56))

/-! ### The cell -/

/-- The effect `!r` writes the cell at address 0, and the typing of the call
    stores `poisoned { 0 }` for it. -/
theorem cell_found (n : Int) : EffectCell (entryOf n) [rdEff] callRes "r" 0 cellQt := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, hlocs, hcell, _⟩ := hf
  unfold refLocs at hlocs
  split at hlocs
  · rename_i ls _ _ hlk
    simp only [Option.some.injEq] at hlocs
    exact EffectCell.mk (List.mem_singleton_self _) rfl hlk rfl hlocs (isCell_eq hcell)
      (by simp [entryOf, ExternCallEntry.ofRuntime, VarEnv.lookup, VarEnv.update])
  · cases hlocs

/-- The cell `!r` is the only cell the call writes. -/
private theorem cell_inv {n : Int} {v : Name} {addr : Address} {qt : QTyp}
    (h : EffectCell (entryOf n) [rdEff] callRes v addr qt) :
    v = "r" ∧ addr = 0 ∧ qt = cellQt := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, hlocs, hcell, _⟩ := hf
  cases h with
  | @mk ef _ qtv ls l _ _ hef htg hlk hety hls hmem hu =>
    rw [List.mem_singleton] at hef
    subst hef
    simp only [rdEff, EffectTarget.namedVar.injEq] at htg
    subst htg
    have hlk' : body.varEnv.lookup "r" = some qtv := hlk
    rw [hlk'] at hlocs
    obtain ⟨ety, pz, pr⟩ := qtv
    simp only at hety
    subst hety
    simp only [refLocs, Option.some.injEq] at hlocs
    rw [hlocs, List.cons.injEq] at hls
    obtain ⟨rfl, -⟩ := hls
    rw [isCell_eq hcell, Option.some.injEq] at hmem
    simp only [entryOf, ExternCallEntry.ofRuntime, VarEnv.lookup, VarEnv.update,
      List.lookup, beq_self_eq_true, Option.some.injEq, Value.loc.injEq] at hu
    exact ⟨rfl, hu.symm, hmem.symm⟩

private theorem cfgC_cell (n : Int) : (cfgC n).memory.lookup 0 = some (n / 2) := by
  simp [cfgC, Memory.lookup, Memory.update]

/-! ### The premises -/

/-- *Match* holds in every run. -/
theorem match_of (n : Int) (predSat : PredSat)
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog')) :
    ExternCallsMatch predSat (U0 n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, ht, hreg, _, _, hd, _⟩ := hf
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
  refine ⟨(callMatches_of (entry := entryOf n) (cf := cfgC n) hlaws hd ht hreg
    (by decide)).ret, ?_⟩
  intro v addr qt _ hc _ _ _ _ _ _ _ hpred _
  obtain ⟨-, -, rfl⟩ := cell_inv hc
  simp [cellQt] at hpred

/-- *Agreement* for the pair holds exactly when the two runs leave the same
    content in the cell. -/
theorem agree_iff (n₀ n₁ : Int) : ExternCallsAgree (U0 n₀) (U0 n₁) ↔ n₀ / 2 = n₁ / 2 := by
  constructor
  · intro h
    have hf := facts_ok
    simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
    obtain ⟨_, _, _, _, _, ht, hreg, _⟩ := hf
    have hag := h.calls _ _ _ _ _ _ _ _ _ _ (reach_call n₀) (reach_call n₁) rfl rfl rfl (call_mk n₀)
      (call_mk n₁) rfl
    have hmem : (0 : Tag) ∈ callRes.tagLog'.map (·.tag) := by rw [ht]; simp
    obtain ⟨a, ha, hat⟩ := List.mem_map.mp hmem
    exact hag.cells "r" 0 0 cellQt _ _ (cell_found n₀) (cell_found n₁) (cfgC_cell n₀)
      (cfgC_cell n₁) a ha (by rw [hat]; rfl) (by rw [hat]; exact hreg)
  · intro hn
    refine ⟨fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ _ _ _ hc₀ hc₁ _ => ?_⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hr₀) hc₀
    obtain ⟨-, rfl, -, rfl, rfl⟩ := inSet_call (inSet_reach hr₁) hc₁
    refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
    intro v a₀ a₁ qt m₀ m₁ h₀ h₁ hm₀ hm₁ _ _ _ _
    obtain ⟨-, rfl, -⟩ := cell_inv h₀
    obtain ⟨-, rfl, -⟩ := cell_inv h₁
    rw [cfgC_cell, Option.some.injEq] at hm₀ hm₁
    rw [← hm₀, ← hm₁, hn]

/-- The typing and the premises: the typing accepts the program with a clean
    `int`; *match* holds in every run; *agreement* holds for 4, 5 and fails
    for 4, 6. -/
theorem readBack_case :
    typecheck K0 prog 60 = .ok rootRes ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false ∧
    (∀ predSat : PredSat, PredSatLaws predSat (programTable ∅ rootRes.tagLog') →
      ∀ n, ExternCallsMatch predSat (U0 n)) ∧
    PredSatLaws geSat (programTable ∅ rootRes.tagLog') ∧
    ExternCallsAgree (U0 4) (U0 5) ∧
    ¬ ExternCallsAgree (U0 4) (U0 6) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, hall, hety, hpz⟩ := hf
  refine ⟨eq_okVal hp, hety, hpz, fun predSat hlaws n => match_of n predSat hlaws,
    predSatLaws_geSat (geTable_of_allGe hall), (agree_iff 4 5).2 (by decide), ?_⟩
  rw [agree_iff]
  decide

/-! ### The theorem -/

/-- The observation: the returned integer. -/
def obsRet : ObservableSpec := { locs := ∅, retEtyp? := some .int }

private theorem trustedK0 : InitialContextTrusted rdReg prog K0 := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 8 ∧ d = rdDecl := by
        simp only [prog, inner, rdD, arg] at hp
        cases hp with
        | vlet_bound h => cases h with | newRef h' => cases h'
        | vlet_body h =>
            cases h with
            | vlet_bound h =>
                cases h with
                | app_fun h =>
                    cases h with
                    | externFn => exact ⟨rfl, rfl⟩
                    | externFn_return hret => cases hret
                | app_arg h => cases h
            | vlet_body h =>
                cases h with
                | ite_cond h =>
                    cases h with
                    | op_left h => cases h
                    | op_right h => cases h
                | ite_then h => cases h with | deref h => cases h
                | ite_else h => cases h
      obtain ⟨rfl, rfl⟩ := h
      simp [rdReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K0_vars _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

/-- **The theorem at `let c = ref x in let ret = rd c in if ret >= 0 then !c else 0`.**
    Two runs whose calls leave the same content in the cell return the same
    value. -/
theorem same_return (n₀ n₁ : Int) (h : n₀ / 2 = n₁ / 2) {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgX n₀) cf₀ o₀) (hr₁ : terminatesTo prog (cfgX n₁) cf₁ o₁) :
    o₀ = o₁ := by
  obtain ⟨htc, hety, hpz, hmatch, hlaws, _, _⟩ := readBack_case
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness rdReg prog sRd obsRet K0 externRegimeMatchesK0 trustedK0
      wfSpecRd rfl ctxMatchesK0 wfCtxK0 rfl rfl rfl tagBoundedK0 guardCapsK0
      geSat ∅ wfTmK0 tmBoundedK0 lawsEmpty 60 rootRes htc
      (And.intro (fun et h => by
          simp only [obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hety, hpz⟩)
        (fun _ _ h => by simp [obsRet, MemoryETypEnv.lookup] at h))
      hlaws ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ wfRegimeK0 wfθ₀ wfθ₀
      (wfCX n₀) (wfCX n₁) reservedWFC reservedWFC disciplineK0 disciplineK0
      (And.intro (fun h _ => by simp [sRd] at h)
        (fun h _ => by simp [sRd, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sRd] at h)
        (fun h _ => by simp [sRd, VarTypeEnv.lookup] at h))
      (instantiatesK0 n₀) (instantiatesK0 n₁) (trustedInitK0 n₀) (trustedInitK0 n₁)
      consistentK0 consistentK0 (hmatch geSat hlaws n₀) (hmatch geSat hlaws n₁)
      agreeCriticalK0 agreeTrustedK0 ((agree_iff n₀ n₁).2 h) hr₀ hr₁
  exact hobs.2

/-- **The runs from `x = 4` and `x = 5` return the same value.** -/
theorem same_return_4_5 {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgX 4) cf₀ o₀) (hr₁ : terminatesTo prog (cfgX 5) cf₁ o₁) :
    o₀ = o₁ :=
  same_return 4 5 (by decide) hr₀ hr₁

end ReadBack

end Cell

end ExternCallsWitness
