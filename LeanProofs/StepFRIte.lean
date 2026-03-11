/-
  Auto-extracted from FaultRobustnessProofs.lean during StepFR operator refactor.
-/
import LeanProofs.StepFR
import LeanProofs.StepFRApp

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

private def matchGuard_checkNoPredOnArrow (qt : QTyp) : TypecheckM Unit := do
  match qt.etyp with
  | ETyp.arrow _ _ _ _ | ETyp.parrow _ _ _ _ =>
      match qt.pred with
      | Predicate.noPred => pure ()
      | _ => throw "Function types cannot carry predicates in matchGuard"
  | _ => pure ()

/-- Shared predicate matcher from `matchGuard`. -/
private def matchGuard_checkPredicate
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (arg : PExpr) (qt : QTyp)
    (fuel : Nat) :
    TypecheckM (Option (Tag × Deps)) := do
  matchGuard_checkNoPredOnArrow qt
  match qt.pred with
  | Predicate.noPred => return none
  | Predicate.guardOnly _tag => return none
  | Predicate.guardClosure tag arg_name pred_body var_env =>
      -- Use `... = true` conditionals to stay syntactically aligned with the unfolded
      -- `matchGuard` implementation (which often normalizes Bool-ifs this way).
      if PExpr.usesArg arg_name pred_body = true then
        if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, arg)) fuel = true then do
          let deps ← extractDepsFromPred qt.pred fuel
          return some (tag, deps)
        else
          return none
      else
        return none

/-- Var-side matches used by `matchGuard`, expressed via `toList` fold for proof convenience. -/
private def matchGuard_varMatches (conditionPExpr : PExpr) (ctx : TypeContext)
    (fuel : Nat) : List (Tag × Deps) :=
  let sCaptured := VarTypeEnv.toCaptured ctx.varEnv
  VarTypeEnv.foldl [] (fun acc name qt =>
    let arg := PExpr.var name
    match matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel with
    | .ok (some kd) => kd :: acc
    | .ok none => acc
    | .error _ => acc) ctx.varEnv

/-- Single ref-entry transition used by `matchGuard` ref-side matching. -/
private def matchGuard_refStep
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (ctx : TypeContext)
    (acc : List (Tag × Deps)) (entry : Name × QTyp) (fuel : Nat) :
    TypecheckM (List (Tag × Deps)) := do
  let name := entry.1
  let qt := entry.2
  match qt.etyp with
  | ETyp.ref ls =>
      if qt.poison = true then
        pure acc
      else
        if ExtTreeSet.isEmpty ls = true then throw "Reference locset is empty in matchGuard" else
        let arg := PExpr.deref (PExpr.var name)
        let merged? ←
          ls.foldM (init := (none : Option Predicate)) (fun accPred? l => do
            match ctx.memEnv.lookup l with
            | some memQt =>
                matchGuard_checkNoPredOnArrow memQt
                let nextPred :=
                  match accPred? with
                  | none => memQt.pred
                  | some p => joinPredicates p memQt.pred
                pure (some nextPred)
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
        let depsMerged ←
          ls.foldM (init := LocSet.empty) (fun dacc l => do
            match ctx.memEnv.lookup l with
            | some memQt =>
                matchGuard_checkNoPredOnArrow memQt
                let deps ← extractDepsFromPred memQt.pred fuel
                pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
            | none => throw s!"Location {l} not found in memory environment during matchGuard")
        let merged := merged?.getD Predicate.noPred
        match merged with
        | Predicate.guardClosure tag arg_name pred_body var_env =>
            if PExpr.usesArg arg_name pred_body = true then
              if PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                  (some (arg_name, arg)) fuel = true then
                pure ((tag, depsMerged) :: acc)
              else
                pure acc
            else
              pure acc
        | Predicate.guardOnly _ => pure acc
        | Predicate.noPred => pure acc
  | _ => pure acc

/-- Ref-side matches used by `matchGuard`, expressed via `toList` fold for proof convenience. -/
private def matchGuard_refMatches (conditionPExpr : PExpr) (ctx : TypeContext)
    (fuel : Nat) : TypecheckM (List (Tag × Deps)) := do
  let sCaptured := VarTypeEnv.toCaptured ctx.varEnv
  VarTypeEnv.foldlM (init := ([] : List (Tag × Deps)))
    (fun acc name qt => matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel)
    ctx.varEnv

private lemma matchGuard_checkPredicate_ok_some_guardClosure
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (arg : PExpr) (qt : QTyp)
    (fuel : Nat)
    (k : Tag) (deps : Deps)
    (h :
      matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel = .ok (some (k, deps))) :
    ∃ arg_name pred_body var_env,
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  cases hpred : qt.pred with
  | noPred =>
      unfold matchGuard_checkPredicate at h
      have : False := by
        cases hchk : matchGuard_checkNoPredOnArrow qt <;> simp [hchk, hpred] at h
      exact False.elim this
  | guardOnly _ =>
      unfold matchGuard_checkPredicate at h
      have : False := by
        cases hchk : matchGuard_checkNoPredOnArrow qt <;> simp [hchk, hpred] at h
      exact False.elim this
  | guardClosure k' arg_name pred_body var_env =>
      unfold matchGuard_checkPredicate at h
      cases hchk : matchGuard_checkNoPredOnArrow qt with
      | error err =>
          have : False := by
            simp [hchk, hpred] at h
            cases h
          exact False.elim this
      | ok _ =>
          simp [hchk, hpred] at h
          by_cases huses : PExpr.usesArg arg_name pred_body = true
          · simp [huses] at h
            by_cases heqv :
                PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                  (some (arg_name, arg)) fuel = true
            · simp [heqv] at h
              cases hdeps : extractDepsFromPred (Predicate.guardClosure k' arg_name pred_body var_env) fuel with
              | error err =>
                  have : False := by
                    simp [hdeps] at h
                    cases h
                  exact False.elim this
              | ok d =>
                  simp [hdeps] at h
                  cases h
                  exact ⟨arg_name, pred_body, var_env, rfl⟩
            · simp [heqv] at h
          · simp [huses] at h

/-- From `matchGuard = .ok`, recover singleton structure of combined var/ref matches. -/
private lemma matchGuard_ok_allMatches_singleton
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    (conditionPExpr : PExpr)
    (fuel : Nat)
    (hcond : cond.toPExpr = .ok conditionPExpr)
  (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
  ∃ refMatches,
    matchGuard_refMatches conditionPExpr ctx fuel = .ok refMatches ∧
    matchGuard_varMatches conditionPExpr ctx fuel ++ refMatches = [(k, deps)] := by
  let varMatchesRaw : List (Tag × Deps) :=
    VarTypeEnv.foldl []
      (fun acc name qt =>
        let arg := PExpr.var name
        match matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) arg qt fuel with
        | .ok (some (tag, deps)) => (tag, deps) :: acc
        | .ok none => acc
        | .error _ => acc)
      ctx.varEnv
  have hmatch2 :
      (do
        let refMatches ← matchGuard_refMatches conditionPExpr ctx fuel
        match varMatchesRaw ++ refMatches with
        | [(tag, deps)] => pure (tag, deps)
        | [] => throw "No matching guard found for condition"
        | _ =>
            throw s!"Multiple matching guards found for condition: {repr (varMatchesRaw ++ refMatches)}") =
      .ok (k, deps) := by
    simpa [varMatchesRaw, matchGuard, hcond, matchGuard_refMatches, matchGuard_refStep,
      matchGuard_checkPredicate, matchGuard_checkNoPredOnArrow,
      bind, Except.bind] using hmatch
  cases href0 : matchGuard_refMatches conditionPExpr ctx fuel with
  | error err =>
      have hbad : (Except.error err : TypecheckM (Tag × Deps)) = .ok (k, deps) := by
        have htmp := hmatch2
        simp [href0, bind, Except.bind] at htmp
      cases hbad
  | ok refMatches =>
      refine ⟨refMatches, by simp, ?_⟩
      have hsingle_raw : varMatchesRaw ++ refMatches = [(k, deps)] := by
        have hmain :
            (match varMatchesRaw ++ refMatches with
            | [(tag, deps)] => Except.ok (tag, deps)
            | [] => Except.error "No matching guard found for condition"
            | _ =>
                Except.error s!"Multiple matching guards found for condition: {
                  repr (varMatchesRaw ++ refMatches)}")
              = Except.ok (k, deps) := by
          simpa [href0, bind, Except.bind] using hmatch2
        set allMatches : List (Tag × Deps) := varMatchesRaw ++ refMatches
        have hmain' :
            (match allMatches with
            | [(tag, deps)] => Except.ok (tag, deps)
            | [] => Except.error "No matching guard found for condition"
            | _ => Except.error s!"Multiple matching guards found for condition: {repr allMatches}")
              = Except.ok (k, deps) := by
          simpa [allMatches] using hmain
        cases hall : allMatches with
        | nil =>
            have : False := by
              simp [hall] at hmain'
            exact False.elim this
        | cons a as =>
            cases as with
            | nil =>
                have ha : a = (k, deps) := by
                  simpa [hall] using hmain'
                subst ha
                simp
            | cons b bs =>
                have : False := by
                  simp [hall] at hmain'
                exact False.elim this
      have hvarRaw_eq : varMatchesRaw = matchGuard_varMatches conditionPExpr ctx fuel := by
        unfold varMatchesRaw
        unfold matchGuard_varMatches
        refine congrArg (fun f => VarTypeEnv.foldl [] f ctx.varEnv) ?_
        funext acc name qt
        dsimp
        cases hcp :
            matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv)
              (PExpr.var name) qt fuel with
        | error err =>
            simp
        | ok opt =>
            cases opt <;> simp
      simpa [hvarRaw_eq] using hsingle_raw

/-- Singleton append split. -/
private lemma singleton_allMatches_implies_var_or_ref
    (varMatches refMatches : List (Tag × Deps)) (k : Tag) (deps : Deps)
    (hall : varMatches ++ refMatches = [(k, deps)]) :
    (k, deps) ∈ varMatches ∨ (k, deps) ∈ refMatches := by
  have hmem : (k, deps) ∈ varMatches ++ refMatches := by simp [hall]
  exact List.mem_append.mp hmem

private lemma var_match_from_varMatches_aux
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (fuel : Nat) :
    ∀ (entries : List (Name × QTyp)),
      (∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt) →
      ∀ (acc : List (Tag × Deps)),
      (∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) →
      ∀ kd, kd ∈ List.foldl
        (fun acc entry =>
          let name := entry.1
          let qt := entry.2
          let arg := PExpr.var name
          match matchGuard_checkPredicate conditionPExpr sCaptured arg qt fuel with
          | .ok (some kd) => kd :: acc
          | .ok none => acc
          | .error _ => acc) acc entries →
        ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env := by
  intro entries
  induction entries with
  | nil =>
      intro _hentries acc hacc kd hmem
      simpa using hacc kd hmem
  | cons entry entries ih =>
      intro hentries acc hacc kd hmem
      rcases entry with ⟨name, qt⟩
      have hlookup_name : ctx.varEnv.lookup name = some qt := hentries name qt (by simp)
      set acc1 :=
        (match matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel with
        | .ok (some kd) => kd :: acc
        | .ok none => acc
        | .error _ => acc)
      have hacc1 :
          ∀ kd, kd ∈ acc1 →
            ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
              ctx.varEnv.lookup x = some qt ∧
              qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env := by
        intro kd' hmem'
        dsimp [acc1] at hmem'
        cases hcp : matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel with
        | error err =>
            simp [hcp] at hmem'
            exact hacc kd' hmem'
        | ok opt =>
            cases opt with
            | none =>
                simp [hcp] at hmem'
                exact hacc kd' hmem'
            | some kd0 =>
                simp [hcp] at hmem'
                rcases hmem' with hhead | htail
                · subst hhead
                  have hcp' :
                      matchGuard_checkPredicate conditionPExpr sCaptured (PExpr.var name) qt fuel = .ok (some kd') := by
                    simp [hcp]
                  rcases matchGuard_checkPredicate_ok_some_guardClosure
                    conditionPExpr sCaptured (PExpr.var name) qt fuel kd'.1 kd'.2 hcp'
                    with ⟨arg_name, pred_body, var_env, hpred⟩
                  exact ⟨name, qt, arg_name, pred_body, var_env, hlookup_name, hpred⟩
                · exact hacc kd' htail
      have hentries_tail :
          ∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt := by
        intro name' qt' hmem'
        exact hentries name' qt' (List.mem_cons_of_mem _ hmem')
      exact ih hentries_tail acc1 hacc1 kd hmem

/-- Var-side extraction from varMatches membership. -/
private lemma var_match_from_varMatches
    (ctx : TypeContext) (conditionPExpr : PExpr) (k : Tag) (deps : Deps)
    (fuel : Nat)
    (hmem : (k, deps) ∈ matchGuard_varMatches conditionPExpr ctx fuel) :
    ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ctx.varEnv.lookup x = some qt ∧
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold matchGuard_varMatches at hmem
  rw [VarTypeEnv.foldl, Std.ExtTreeMap.foldl_eq_foldl_toList] at hmem
  have hentries_toList :
      ∀ name qt, (name, qt) ∈ ctx.varEnv.toList → ctx.varEnv.lookup name = some qt := by
    intro name qt hmemToList
    have hlookup : ctx.varEnv[name]? = some qt :=
      (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := ctx.varEnv)).1 hmemToList
    simpa [VarTypeEnv.lookup] using hlookup
  have h :=
    var_match_from_varMatches_aux ctx conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) fuel
      ctx.varEnv.toList hentries_toList [] (by intro kd h; cases h) (k, deps) hmem
  simpa using h

private def matchGuard_refPredFoldF (ctx : TypeContext)
    (accPred? : Option Predicate) (l : Loc) : TypecheckM (Option Predicate) := do
  match ctx.memEnv.lookup l with
  | some memQt =>
      matchGuard_checkNoPredOnArrow memQt
      let nextPred :=
        match accPred? with
        | none => memQt.pred
        | some p => joinPredicates p memQt.pred
      pure (some nextPred)
  | none => throw s!"Location {l} not found in memory environment during matchGuard"

private lemma list_foldlM_matchGuard_refPred_eq_guardClosure_from_some
    (ctx : TypeContext) :
    ∀ (xs : List Loc) (p0 : Predicate) (pred? : Option Predicate)
      (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      List.foldlM (matchGuard_refPredFoldF ctx) (some p0) xs = .ok pred? →
      pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
      p0 = Predicate.guardClosure k arg_name pred_body var_env ∧
      (∀ l ∈ xs, ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  induction xs with
  | nil =>
      intro p0 pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      subst hfold
      refine ⟨?_, ?_⟩
      · simpa using hpred
      · intro l hl
        cases hl
  | cons x xs ih =>
      intro p0 pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : matchGuard_refPredFoldF ctx (some p0) x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : ctx.memEnv.lookup x with
          | none =>
              have hlookup' : ctx.memEnv.lookup x = none := hlookup
              have : False := by
                simp [matchGuard_refPredFoldF, hlookup'] at hfx
              exact False.elim this
          | some memQt =>
              have hlookup' : ctx.memEnv.lookup x = some memQt := hlookup
              cases hchk : matchGuard_checkNoPredOnArrow memQt with
              | error err =>
                  have : False := by
                    simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  exact False.elim this
              | ok _ =>
                  simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  cases hfx
                  have htail_fold :
                      List.foldlM (matchGuard_refPredFoldF ctx)
                        (some (joinPredicates p0 memQt.pred)) xs = .ok pred? := by
                    simpa using hfold
                  have hih :=
                    ih (joinPredicates p0 memQt.pred) pred? k arg_name pred_body var_env htail_fold hpred
                  have hjoin :=
                    joinPredicates_eq_guardClosure
                      (p := p0) (q := memQt.pred)
                      (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                      hih.1
                  refine ⟨hjoin.1, ?_⟩
                  intro l hl
                  rcases (List.mem_cons.mp hl) with rfl | hltail
                  · refine ⟨memQt, ?_, hjoin.2⟩
                    simpa [MemoryTypeEnv.lookup] using hlookup
                  · exact hih.2 l hltail

private lemma list_foldlM_matchGuard_refPred_eq_guardClosure
    (ctx : TypeContext) :
    ∀ (xs : List Loc) (pred? : Option Predicate)
      (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      List.foldlM (matchGuard_refPredFoldF ctx) (none : Option Predicate) xs = .ok pred? →
      pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env →
      (∀ l ∈ xs, ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  intro xs
  cases xs with
  | nil =>
      intro pred? k arg_name pred_body var_env _hfold _hpred l hl
      cases hl
  | cons x xs =>
      intro pred? k arg_name pred_body var_env hfold hpred
      simp [List.foldlM_cons, bind, Except.bind] at hfold
      cases hfx : matchGuard_refPredFoldF ctx none x with
      | error err =>
          simp [hfx] at hfold
      | ok acc' =>
          simp [hfx] at hfold
          cases hlookup : ctx.memEnv.lookup x with
          | none =>
              have hlookup' : ctx.memEnv.lookup x = none := hlookup
              have : False := by
                simp [matchGuard_refPredFoldF, hlookup'] at hfx
              exact False.elim this
          | some memQt =>
              have hlookup' : ctx.memEnv.lookup x = some memQt := hlookup
              cases hchk : matchGuard_checkNoPredOnArrow memQt with
              | error err =>
                  have : False := by
                    simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  exact False.elim this
              | ok _ =>
                  simp [matchGuard_refPredFoldF, hlookup', hchk] at hfx
                  cases hfx
                  have htail_fold :
                      List.foldlM (matchGuard_refPredFoldF ctx) (some memQt.pred) xs = .ok pred? := by
                    simpa using hfold
                  have htail :=
                    list_foldlM_matchGuard_refPred_eq_guardClosure_from_some
                      ctx xs memQt.pred pred? k arg_name pred_body var_env htail_fold hpred
                  intro l hl
                  rcases (List.mem_cons.mp hl) with rfl | hltail
                  · refine ⟨memQt, ?_, htail.1⟩
                    simpa [MemoryTypeEnv.lookup] using hlookup
                  · exact htail.2 l hltail

private lemma matchGuard_refPred_foldM_guardClosure
    (ctx : TypeContext) (ls : LocSet) (pred? : Option Predicate)
    (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
    (hfold : LocSet.foldM ls (init := (none : Option Predicate)) (matchGuard_refPredFoldF ctx) = .ok pred?)
    (hpred : pred?.getD Predicate.noPred = Predicate.guardClosure k arg_name pred_body var_env) :
    ∀ l, l ∈ ls →
      ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
        memQt.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  have hlist :=
    list_foldlM_matchGuard_refPred_eq_guardClosure
      ctx ls.toList pred? k arg_name pred_body var_env hfold hpred
  intro l hl
  have hl' : l ∈ ls.toList := by
    simpa using hl
  exact hlist l hl'

private lemma matchGuard_refStep_preserves_invariant
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (name : Name) (qt : QTyp) (acc acc1 : List (Tag × Deps))
    (fuel : Nat)
    (hlookup_name : ctx.varEnv.lookup name = some qt)
    (hacc :
      ∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env))
    (hstep : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .ok acc1) :
    ∀ kd, kd ∈ acc1 →
      ∃ (x : Name) (qt : QTyp) (ls : LocSet)
        (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
        ctx.varEnv.lookup x = some qt ∧
        qt.etyp = ETyp.ref ls ∧
        ls.isEmpty = false ∧
        (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
            memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
  intro kd hmem
  have hstep0 : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .ok acc1 := hstep
  unfold matchGuard_refStep at hstep
  cases hEt : qt.etyp with
  | ref ls =>
      by_cases hpoisonT : qt.poison = true
      · simp [hEt, hpoisonT] at hstep
        cases hstep
        exact hacc kd hmem
      · have hpoisonF : qt.poison = false := by
          cases hq : qt.poison with
          | false =>
              rfl
          | true =>
              simp [hq] at hpoisonT
        by_cases hlsEmptyT : ls.isEmpty = true
        · simp [hEt, hpoisonF, hlsEmptyT] at hstep
        · cases hmerged :
            LocSet.foldM ls (init := (none : Option Predicate))
              (fun accPred? l => do
                match ctx.memEnv.lookup l with
                | some memQt =>
                    matchGuard_checkNoPredOnArrow memQt
                    let nextPred :=
                      match accPred? with
                      | none => memQt.pred
                      | some p => joinPredicates p memQt.pred
                    pure (some nextPred)
                | none => throw s!"Location {l} not found in memory environment during matchGuard") with
          | error err =>
              have hlsEmptyF : ls.isEmpty = false := by
                cases hls : ls.isEmpty with
                | false =>
                    rfl
                | true =>
                    simp [hls] at hlsEmptyT
              have hstepErr :
                  matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .error err := by
                unfold matchGuard_refStep
                try simp [hEt, hpoisonF, hlsEmptyF]
                erw [hmerged]
                simp [bind, Except.bind]
              have : False := by
                rw [hstepErr] at hstep0
                simp at hstep0
              exact False.elim this
          | ok merged? =>
              have hlsEmptyF : ls.isEmpty = false := by
                cases hls : ls.isEmpty with
                | false =>
                    rfl
                | true =>
                    simp [hls] at hlsEmptyT
              cases hdeps :
                  LocSet.foldM ls (init := LocSet.empty) (fun dacc l => do
                    match ctx.memEnv.lookup l with
                    | some memQt =>
                        matchGuard_checkNoPredOnArrow memQt
                        let deps ← extractDepsFromPred memQt.pred fuel
                        pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
                    | none => throw s!"Location {l} not found in memory environment during matchGuard") with
                | error err =>
                  have hstepErr :
                      matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .error err := by
                    unfold matchGuard_refStep
                    -- Simplify outer control-flow first, then rewrite the computed folds.
                    simp [hEt, hpoisonF, hlsEmptyF]
                    erw [hmerged]
                    erw [hdeps]
                    simp [bind, Except.bind]
                  have : False := by
                    rw [hstepErr] at hstep0
                    simp at hstep0
                  exact False.elim this
                | ok depsMerged =>
                  cases hmg : merged?.getD Predicate.noPred with
                  | noPred =>
                      have hacc1eq : acc1 = acc := by
                        have hstep' := hstep0
                        unfold matchGuard_refStep at hstep'
                        simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                        erw [hmerged] at hstep'
                        erw [hdeps] at hstep'
                        simp [bind, Except.bind] at hstep'
                        erw [hmg] at hstep'
                        simp at hstep'
                        cases hstep'
                        rfl
                      subst hacc1eq
                      exact hacc kd hmem
                  | guardOnly gk =>
                      have hacc1eq : acc1 = acc := by
                        have hstep' := hstep0
                        unfold matchGuard_refStep at hstep'
                        simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                        erw [hmerged] at hstep'
                        erw [hdeps] at hstep'
                        simp [bind, Except.bind] at hstep'
                        erw [hmg] at hstep'
                        simp at hstep'
                        cases hstep'
                        rfl
                      subst hacc1eq
                      exact hacc kd hmem
                  | guardClosure tag arg_name pred_body var_env =>
                      by_cases husesT : PExpr.usesArg arg_name pred_body = true
                      · by_cases heqvT :
                          PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                            (some (arg_name, PExpr.deref (PExpr.var name))) fuel = true
                        · have hacc1eq : acc1 = (tag, depsMerged) :: acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            simp [husesT, heqvT] at hstep'
                            cases hstep'
                            rfl
                          subst hacc1eq
                          rcases (List.mem_cons.mp hmem) with hhead | htail
                          · subst hhead
                            refine ⟨name, qt, ls, arg_name, pred_body, var_env, hlookup_name, hEt, hlsEmptyF, ?_⟩
                            have hmerged' :
                                LocSet.foldM ls (init := (none : Option Predicate))
                                  (matchGuard_refPredFoldF ctx) = .ok merged? := by
                              simpa [matchGuard_refPredFoldF] using hmerged
                            have hls :
                                ∀ l, l ∈ ls →
                                  ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                                    memQt.pred =
                                      Predicate.guardClosure tag arg_name pred_body var_env :=
                              matchGuard_refPred_foldM_guardClosure
                                ctx ls merged? tag arg_name pred_body var_env hmerged'
                                (by simp [hmg])
                            exact hls
                          · exact hacc kd htail
                        · have heqvF :
                              PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                (some (arg_name, PExpr.deref (PExpr.var name))) fuel = false := by
                            cases heqv :
                                PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                  (some (arg_name, PExpr.deref (PExpr.var name))) fuel with
                            | false =>
                                rfl
                            | true =>
                                simp [heqv] at heqvT
                          have hacc1eq : acc1 = acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            simp [husesT, heqvF] at hstep'
                            cases hstep'
                            rfl
                          subst hacc1eq
                          exact hacc kd hmem
                      · have husesF : PExpr.usesArg arg_name pred_body = false := by
                          cases huses : PExpr.usesArg arg_name pred_body with
                          | false =>
                              rfl
                          | true =>
                              simp [huses] at husesT
                        have hacc1eq : acc1 = acc := by
                          have hstep' := hstep0
                          unfold matchGuard_refStep at hstep'
                          -- Avoid fragile `rw/erw` matching on folded expressions; `simp` with the
                          -- computed fold equalities is stable under definitional unfolding.
                          simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                          erw [hmerged] at hstep'
                          erw [hdeps] at hstep'
                          simp [bind, Except.bind] at hstep'
                          erw [hmg] at hstep'
                          simp [husesF] at hstep'
                          cases hstep'
                          rfl
                        subst hacc1eq
                        exact hacc kd hmem
    | int =>
        simp [hEt] at hstep
        cases hstep
        exact hacc kd hmem
  | bool =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | unit =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | arrow t1 t2 p1 p2 =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | parrow t1 t2 p1 p2 =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem
  | string =>
      simp [hEt] at hstep
      cases hstep
      exact hacc kd hmem

private lemma ref_match_from_refMatches_aux
    (ctx : TypeContext) (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv)
    (fuel : Nat) :
    ∀ (entries : List (Name × QTyp)),
      (∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt) →
      ∀ (acc : List (Tag × Deps)),
      (∀ kd, kd ∈ acc →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env)) →
      ∀ acc',
        List.foldlM (fun acc entry => matchGuard_refStep conditionPExpr sCaptured ctx acc entry fuel) acc entries =
          .ok acc' →
      ∀ kd, kd ∈ acc' →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
  intro entries
  induction entries with
  | nil =>
      intro _hentries acc hacc acc' hfold kd hmem
      simp [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      simpa using hacc kd hmem
  | cons entry entries ih =>
      intro hentries acc hacc acc' hfold kd hmem
      rcases entry with ⟨name, qt⟩
      have hlookup_name : ctx.varEnv.lookup name = some qt := hentries name qt (by simp)
      cases hstep : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel with
      | error err =>
          simp [List.foldlM_cons, hstep, bind, Except.bind] at hfold
      | ok acc1 =>
          simp [List.foldlM_cons, hstep, bind, Except.bind] at hfold
          have hacc1 :
              ∀ kd, kd ∈ acc1 →
                ∃ (x : Name) (qt : QTyp) (ls : LocSet)
                  (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
                  ctx.varEnv.lookup x = some qt ∧
                  qt.etyp = ETyp.ref ls ∧
                  ls.isEmpty = false ∧
                  (∀ l, l ∈ ls →
                    ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                      memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) := by
            exact
              matchGuard_refStep_preserves_invariant
                ctx conditionPExpr sCaptured name qt acc acc1 fuel hlookup_name hacc hstep
          have hentries_tail :
              ∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt := by
            intro name' qt' hmem'
            exact hentries name' qt' (List.mem_cons_of_mem _ hmem')
          exact ih hentries_tail acc1 hacc1 acc' hfold kd hmem

/-- Ref-side extraction from refMatches membership. -/
private lemma ref_match_from_refMatches
    (ctx : TypeContext) (conditionPExpr : PExpr) (k : Tag) (deps : Deps)
    (refMatches : List (Tag × Deps))
    (fuel : Nat)
    (href : matchGuard_refMatches conditionPExpr ctx fuel = .ok refMatches)
    (hmem : (k, deps) ∈ refMatches) :
    ∃ (x : Name) (qt : QTyp) (ls : LocSet)
      (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ctx.varEnv.lookup x = some qt ∧
      qt.etyp = ETyp.ref ls ∧
      ls.isEmpty = false ∧
      (∀ l, l ∈ ls →
        ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) := by
  unfold matchGuard_refMatches at href
  rw [VarTypeEnv.foldlM, Std.ExtTreeMap.foldlM_eq_foldlM_toList] at href
  cases hfold :
      List.foldlM
        (fun acc entry =>
          matchGuard_refStep conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) ctx acc entry fuel)
        [] ctx.varEnv.toList with
  | error err =>
      simp [hfold] at href
  | ok rms =>
      simp [hfold] at href
      subst href
      exact
        ref_match_from_refMatches_aux ctx conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) fuel
          ctx.varEnv.toList
          (by
            intro name qt hmemToList
            have hlookup : ctx.varEnv[name]? = some qt :=
              (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some (t := ctx.varEnv)).1 hmemToList
            simpa [VarTypeEnv.lookup] using hlookup)
          [] (by intro kd h; cases h) rms hfold (k, deps) hmem

/-- Successful `matchGuard` implies the condition has a pure-expression view. -/
lemma matchGuard_ok_toPExpr?_some
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ conditionPExpr, Expr.toPExpr? cond = some conditionPExpr := by
  cases hcond : cond.toPExpr with
  | error _err =>
      unfold matchGuard at hmatch
      simp [hcond] at hmatch
      cases hmatch
  | ok conditionPExpr =>
      exact ⟨conditionPExpr, Expr_toPExpr?_eq_some_of_toPExpr_ok cond conditionPExpr hcond⟩

lemma qtypCleanUnder_transport_pure_regime_of_toPExpr
    (ctx : TypeContext) (e : Expr) (pe : PExpr) (fuel : Nat) (res : TypeResult)
    (hpe : Expr.toPExpr? e = some pe)
    (htc : typecheckExpr .ioFree { ctx with pureCtx := true } e fuel = .ok res) :
    ∀ qt, qtypCleanUnder ctx.regime qt → qtypCleanUnder res.regime' qt := by
  intro qt hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hreg hnotfun =>
      have hreg' : res.regime'.lookup? k = some true :=
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctx) (e := e) (pe := pe) (fuel := fuel) (res := res)
          hpe htc k true hreg
      exact qtypCleanUnder.guard k htag hreg' hnotfun

lemma runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
    (ctx : TypeContext) (res : TypeResult) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (k : Tag) (deps : Deps)
    (hsub : ∀ l, res.memEnv'.contains l → ctx.memEnv.contains l)
    (hric :
      runtimeInstantiatesCtx
        (ctxAfter { ctx with pureCtx := true } res)
        μ ρ θ) :
    runtimeInstantiatesCtx
      { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩ }
      μ ρ θ := by
  rcases hric with ⟨hmem, hvar⟩
  unfold runtimeInstantiatesCtx
  constructor
  · intro l a hlookup
    rcases hmem l a hlookup with ⟨hcontainsRes, hcontainsMem⟩
    exact ⟨hsub l hcontainsRes, hcontainsMem⟩
  · intro x qt hlookup
    have hlookup' :
        (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
      simpa [ctxAfter] using hlookup
    exact hvar hlookup'

private lemma consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
    (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (kTrue : Tag) (depsTrue : Deps)
    (hreg_bridge :
      ∀ k b, ctx.regime.lookup? k = some b → res.regime'.lookup? k = some b)
    (hmem_bridge :
      ∀ l qt k,
        ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k →
        ctx.regime.lookup? k ≠ none →
        res.memEnv'.lookup l = some qt)
    (hcwr :
      consistentWithRegime predSat
        (ctxAfter { ctx with pureCtx := true } res).regime
        (ctxAfter { ctx with pureCtx := true } res) μ ρ θ) :
    consistentWithRegime predSat
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }) μ ρ θ := by
  unfold consistentWithRegime at hcwr ⊢
  constructor
  · intro l qt k hlookup hguard hRdef
    have hlookupRes : res.memEnv'.lookup l = some qt := hmem_bridge l qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hloc :=
          hcwr.1 l qt k
            (by
              unfold ctxAfter
              exact hlookupRes)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        cases hloc with
        | noPred_ok hpred =>
            exact locsRegime.noPred_ok (l, qt) hpred
        | guardOnly_ok k' hgo =>
            exact locsRegime.guardOnly_ok (l, qt) k' hgo
        | withPred_ok k' arg_name pred_body var_env a n b' hclos hregime hreal hmem hconsist =>
            have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
              simpa using hclos
            have htag_qt : qtypGuardTag qt = some k' := by
              simp [qtypGuardTag, hclos']
            have hkEq : k' = k := by
              have : some k' = some k := by
                calc
                  some k' = qtypGuardTag qt := by symm; exact htag_qt
                  _ = some k := hguard
              exact Option.some.inj this
            have hbEq : b' = b := by
              have : some b' = some b := by
                calc
                  some b' = res.regime'.lookup? k' := hregime.symm
                  _ = res.regime'.lookup? k := by simp [hkEq]
                  _ = some b := hbres
              exact Option.some.inj this
            have hbctx' : ctx.regime.lookup? k' = some b' := by
              calc
                ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                _ = some b := hbctx
                _ = some b' := by simp [hbEq]
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b'
                hclos hbctx' hreal hmem hconsist
  · constructor
    · intro x qt k hlookup hguard hRdef
      cases hbctx : ctx.regime.lookup? k with
      | none =>
          exact False.elim (hRdef hbctx)
      | some b =>
          have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
          have hvar :=
            hcwr.2.1 x qt k
              (by
                unfold ctxAfter
                exact hlookup)
              hguard
              (by
                unfold ctxAfter
                intro hnone
                rw [hbres] at hnone
                contradiction)
          cases hvar with
          | noPred_ok hpred =>
              exact varsRegime.noPred_ok (x, qt) hpred
          | guardOnly_ok k' hgo =>
              exact varsRegime.guardOnly_ok (x, qt) k' hgo
          | withPred_ok k' arg_name pred_body var_env v b' hclos hregime hvarLookup hconsist =>
              have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                simpa using hclos
              have htag_qt : qtypGuardTag qt = some k' := by
                simp [qtypGuardTag, hclos']
              have hkEq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by symm; exact htag_qt
                    _ = some k := hguard
                exact Option.some.inj this
              have hbEq : b' = b := by
                have : some b' = some b := by
                  calc
                    some b' = res.regime'.lookup? k' := hregime.symm
                    _ = res.regime'.lookup? k := by simp [hkEq]
                    _ = some b := hbres
                exact Option.some.inj this
              have hbctx' : ctx.regime.lookup? k' = some b' := by
                calc
                  ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                  _ = some b := hbctx
                  _ = some b' := by simp [hbEq]
              exact
                varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b'
                  hclos hbctx' hvarLookup hconsist
    · intro x qt v hlookup hlookup_v
      have hlookupRes :
          (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
        unfold ctxAfter
        exact hlookup
      have hcapRes :
          closureCapturedVarsRegime predSat
            (ctxAfter { ctx with pureCtx := true } res).regime
            qt μ θ v :=
        hcwr.2.2 x qt v hlookupRes hlookup_v
      exact
        closureCapturedVarsRegime_transport_lookup_back
          (predSat := predSat)
          (R := (ctxAfter { ctx with pureCtx := true } res).regime)
          (R' := ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime)
          (μ := μ)
          (hlookup_back := by
            intro k b hk
            simpa [ctxAfter] using hreg_bridge k b hk)
          hcapRes

theorem consistentWithRegimeMasked_transport_ctxAfter_pure_to_ctx_insert_true
    (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext) (res : TypeResult)
    (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (kTrue : Tag) (depsTrue : Deps)
    (hreg_bridge :
      ∀ k b, ctx.regime.lookup? k = some b → res.regime'.lookup? k = some b)
    (hmem_bridge :
      ∀ l qt k,
        ctx.memEnv.lookup l = some qt →
        qtypGuardTag qt = some k →
        ctx.regime.lookup? k ≠ none →
        res.memEnv'.lookup l = some qt)
    (hcwr :
      consistentWithRegimeMasked masked predSat
        (ctxAfter { ctx with pureCtx := true } res).regime
        (ctxAfter { ctx with pureCtx := true } res) μ ρ θ) :
    consistentWithRegimeMasked masked predSat
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime
      ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }) μ ρ θ := by
  rcases hcwr with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    have hlookupRes : res.memEnv'.lookup l = some qt := hmem_bridge l qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hloc :=
          hlocs l qt k
            (by
              unfold ctxAfter
              exact hlookupRes)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        rcases hloc with hmasked | hloc
        · exact Or.inl hmasked
        · cases hloc with
          | noPred_ok hpred =>
              exact Or.inr (locsRegime.noPred_ok (l, qt) hpred)
          | guardOnly_ok k' hgo =>
              exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hgo)
          | withPred_ok k' arg_name pred_body var_env a n b' hclos hregime hreal hmem hconsist =>
              have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                simpa using hclos
              have htag_qt : qtypGuardTag qt = some k' := by
                simp [qtypGuardTag, hclos']
              have hkEq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by symm; exact htag_qt
                    _ = some k := hguard
                exact Option.some.inj this
              have hbEq : b' = b := by
                have : some b' = some b := by
                  calc
                    some b' = res.regime'.lookup? k' := hregime.symm
                    _ = res.regime'.lookup? k := by simp [hkEq]
                    _ = some b := hbres
                exact Option.some.inj this
              have hbctx' : ctx.regime.lookup? k' = some b' := by
                calc
                  ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                  _ = some b := hbctx
                  _ = some b' := by simp [hbEq]
              exact Or.inr <|
                locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b'
                  hclos hbctx' hreal hmem hconsist
  · intro x qt k hlookup hguard hRdef
    cases hbctx : ctx.regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hbctx)
    | some b =>
        have hbres : res.regime'.lookup? k = some b := hreg_bridge k b hbctx
        have hvar :=
          hvars x qt k
            (by
              unfold ctxAfter
              exact hlookup)
            hguard
            (by
              unfold ctxAfter
              intro hnone
              rw [hbres] at hnone
              contradiction)
        rcases hvar with hmasked | hvar
        · exact Or.inl hmasked
        · cases hvar with
          | noPred_ok hpred =>
              exact Or.inr (varsRegime.noPred_ok (x, qt) hpred)
          | guardOnly_ok k' hgo =>
              exact Or.inr (varsRegime.guardOnly_ok (x, qt) k' hgo)
          | withPred_ok k' arg_name pred_body var_env v b' hclos hregime hvarLookup hconsist =>
              have hclos' : qt.pred = Predicate.guardClosure k' arg_name pred_body var_env := by
                simpa using hclos
              have htag_qt : qtypGuardTag qt = some k' := by
                simp [qtypGuardTag, hclos']
              have hkEq : k' = k := by
                have : some k' = some k := by
                  calc
                    some k' = qtypGuardTag qt := by symm; exact htag_qt
                    _ = some k := hguard
                exact Option.some.inj this
              have hbEq : b' = b := by
                have : some b' = some b := by
                  calc
                    some b' = res.regime'.lookup? k' := hregime.symm
                    _ = res.regime'.lookup? k := by simp [hkEq]
                    _ = some b := hbres
                exact Option.some.inj this
              have hbctx' : ctx.regime.lookup? k' = some b' := by
                calc
                  ctx.regime.lookup? k' = ctx.regime.lookup? k := by simp [hkEq]
                  _ = some b := hbctx
                  _ = some b' := by simp [hbEq]
              exact Or.inr <|
                varsRegime.withPred_ok (x, qt) k' arg_name pred_body var_env v b'
                  hclos hbctx' hvarLookup hconsist
  · intro x qt v hlookup hlookup_v
    have hlookupRes :
        (ctxAfter { ctx with pureCtx := true } res).varEnv.lookup x = some qt := by
      unfold ctxAfter
      exact hlookup
    have hcapRes :
        closureCapturedVarsRegimeMasked masked predSat
          (ctxAfter { ctx with pureCtx := true } res).regime
          qt μ θ v :=
      hclos x qt v hlookupRes hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter { ctx with pureCtx := true } res).regime)
        (R' := ({ ctx with tagEnv := ctx.tagEnv.insert kTrue ⟨true, depsTrue⟩ }).regime)
        (μ := μ)
        (hlookup_back := by
          intro k b hk
          simpa [ctxAfter] using hreg_bridge k b hk)
        hcapRes

private lemma joinMemEnvs_lookup_guardClosure_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hleft := joinMemEnvs_lookup_eq_left_of_right_none env1 env2 l hcontains1
      (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none)
    rw [hlookup_join] at hleft
    have hq : qt = qt1 := by simpa [hlookup1] using hleft
    simpa [hq] using hpred_join
  · rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have _ht12 : t1 = t2 := by simpa using hetyp_eq
            have hjoin_lookup_get :
                (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                some ⟨qt.poison, qt.pred⟩ := by
              have hget := memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
              simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hget
            have hmatch : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) = some ⟨qt.poison, qt.pred⟩ := by
              have h : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                  f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) := by
                cases hopt : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) with
                | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
                | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
              rw [← h]
              exact hjoin_lookup_get
            rw [he1, he2] at hmatch
            simp only [f] at hmatch
            have hpred_joined : qt.pred = joinPredicates pred1 pred2 := by
              exact (MemEntry.mk.inj (Option.some.inj hmatch.symm)).2
            have hpred_eq : joinPredicates pred1 pred2 = Predicate.guardClosure k arg_name pred_body var_env := by
              calc
                joinPredicates pred1 pred2 = qt.pred := hpred_joined.symm
                _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_join
            exact (joinPredicates_eq_guardClosure (p := pred1) (q := pred2) hpred_eq).1

private lemma joinMemEnvs_lookup_guardClosure_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hright := joinMemEnvs_lookup_eq_right_of_left_none env1 env2 l
      (by simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none) hcontains2
    rw [hlookup_join] at hright
    have hq : qt = qt2 := by simpa [hlookup2] using hright
    simpa [hq] using hpred_join
  · rcases Option.ne_none_iff_exists'.1 hlookup1_none with ⟨qt1, hlookup1⟩
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    classical
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have he1 := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hetyp_eq : qt1.etyp = qt2.etyp := by
      rw [memEnv_lookup_etyp_int env1 l qt1 hlookup1, memEnv_lookup_etyp_int env2 l qt2 hlookup2]
    cases qt1 with
    | mk t1 p1 pred1 =>
        cases qt2 with
        | mk t2 p2 pred2 =>
            have _ht12 : t1 = t2 := by simpa using hetyp_eq
            have hjoin_lookup_get :
                (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                some ⟨qt.poison, qt.pred⟩ := by
              have hget := memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
              simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hget
            have hmatch : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) = some ⟨qt.poison, qt.pred⟩ := by
              have h : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups ({} : MemoryTypeEnv))[l]? =
                  f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) := by
                cases hopt : f l (ExtTreeMap.get? env1 l) (ExtTreeMap.get? env2 l) with
                | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
                | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
              rw [← h]
              exact hjoin_lookup_get
            rw [he1, he2] at hmatch
            simp only [f] at hmatch
            have hpred_joined : qt.pred = joinPredicates pred1 pred2 := by
              exact (MemEntry.mk.inj (Option.some.inj hmatch.symm)).2
            have hpred_eq : joinPredicates pred1 pred2 = Predicate.guardClosure k arg_name pred_body var_env := by
              calc
                joinPredicates pred1 pred2 = qt.pred := hpred_joined.symm
                _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_join
            exact (joinPredicates_eq_guardClosure (p := pred1) (q := pred2) hpred_eq).2

private lemma joinMemEnvsStrong_lookup_guardClosure_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hleft :=
      joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    rw [hlookup_join] at hleft
    have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
      simpa [hlookup1] using hleft
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact
      joinMemEnvs_lookup_guardClosure_left
        env1 env2 l qt qt1 k arg_name pred_body var_env
        hlookupW hlookup1 hpred_join

private lemma joinMemEnvsStrong_lookup_guardClosure_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hright :=
      joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    rw [hlookup_join] at hright
    have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
      simpa [hlookup2] using hright
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 hlookup1_none with ⟨qt1, hlookup1⟩
    have hlookupW : (joinMemEnvs env1 env2).lookup l = some qt := by
      rw [← joinMemEnvsStrong_lookup_eq_joinMemEnvs_of_both_lookup env1 env2 l qt1 qt2 hlookup1 hlookup2]
      exact hlookup_join
    exact
      joinMemEnvs_lookup_guardClosure_right
        env1 env2 l qt qt2 k arg_name pred_body var_env
        hlookupW hlookup2 hpred_join

private lemma joinMemEnvsStrong_lookup_guardClosure_implies_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt1, env1.lookup l = some qt1 ∧ qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases h1none : env1.lookup l = none
  · have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
      memEnv_contains_of_lookup_some (env := (joinMemEnvsStrong env1 env2)) (l := l) (qt := qt) hlookup_join
    have hor := joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join
    have hnot1 : ¬ env1.contains l := by
      intro hcontains1
      rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
      rw [hlookup1] at h1none
      cases h1none
    have hcontains2 : env2.contains l := by
      cases hor with
      | inl hcontains1 => exact (hnot1 hcontains1).elim
      | inr hcontains2 => exact hcontains2
    rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
    have h1none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h1none
    have hright :=
      joinMemEnvsStrong_lookup_eq_right_of_left_none env1 env2 l h1none_get hcontains2
    rw [hlookup_join] at hright
    have hq : qt = ⟨qt2.etyp, qt2.poison, Predicate.noPred⟩ := by
      simpa [hlookup2] using hright
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 h1none with ⟨qt1, hlookup1⟩
    exact ⟨qt1, hlookup1,
      joinMemEnvsStrong_lookup_guardClosure_left
        env1 env2 l qt qt1 k arg_name pred_body var_env
        hlookup_join hlookup1 hpred_join⟩

private lemma joinMemEnvsStrong_lookup_guardClosure_implies_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvsStrong env1 env2).lookup l = some qt)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt2, env2.lookup l = some qt2 ∧ qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases h2none : env2.lookup l = none
  · have hcontains_join : (joinMemEnvsStrong env1 env2).contains l :=
      memEnv_contains_of_lookup_some (env := (joinMemEnvsStrong env1 env2)) (l := l) (qt := qt) hlookup_join
    have hor := joinMemEnvsStrong_contains_implies_or env1 env2 l hcontains_join
    have hnot2 : ¬ env2.contains l := by
      intro hcontains2
      rcases memEnv_lookup_some_of_contains env2 l hcontains2 with ⟨qt2, hlookup2⟩
      rw [hlookup2] at h2none
      cases h2none
    have hcontains1 : env1.contains l := by
      cases hor with
      | inl hcontains1 => exact hcontains1
      | inr hcontains2 => exact (hnot2 hcontains2).elim
    rcases memEnv_lookup_some_of_contains env1 l hcontains1 with ⟨qt1, hlookup1⟩
    have h2none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using h2none
    have hleft :=
      joinMemEnvsStrong_lookup_eq_left_of_right_none env1 env2 l hcontains1 h2none_get
    rw [hlookup_join] at hleft
    have hq : qt = ⟨qt1.etyp, qt1.poison, Predicate.noPred⟩ := by
      simpa [hlookup1] using hleft
    have : False := by
      simp [hq] at hpred_join
    exact False.elim this
  · rcases Option.ne_none_iff_exists'.1 h2none with ⟨qt2, hlookup2⟩
    exact ⟨qt2, hlookup2,
      joinMemEnvsStrong_lookup_guardClosure_right
        env1 env2 l qt qt2 k arg_name pred_body var_env
        hlookup_join hlookup2 hpred_join⟩

private lemma consistentWithRegime_join_from_left
  (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegime predSat
      (ctxAfter ctx resLeft).regime
      (ctxAfter ctx resLeft) μ ρ θ) :
  consistentWithRegime predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx resLeft).regime.lookup? k = some b := by
    intro k b hk
    have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
      simpa [ctxAfter, hregime] using hk
    simpa [ctxAfter] using
      joinRegimes_lookup_some_left resLeft.regime' resRight.regime' k b hk'
  unfold consistentWithRegime at hcwr ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact locsRegime.guardOnly_ok (l, qt) k' hpred
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinMemEnvsStrong_lookup_guardClosure_implies_left
              resLeft.memEnv' resRight.memEnv' l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtLeft, hlookupLeft, hpredLeft⟩
        have hRdef_left : (ctxAfter ctx resLeft).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_left : (ctxAfter ctx resLeft).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_left] at hnone
              contradiction
        have hguard_left : qtypGuardTag qtLeft = some k' := by
          simp [qtypGuardTag, hpredLeft]
        have hloc_left :=
          hcwr.1 l qtLeft k'
            (by simpa [ctxAfter] using hlookupLeft)
            hguard_left
            hRdef_left
        cases hloc_left with
        | noPred_ok hnp =>
            simp [qtypGuardTag, hpredLeft] at hnp
        | guardOnly_ok _ hgo =>
            simp [hpredLeft] at hgo
        | withPred_ok kLeft arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
            have hpred_ctor_eq :
                Predicate.guardClosure kLeft arg_name' pred_body' var_env' =
                  Predicate.guardClosure k' arg_name pred_body var_env := by
              calc
                Predicate.guardClosure kLeft arg_name' pred_body' var_env' = qtLeft.pred := by
                  simpa using hclos.symm
                _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredLeft
            cases hpred_ctor_eq
            have hpred_eq : qtLeft.pred = qt.pred := by
              simp [hpredLeft, hpred]
            have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
              cases hkres : (ctxAfter ctx res).regime.lookup? k' with
              | none =>
                  exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
              | some b' =>
                  have hk_left : (ctxAfter ctx resLeft).regime.lookup? k' = some b' :=
                    hlookup_back k' b' hkres
                  have hb_eq : b = b' := by
                    have : some b = some b' := by
                      calc
                        some b = (ctxAfter ctx resLeft).regime.lookup? k' := by symm; exact hreg
                        _ = some b' := hk_left
                    exact Option.some.inj this
                  exact congrArg some hb_eq.symm
            have hcons_res :
                (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
              refine ⟨?_, ?_⟩
              · intro hb
                exact
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := qtLeft) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
              · intro hb
                exact
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := qtLeft) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_left : (ctxAfter ctx resLeft).regime.lookup? k ≠ none := by
          intro hnone
          have hk_left := hlookup_back k b hkres
          rw [hk_left] at hnone
          contradiction
        have hvar_left :=
          hcwr.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_left
        exact
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter ctx resLeft).regime)
            (R' := (ctxAfter ctx res).regime)
            (μ := μ) (ρ := ρ) (entry := (x, qt))
            hlookup_back hguard hkres hvar_left
  · intro x qt v hlookup hlookup_v
    have hcap_left :
        closureCapturedVarsRegime predSat
          (ctxAfter ctx resLeft).regime
          qt μ θ v :=
      hcwr.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegime_transport_lookup_back
        (predSat := predSat)
        (R := (ctxAfter ctx resLeft).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_left

private lemma consistentWithRegime_join_from_right
  (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegime predSat
      (ctxAfter ctx resRight).regime
      (ctxAfter ctx resRight) μ ρ θ) :
  consistentWithRegime predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx resRight).regime.lookup? k = some b := by
    intro k b hk
    have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
      simpa [ctxAfter, hregime] using hk
    simpa [ctxAfter] using
      joinRegimes_lookup_some_right resLeft.regime' resRight.regime' k b hk'
  unfold consistentWithRegime at hcwr ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact locsRegime.guardOnly_ok (l, qt) k' hpred
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinMemEnvsStrong_lookup_guardClosure_implies_right
              resLeft.memEnv' resRight.memEnv' l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtRight, hlookupRight, hpredRight⟩
        have hRdef_right : (ctxAfter ctx resRight).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_right : (ctxAfter ctx resRight).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_right] at hnone
              contradiction
        have hguard_right : qtypGuardTag qtRight = some k' := by
          simp [qtypGuardTag, hpredRight]
        have hloc_right :=
          hcwr.1 l qtRight k'
            (by simpa [ctxAfter] using hlookupRight)
            hguard_right
            hRdef_right
        cases hloc_right with
        | noPred_ok hnp =>
            simp [qtypGuardTag, hpredRight] at hnp
        | guardOnly_ok _ hgo =>
            simp [hpredRight] at hgo
        | withPred_ok kRight arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
            have hpred_ctor_eq :
                Predicate.guardClosure kRight arg_name' pred_body' var_env' =
                  Predicate.guardClosure k' arg_name pred_body var_env := by
              calc
                Predicate.guardClosure kRight arg_name' pred_body' var_env' = qtRight.pred := by
                  simpa using hclos.symm
                _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredRight
            cases hpred_ctor_eq
            have hpred_eq : qtRight.pred = qt.pred := by
              simp [hpredRight, hpred]
            have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
              cases hkres : (ctxAfter ctx res).regime.lookup? k' with
              | none =>
                  exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
              | some b' =>
                  have hk_right : (ctxAfter ctx resRight).regime.lookup? k' = some b' :=
                    hlookup_back k' b' hkres
                  have hb_eq : b = b' := by
                    have : some b = some b' := by
                      calc
                        some b = (ctxAfter ctx resRight).regime.lookup? k' := by symm; exact hreg
                        _ = some b' := hk_right
                    exact Option.some.inj this
                  exact congrArg some hb_eq.symm
            have hcons_res :
                (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
              refine ⟨?_, ?_⟩
              · intro hb
                exact
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := qtRight) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
              · intro hb
                exact
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := qtRight) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_right : (ctxAfter ctx resRight).regime.lookup? k ≠ none := by
          intro hnone
          have hk_right := hlookup_back k b hkres
          rw [hk_right] at hnone
          contradiction
        have hvar_right :=
          hcwr.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_right
        exact
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter ctx resRight).regime)
            (R' := (ctxAfter ctx res).regime)
            (μ := μ) (ρ := ρ) (entry := (x, qt))
            hlookup_back hguard hkres hvar_right
  · intro x qt v hlookup hlookup_v
    have hcap_right :
        closureCapturedVarsRegime predSat
          (ctxAfter ctx resRight).regime
          qt μ θ v :=
      hcwr.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegime_transport_lookup_back
        (predSat := predSat)
        (R := (ctxAfter ctx resRight).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_right

private lemma ite_join_transport_runtimeInstantiatesCtx
  (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (h_mem : ∀ l, first.memEnv'.contains l → res.memEnv'.contains l)
  (h_first : runtimeInstantiatesCtx (ctxAfter ctx first) μ ρ θ) :
  runtimeInstantiatesCtx (ctxAfter ctx res) μ ρ θ := by
  unfold runtimeInstantiatesCtx at h_first ⊢
  simp only [ctxAfter]
  constructor
  · intro l a hθ
    have ⟨hcontains, hμ⟩ := h_first.1 l a hθ
    exact ⟨h_mem l hcontains, hμ⟩
  · exact h_first.2

private lemma ite_qtypCleanUnder_lookup_true_back
    {R R' : Regime}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    {qt : QTyp} :
    qtypCleanUnder R' qt → qtypCleanUnder R qt := by
  intro hclean
  cases hclean with
  | clean hpoison =>
      exact qtypCleanUnder.clean hpoison
  | guard k htag hk hnotfun =>
      exact qtypCleanUnder.guard k htag (hlookup_true_back k hk) hnotfun

private lemma ite_agreeValueUnder_clean_transport_by_lookupTrueBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value}
    (hlookup_true_back : ∀ (k : Tag), R'.lookup? k = some true → R.lookup? k = some true)
    (hmemberVars₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₀ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₀ σcap ρcap)
    (hmemberCvcr₀_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₀ θ₀ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₀ θ₀ σcap ρcap)
    (hmemberVars₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberVarsRegimeEvidence predSat R μ₁ σcap ρcap →
          MemberVarsRegimeEvidence predSat R' μ₁ σcap ρcap)
    (hmemberCvcr₁_transport :
      ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
        MemberCvcrEvidence predSat R μ₁ θ₁ σcap ρcap →
          MemberCvcrEvidence predSat R' μ₁ θ₁ σcap ρcap) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
  have h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt := by
    intro qt' hclean'
    exact ite_qtypCleanUnder_lookup_true_back hlookup_true_back hclean'
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      h_clean_back
      hmemberVars₀_transport hmemberCvcr₀_transport
      hmemberVars₁_transport hmemberCvcr₁_transport
      hclean hagree

private lemma ite_join_transport_agreeOnClean_from_member
  (predSat : PredSat) (ctx : TypeContext)
  (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src :
    agreeOnClean predSat (ctxAfter ctx src).regime (ctxAfter ctx src)
      μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁)
  (h_clean_res_to_src :
    ∀ qt,
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      qtypCleanUnder (ctxAfter ctx src).regime qt)
  (h_mem_from_src_or_unrealized :
    ∀ l qt,
      (ctxAfter ctx res).memEnv.lookup l = some qt →
      qtypCleanUnder (ctxAfter ctx res).regime qt →
      ((∃ qt_src,
          (ctxAfter ctx src).memEnv.lookup l = some qt_src ∧
          qtypCleanUnder (ctxAfter ctx src).regime qt_src ∧
          qt.etyp = qt_src.etyp ∧
          (qt.poison = false → qt_src.poison = false)) ∨
        (θ₀.lookup l = none ∧ θ₁.lookup l = none)))
  (hmemberVars₀_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberVarsRegimeEvidence predSat src.regime' μ₀ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₀ σcap ρcap)
  (hmemberCvcr₀_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberCvcrEvidence predSat src.regime' μ₀ θ₀ σcap ρcap →
        MemberCvcrEvidence predSat res.regime' μ₀ θ₀ σcap ρcap)
  (hmemberVars₁_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberVarsRegimeEvidence predSat src.regime' μ₁ σcap ρcap →
        MemberVarsRegimeEvidence predSat res.regime' μ₁ σcap ρcap)
  (hmemberCvcr₁_transport :
    ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
      MemberCvcrEvidence predSat src.regime' μ₁ θ₁ σcap ρcap →
        MemberCvcrEvidence predSat res.regime' μ₁ θ₁ σcap ρcap) :
  agreeOnClean predSat (ctxAfter ctx res).regime (ctxAfter ctx res)
    μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  simp only [agreeOnClean, ctxAfter]
  have hlookup_true_back :
      ∀ (k : Tag),
        (ctxAfter ctx res).regime.lookup? k = some true →
        (ctxAfter ctx src).regime.lookup? k = some true := by
    intro k hk
    let qtWitness : QTyp := ⟨ETyp.int, true, Predicate.guardOnly k⟩
    have hclean_res_witness :
        qtypCleanUnder (ctxAfter ctx res).regime qtWitness :=
      qtypCleanUnder.guard k (by simp [qtWitness, qtypGuardTag]) hk
        (by simp [qtWitness, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    have hclean_src_witness :
        qtypCleanUnder (ctxAfter ctx src).regime qtWitness :=
      h_clean_res_to_src qtWitness hclean_res_witness
    cases hclean_src_witness with
    | clean hpoison =>
        simp [qtWitness] at hpoison
    | guard k' htag_src hk_src _ =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qtWitness := by symm; exact htag_src
              _ = some k := by simp [qtWitness, qtypGuardTag]
          exact Option.some.inj this
        simpa [hk_eq] using hk_src
  constructor
  · intro l qt hlookup hclean
    rcases h_mem_from_src_or_unrealized l qt hlookup hclean with hlookup_src | hunrealized
    · rcases hlookup_src with ⟨qt_src, hlookup_src, hclean_src, hetyp_eq, hpoison_imp⟩
      have hloc_agree_src := h_src.1 l qt_src hlookup_src hclean_src
      cases hloc_agree_src with
      | both_unrealized _ _ hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values _ _ a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree =>
          have hagree_src_qt :
              agreeValueUnder predSat src.regime' μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_transport_clean
              (predSat := predSat)
              (R := src.regime')
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              (qt := qt) (qt2 := qt_src)
              (o₀ := Value.num n₀) (o₁ := Value.num n₁)
              (h_clean_res_to_src qt hclean) hetyp_eq hpoison_imp hagree
          have hagree' :
              agreeValueUnder predSat res.regime' μ₀ μ₁ θ₀ θ₁ qt (Value.num n₀) (Value.num n₁) :=
            ite_agreeValueUnder_clean_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := src.regime') (R' := res.regime')
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              (qt := qt) (v₀ := Value.num n₀) (v₁ := Value.num n₁)
              hlookup_true_back
              hmemberVars₀_transport hmemberCvcr₀_transport
              hmemberVars₁_transport hmemberCvcr₁_transport
              hclean hagree_src_qt
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagree'
    · exact agreeLocUnder.both_unrealized l qt hunrealized.1 hunrealized.2
  · intro x qt hlookup hclean
    have hclean_src : qtypCleanUnder src.regime' qt :=
      h_clean_res_to_src qt hclean
    have hagree_src := h_src.2 x qt hlookup hclean_src
    cases hagree_src with
    | both_none _ _ hnone₀ hnone₁ =>
        exact agreeVarUnder.both_none x qt hnone₀ hnone₁
    | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagree =>
        have hagree' :
            agreeValueUnder predSat res.regime' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ :=
          ite_agreeValueUnder_clean_transport_by_lookupTrueBack
            (predSat := predSat)
            (R := src.regime') (R' := res.regime')
            (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
            (qt := qt) (v₀ := v₀) (v₁ := v₁)
            hlookup_true_back
            hmemberVars₀_transport hmemberCvcr₀_transport
            hmemberVars₁_transport hmemberCvcr₁_transport
            hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'

theorem consistentWithRegimeMasked_join_from_left
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegimeMasked masked predSat
      (ctxAfter ctx resLeft).regime
      (ctxAfter ctx resLeft) μ ρ θ) :
  consistentWithRegimeMasked masked predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx resLeft).regime.lookup? k = some b := by
    intro k b hk
    have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
      simpa [ctxAfter, hregime] using hk
    simpa [ctxAfter] using
      joinRegimes_lookup_some_left resLeft.regime' resRight.regime' k b hk'
  rcases hcwr with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hpred)
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinMemEnvsStrong_lookup_guardClosure_implies_left
              resLeft.memEnv' resRight.memEnv' l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtLeft, hlookupLeft, hpredLeft⟩
        have hRdef_left : (ctxAfter ctx resLeft).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_left : (ctxAfter ctx resLeft).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_left] at hnone
              contradiction
        have hguard_left : qtypGuardTag qtLeft = some k' := by
          simp [qtypGuardTag, hpredLeft]
        have hloc_left :=
          hlocs l qtLeft k'
            (by simpa [ctxAfter] using hlookupLeft)
            hguard_left
            hRdef_left
        rcases hloc_left with hmasked | hloc_left
        · exact Or.inl (by simpa [hk_eq] using hmasked)
        · cases hloc_left with
          | noPred_ok hnp =>
              simp [qtypGuardTag, hpredLeft] at hnp
          | guardOnly_ok _ hgo =>
              simp [hpredLeft] at hgo
          | withPred_ok kLeft arg_name' pred_body' var_env' a n b hclos_left hreg hreal hmem hcons =>
              have hpred_ctor_eq :
                  Predicate.guardClosure kLeft arg_name' pred_body' var_env' =
                    Predicate.guardClosure k' arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure kLeft arg_name' pred_body' var_env' = qtLeft.pred := by
                    simpa using hclos_left.symm
                  _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredLeft
              cases hpred_ctor_eq
              have hpred_eq : qtLeft.pred = qt.pred := by
                simp [hpredLeft, hpred]
              have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
                cases hkres : (ctxAfter ctx res).regime.lookup? k' with
                | none =>
                    exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
                | some b' =>
                    have hk_left : (ctxAfter ctx resLeft).regime.lookup? k' = some b' :=
                      hlookup_back k' b' hkres
                    have hb_eq : b = b' := by
                      have : some b = some b' := by
                        calc
                          some b = (ctxAfter ctx resLeft).regime.lookup? k' := by symm; exact hreg
                          _ = some b' := hk_left
                      exact Option.some.inj this
                    exact congrArg some hb_eq.symm
              have hcons_res :
                  (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                  (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
                refine ⟨?_, ?_⟩
                · intro hb
                  exact
                    qtypPredHolds_transport_pred
                      (predSat := predSat) (qt := qtLeft) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
                · intro hb
                  exact
                    qtypPredHolds_transport_pred_not
                      (predSat := predSat) (qt := qtLeft) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
              exact Or.inr <|
                locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                  hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hkres)
    | some b =>
        have hRdef_left : (ctxAfter ctx resLeft).regime.lookup? k ≠ none := by
          intro hnone
          have hk_left := hlookup_back k b hkres
          rw [hk_left] at hnone
          contradiction
        have hvar_left :=
          hvars x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_left
        rcases hvar_left with hmasked | hvar_left
        · exact Or.inl hmasked
        · exact Or.inr <|
            varsRegime_transport_active_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx resLeft).regime)
              (R' := (ctxAfter ctx res).regime)
              (μ := μ) (ρ := ρ) (entry := (x, qt))
              hlookup_back hguard hkres hvar_left
  · intro x qt v hlookup hlookup_v
    have hcap_left :
        closureCapturedVarsRegimeMasked masked predSat
          (ctxAfter ctx resLeft).regime
          qt μ θ v :=
      hclos x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter ctx resLeft).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_left

theorem consistentWithRegimeMasked_join_from_right
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext)
  (resLeft resRight res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong resLeft.memEnv' resRight.memEnv')
  (hregime : res.regime' = joinRegimes resLeft.regime' resRight.regime')
  (hcwr :
    consistentWithRegimeMasked masked predSat
      (ctxAfter ctx resRight).regime
      (ctxAfter ctx resRight) μ ρ θ) :
  consistentWithRegimeMasked masked predSat
    (ctxAfter ctx res).regime
    (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx resRight).regime.lookup? k = some b := by
    intro k b hk
    have hk' : (joinRegimes resLeft.regime' resRight.regime').lookup? k = some b := by
      simpa [ctxAfter, hregime] using hk
    simpa [ctxAfter] using
      joinRegimes_lookup_some_right resLeft.regime' resRight.regime' k b hk'
  rcases hcwr with ⟨hlocs, hvars, hclos⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred] at hguard
    | guardOnly k' =>
        exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hpred)
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinMemEnvsStrong_lookup_guardClosure_implies_right
              resLeft.memEnv' resRight.memEnv' l qt k' arg_name pred_body var_env
              (by simpa [ctxAfter, hmemEnv] using hlookup)
              hpred
          with ⟨qtRight, hlookupRight, hpredRight⟩
        have hRdef_right : (ctxAfter ctx resRight).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [ctxAfter, hk_eq] using hkres)
          | some b =>
              have hk_right : (ctxAfter ctx resRight).regime.lookup? k' = some b :=
                hlookup_back k' b hkres
              rw [hk_right] at hnone
              contradiction
        have hguard_right : qtypGuardTag qtRight = some k' := by
          simp [qtypGuardTag, hpredRight]
        have hloc_right :=
          hlocs l qtRight k'
            (by simpa [ctxAfter] using hlookupRight)
            hguard_right
            hRdef_right
        rcases hloc_right with hmasked | hloc_right
        · exact Or.inl (by simpa [hk_eq] using hmasked)
        · cases hloc_right with
          | noPred_ok hnp =>
              simp [qtypGuardTag, hpredRight] at hnp
          | guardOnly_ok _ hgo =>
              simp [hpredRight] at hgo
          | withPred_ok kRight arg_name' pred_body' var_env' a n b hclos_right hreg hreal hmem hcons =>
              have hpred_ctor_eq :
                  Predicate.guardClosure kRight arg_name' pred_body' var_env' =
                    Predicate.guardClosure k' arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure kRight arg_name' pred_body' var_env' = qtRight.pred := by
                    simpa using hclos_right.symm
                  _ = Predicate.guardClosure k' arg_name pred_body var_env := hpredRight
              cases hpred_ctor_eq
              have hpred_eq : qtRight.pred = qt.pred := by
                simp [hpredRight, hpred]
              have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
                cases hkres : (ctxAfter ctx res).regime.lookup? k' with
                | none =>
                    exact False.elim (hRdef (by simpa [ctxAfter, hk_eq] using hkres))
                | some b' =>
                    have hk_right : (ctxAfter ctx resRight).regime.lookup? k' = some b' :=
                      hlookup_back k' b' hkres
                    have hb_eq : b = b' := by
                      have : some b = some b' := by
                        calc
                          some b = (ctxAfter ctx resRight).regime.lookup? k' := by symm; exact hreg
                          _ = some b' := hk_right
                      exact Option.some.inj this
                    exact congrArg some hb_eq.symm
              have hcons_res :
                  (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                  (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
                refine ⟨?_, ?_⟩
                · intro hb
                  exact
                    qtypPredHolds_transport_pred
                      (predSat := predSat) (qt := qtRight) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
                · intro hb
                  exact
                    qtypPredHolds_transport_pred_not
                      (predSat := predSat) (qt := qtRight) (qt' := qt)
                      (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
              exact Or.inr <|
                locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                  hpred hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact Or.inr <| False.elim (hRdef hkres)
    | some b =>
        have hRdef_right : (ctxAfter ctx resRight).regime.lookup? k ≠ none := by
          intro hnone
          have hk_right := hlookup_back k b hkres
          rw [hk_right] at hnone
          contradiction
        have hvar_right :=
          hvars x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_right
        rcases hvar_right with hmasked | hvar_right
        · exact Or.inl hmasked
        · exact Or.inr <|
            varsRegime_transport_active_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx resRight).regime)
              (R' := (ctxAfter ctx res).regime)
              (μ := μ) (ρ := ρ) (entry := (x, qt))
              hlookup_back hguard hkres hvar_right
  · intro x qt v hlookup hlookup_v
    have hcap_right :
        closureCapturedVarsRegimeMasked masked predSat
          (ctxAfter ctx resRight).regime
          qt μ θ v :=
      hclos x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter ctx resRight).regime)
        (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_right

/-- Extract a context-level guard owner from successful `matchGuard`. -/
private lemma matchGuard_ok_extract_owner_in_ctx
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
      ∨
      (∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ) ) := by
  have hcond_ok : ∃ conditionPExpr, cond.toPExpr = .ok conditionPExpr := by
    rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
    have hcond_ok' : cond.toPExpr = .ok conditionPExpr := by
      unfold Expr.toPExpr
      rw [hcond_some]
      simp [pure, Except.pure]
    exact ⟨conditionPExpr, hcond_ok'⟩
  rcases hcond_ok with ⟨conditionPExpr, hcond⟩
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  have hvar_or_href :=
    singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall
  rcases hvar_or_href with hvar | hrefMem
  · left
    exact var_match_from_varMatches ctx conditionPExpr k deps fuel hvar
  · right
    exact ref_match_from_refMatches ctx conditionPExpr k deps refMatches fuel href hrefMem

/-- Lift a context-level owner witness to the runtime owner witness shape used by `match_iff`. -/
private lemma owner_in_ctx_to_runtime_owner_witness
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (k : Tag)
    (hctx :
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
        ∨
        (∃ (x : Name) (qt : QTyp) (ls : LocSet)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            ls.isEmpty = false ∧
            (∀ l, l ∈ ls →
              ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ) ))
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    ∃ v,
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          ρ.lookup x = some v)
        ∨
        (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          ctx.memEnv.lookup l0 = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) := by
  rcases hric with ⟨hmemInst, hvarInst⟩
  rcases hctx with hvar | href
  · rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred⟩
    rcases hvarInst hlookup with ⟨v, hρ, _⟩
    exact ⟨v, Or.inl ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred, hρ⟩⟩
  · rcases href with ⟨x, qt, ls, arg_name, pred_body, var_env, hlookup, hetyp, _hlsNonempty, hall⟩
    rcases hvarInst hlookup with ⟨v0, _hρ, hvtyp⟩
    have hvtyp_ref : valueHasETyp θ v0 (ETyp.ref ls) := by
      simpa [hetyp] using hvtyp
    cases hvtyp_ref with
    | loc hθ hin =>
        rename_i a l0
        have hμcontains : μ.contains a = true := (hmemInst l0 a hθ).2
        rcases Memory_lookup_some_of_contains hμcontains with ⟨n, hμ⟩
        rcases hall l0 hin with ⟨memQt, hlookupMem, hpredMem⟩
        exact ⟨Value.num n, Or.inr
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hin, hlookupMem, hpredMem, hθ, hμ, rfl⟩⟩

/-- If `matchGuard` succeeds at `(k,deps)`, there is a runtime owner witness for tag `k`
    under any runtime that instantiates `ctx`. -/
lemma matchGuard_ok_runtime_owner
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hric : runtimeInstantiatesCtx ctx μ ρ θ) :
    ∃ v,
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          ρ.lookup x = some v)
        ∨
        (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          ctx.memEnv.lookup l0 = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          θ.lookup l0 = some a ∧
          μ.lookup a = some n ∧
          v = Value.num n) ) := by
  have hctx := matchGuard_ok_extract_owner_in_ctx ctx cond k deps hmatch
  exact owner_in_ctx_to_runtime_owner_witness ctx μ ρ θ k hctx hric

/-- Successful `matchGuard` implies the returned guard tag appears as
    `qtypGuardTag` in the context's `varEnv` or `memEnv`. -/
lemma matchGuard_ok_tag_from_ctx
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    (∃ x qt, ctx.varEnv.lookup x = some qt ∧ qtypGuardTag qt = some k) ∨
    (∃ l qt, ctx.memEnv.lookup l = some qt ∧ qtypGuardTag qt = some k) := by
  have howner := matchGuard_ok_extract_owner_in_ctx ctx cond k deps hmatch
  rcases howner with hvar | href
  · rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred⟩
    left
    exact ⟨x, qt, hlookup, by simp [qtypGuardTag, hpred]⟩
  · rcases href with ⟨x, qt, ls, arg_name, pred_body, var_env, _hlookup, _hetyp, hlsNonempty, hall⟩
    have hne : ls ≠ (∅ : LocSet) := by
      exact (Std.ExtTreeSet.isEmpty_eq_false_iff).1 hlsNonempty
    have hexists : ∃ l, l ∈ ls := by
      by_contra hno
      apply hne
      exact (Std.ExtTreeSet.eq_empty_iff_forall_not_mem).2 (by
        intro l
        exact fun hl => hno ⟨l, hl⟩)
    rcases hexists with ⟨l, hl⟩
    rcases hall l hl with ⟨memQt, hlookupMem, hpredMem⟩
    right
    exact ⟨l, memQt, hlookupMem, by simp [qtypGuardTag, hpredMem]⟩

/-- In a context where all top-level guard tags lie below the regime bound,
    `matchGuard` returns a tag below that bound. -/
lemma matchGuard_tag_in_bound
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hbounded : predTagsBoundedInCtx ctx) :
    k < ctx.regime.bound := by
  rcases hbounded with ⟨hvar_bounded, hmem_bounded⟩
  rcases matchGuard_ok_tag_from_ctx ctx cond k deps hmatch with
    ⟨x, qt, hlookup, htag⟩ | ⟨l, qt, hlookup, htag⟩
  · exact hvar_bounded x qt k hlookup htag
  · exact hmem_bounded l qt k hlookup htag

/-- Optional local helper for the `ite` FR modes.
    Shows the guard evaluation boolean is aligned with the regime value once
    `matchGuard` succeeds and an owner witness is available.

    NOTE: `howner` is the runtime owner-witness needed by `PredSatLaws.match_iff`
    (premise (iii)). At intended call sites, derive it via bridge lemmas:
    `matchGuard_ok_owner_in_ctx` then `owner_in_ctx_to_runtime`.
    Sketch:
    `matchGuard_ok_owner_in_ctx`:
      `matchGuard cond ctx.memEnv ctx.varEnv = .ok (k,deps) →`
      `∃ owner, ownerHasGuardTagInCtx ctx cond k owner`
    `owner_in_ctx_to_runtime`:
      `runtimeInstantiatesCtx ctx μ ρ θ → ownerHasGuardTagInCtx ctx cond k owner →`
      `∃ v, ownerWitnessAtRuntime owner μ ρ θ v`
    This helper itself does not need `runtimeInstantiatesCtx`; that premise
    is expected while constructing `howner` via the bridge lemmas. -/
lemma guard_branch_alignment
    (predSat : PredSat) (tm : TagMeaning) (mode : LeanPoison.EvalMode)
    (ctx : TypeContext) (μ₀ : Memory) (ρ₀ : VarEnv) (θ₀ : RealizationMap)
    (l₀ : Address) (pm₀ : Bool)
    (hwfTm : wfTagMeaningCtx tm ctx) (hpred : PredSatLaws predSat tm)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ₀ ρ₀ θ₀)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config)
    {fuel : Nat}
    (howner :
      ∃ v,
        ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            ρ₀.lookup x = some v)
          ∨
          (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
              (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            l0 ∈ ls ∧
            ctx.memEnv.lookup l0 = some memQt ∧
            memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            θ₀.lookup l0 = some a ∧
            μ₀.lookup a = some n ∧
            v = Value.num n) ) ) :
    matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    terminatesTo mode cond
      { memory := μ₀, varEnv := ρ₀, nextAddr := l₀, pureMode := pm₀ }
      cfg' (Value.bool b') →
    b' = b := by
  intro hmatch hregime hterm
  rcases howner with ⟨v, hv_owner⟩
  have hmatch_iff_v : (b' = true ↔ predSat k μ₀ v) := by
    exact hpred.match_iff mode cond ctx.memEnv ctx.varEnv fuel k deps
      μ₀ ρ₀ θ₀ l₀ pm₀ cfg' v b' hwfTm hmatch hterm (by
        cases hv_owner with
        | inl hvar =>
            rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
            left
            refine ⟨x, qt, hlookup, ?_, hvar⟩
            simp [qtypGuardTag, hpred_qt]
        | inr href =>
            rcases href with
              ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
                hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
            right
            refine ⟨x, qt, memQt, ls, l0, a, n, hlookup, hetyp, hIn, hlookupMem, ?_, hθ, hμ, hv⟩
            simp [qtypGuardTag, hpred_memQt])
  have hRdef : ctx.regime.lookup? k ≠ none := by
    simp [hregime]
  have hpred_implies_lookup_true : predSat k μ₀ v → ctx.regime.lookup? k = some true := by
    intro hsat
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ ρ₀ (x, qt) :=
          hcwr.2.1 x qt k hlookup htag_qt hRdef
        cases hvr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_qt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_qt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 v1 b1 hclos hregime1 hvar1 hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = qt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_qt
              cases hEq
              rfl
            have hv1 : v1 = v := by
              have : some v1 = some v := by simpa [hvar1] using hvar
              exact Option.some.inj this
            by_cases hb1t : b1 = true
            ·
              have hlookup_k_b1 : ctx.regime.lookup? k = some b1 := by
                simpa [hk] using hregime1
              simpa [hb1t] using hlookup_k_b1
            · have hb1f : b1 = false := by
                cases b1 <;> simp at hb1t ⊢
              have hnot : ¬ qtypPredHolds predSat qt μ₀ v1 := hconsist.2 hb1f
              have hsat1 : predSat k1 μ₀ v1 := by
                simpa [hk, hv1] using hsat
              have hholds : qtypPredHolds predSat qt μ₀ v1 :=
                qtypPredHolds.guardClosure_ok hclos hsat1
              exact False.elim (hnot hholds)
    | inr href =>
        rcases href with
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
        have htag_memQt : qtypGuardTag memQt = some k := by
          simp [qtypGuardTag, hpred_memQt]
        have hlr : locsRegime predSat ctx.regime μ₀ θ₀ (l0, memQt) :=
          hcwr.1 l0 memQt k hlookupMem htag_memQt hRdef
        cases hlr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_memQt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_memQt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 a1 n1 b1 hclos hregime1 hreal hmem hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = memQt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_memQt
              cases hEq
              rfl
            have ha : a1 = a := by
              have : some a1 = some a := by simpa [hreal] using hθ
              exact Option.some.inj this
            have hmemA : μ₀.lookup a = some n1 := by
              simpa [ha] using hmem
            have hn : n1 = n := by
              have : some n1 = some n := by simpa [hmemA] using hμ
              exact Option.some.inj this
            have hv_num : v = Value.num n1 := by
              calc
                v = Value.num n := hv
                _ = Value.num n1 := by simp [hn]
            by_cases hb1t : b1 = true
            ·
              have hlookup_k_b1 : ctx.regime.lookup? k = some b1 := by
                simpa [hk] using hregime1
              simpa [hb1t] using hlookup_k_b1
            · have hb1f : b1 = false := by
                cases b1 <;> simp at hb1t ⊢
              have hnot : ¬ qtypPredHolds predSat memQt μ₀ (Value.num n1) := hconsist.2 hb1f
              have hsat_num : predSat k1 μ₀ (Value.num n1) := by
                simpa [hk, hv_num] using hsat
              have hholds : qtypPredHolds predSat memQt μ₀ (Value.num n1) :=
                qtypPredHolds.guardClosure_ok hclos hsat_num
              exact False.elim (hnot hholds)
  have hlookup_true_implies_pred : ctx.regime.lookup? k = some true → predSat k μ₀ v := by
    intro hktrue
    cases hv_owner with
    | inl hvar =>
        rcases hvar with ⟨x, qt, arg_name, pred_body, var_env, hlookup, hpred_qt, hvar⟩
        have htag_qt : qtypGuardTag qt = some k := by
          simp [qtypGuardTag, hpred_qt]
        have hvr : varsRegime predSat ctx.regime μ₀ ρ₀ (x, qt) :=
          hcwr.2.1 x qt k hlookup htag_qt hRdef
        cases hvr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_qt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_qt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 v1 b1 hclos hregime1 hvar1 hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = qt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_qt
              cases hEq
              rfl
            have hv1 : v1 = v := by
              have : some v1 = some v := by simpa [hvar1] using hvar
              exact Option.some.inj this
            have hb1t : b1 = true := by
              have hlookup_k1_true : ctx.regime.lookup? k1 = some true := by
                simpa [hk] using hktrue
              have : some b1 = some true := by simpa [hregime1] using hlookup_k1_true
              exact Option.some.inj this
            have hholds : qtypPredHolds predSat qt μ₀ v1 := hconsist.1 hb1t
            cases hholds with
            | noPred_ok hnp =>
                exfalso
                simp [hpred_qt] at hnp
            | guardOnly_ok hgo _ =>
                exfalso
                simp [hpred_qt] at hgo
            | guardClosure_ok hclos' hsat' =>
                rename_i k2 arg2 body2 env2
                have hk2 : k2 = k1 := by
                  have hEq :
                      Predicate.guardClosure k2 arg2 body2 env2 =
                      Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := by
                    calc
                      Predicate.guardClosure k2 arg2 body2 env2 = qt.pred := by
                        symm; exact hclos'
                      _ = Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := hclos
                  cases hEq
                  rfl
                subst hk2
                simpa [hk, hv1] using hsat'
    | inr href =>
        rcases href with
          ⟨x, qt, memQt, ls, l0, a, n, arg_name, pred_body, var_env,
            hlookup, hetyp, hIn, hlookupMem, hpred_memQt, hθ, hμ, hv⟩
        have htag_memQt : qtypGuardTag memQt = some k := by
          simp [qtypGuardTag, hpred_memQt]
        have hlr : locsRegime predSat ctx.regime μ₀ θ₀ (l0, memQt) :=
          hcwr.1 l0 memQt k hlookupMem htag_memQt hRdef
        cases hlr with
        | noPred_ok hnp =>
            exfalso
            simp [qtypGuardTag, hpred_memQt] at hnp
        | guardOnly_ok _k hgo =>
            exfalso
            simp [hpred_memQt] at hgo
        | withPred_ok k1 arg_name1 pred_body1 var_env1 a1 n1 b1 hclos hregime1 hreal hmem hconsist =>
            have hk : k1 = k := by
              have hEq :
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 =
                  Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 = memQt.pred := by
                    symm; exact hclos
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_memQt
              cases hEq
              rfl
            have ha : a1 = a := by
              have : some a1 = some a := by simpa [hreal] using hθ
              exact Option.some.inj this
            have hmemA : μ₀.lookup a = some n1 := by
              simpa [ha] using hmem
            have hn : n1 = n := by
              have : some n1 = some n := by simpa [hmemA] using hμ
              exact Option.some.inj this
            have hv_num : v = Value.num n1 := by
              calc
                v = Value.num n := hv
                _ = Value.num n1 := by simp [hn]
            have hb1t : b1 = true := by
              have hlookup_k1_true : ctx.regime.lookup? k1 = some true := by
                simpa [hk] using hktrue
              have : some b1 = some true := by simpa [hregime1] using hlookup_k1_true
              exact Option.some.inj this
            have hholds : qtypPredHolds predSat memQt μ₀ (Value.num n1) := hconsist.1 hb1t
            have hsat_num : predSat k1 μ₀ (Value.num n1) := by
              cases hholds with
              | noPred_ok hnp =>
                  exfalso
                  simp [hpred_memQt] at hnp
              | guardOnly_ok hgo _ =>
                  exfalso
                  simp [hpred_memQt] at hgo
              | guardClosure_ok hclos' hsat' =>
                  rename_i k2 arg2 body2 env2
                  have hk2 : k2 = k1 := by
                    have hEq :
                        Predicate.guardClosure k2 arg2 body2 env2 =
                        Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := by
                      calc
                        Predicate.guardClosure k2 arg2 body2 env2 = memQt.pred := by
                          symm; exact hclos'
                        _ = Predicate.guardClosure k1 arg_name1 pred_body1 var_env1 := hclos
                    cases hEq
                    rfl
                  subst hk2
                  exact hsat'
            simpa [hk, hv_num] using hsat_num
  have hb'_iff : (b' = true ↔ b = true) := by
    constructor
    · intro hb'true
      have hsat : predSat k μ₀ v := hmatch_iff_v.mp hb'true
      have hktrue : ctx.regime.lookup? k = some true := hpred_implies_lookup_true hsat
      have : some b = some true := by simpa [hregime] using hktrue
      exact Option.some.inj this
    · intro hbtrue
      have hktrue : ctx.regime.lookup? k = some true := by
        simp [hregime, hbtrue]
      have hsat : predSat k μ₀ v := hlookup_true_implies_pred hktrue
      exact hmatch_iff_v.mpr hsat
  cases b <;> cases b' <;> simp at hb'_iff ⊢

/-- Public wrapper for branch-alignment from a successful `matchGuard`.
    Packages the runtime-owner extraction and the semantic alignment step
    needed by the single-run `ite` proof. -/
theorem matchGuard_runtime_branch_alignment
    (predSat : PredSat) (tm : TagMeaning) (mode : LeanPoison.EvalMode)
    (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
    (a : Address) (pm : Bool)
    (hwfTm : wfTagMeaningCtx tm ctx) (hpred : PredSatLaws predSat tm)
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hcwr : consistentWithRegime predSat ctx.regime ctx μ ρ θ)
    (cond : Expr) (k : Tag) (deps : Deps) (b b' : Bool) (cfg' : Config)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps))
    (hregime : ctx.regime.lookup? k = some b)
    (hterm : terminatesTo mode cond
      { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
      cfg' (Value.bool b')) :
    b' = b := by
  have howner := matchGuard_ok_runtime_owner ctx μ ρ θ cond k deps hmatch hric
  exact
    guard_branch_alignment predSat tm mode ctx μ ρ θ a pm
      hwfTm hpred hcwr cond k deps b b' cfg' howner hmatch hregime hterm

private lemma stepFR_ite_mode1
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_true : ctxᵢ.regime.lookup? k = some true)
  (res1 res2 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          typecheckExpr .ioFree ctxTrue e2 fuel' = .ok res2)
  (hmemEnv : res.memEnv' = res2.memEnv')
  (htagEnv : res.tagEnv' = res2.tagEnv')
  (hnextLoc : res.nextLoc' = res2.nextLoc')
  (hnextTag : res.nextTag' = res2.nextTag')
  (hregime' : res.regime' = res2.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res2.qualType.poison)
  (hetyp : res.qualType.etyp = res2.qualType.etyp) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwfTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  have hb₀_true : b₀ = true := by
    have howner₀ := matchGuard_ok_runtime_owner ctxᵢ μ₀ ρ₀ θ₀ e1 k deps hmatch hric₀
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps true b₀ cfg₀1
        howner₀
        hmatch hregime_true ht₀_e1
  have hb₁_true : b₁ = true := by
    have howner₁ := matchGuard_ok_runtime_owner ctxᵢ μ₁ ρ₁ θ₁ e1 k deps hmatch hric₁
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps true b₁ cfg₁1
        howner₁
        hmatch hregime_true ht₁_e1
  have ht₀_e2 : terminatesTo .ioFree e2 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₀_true]
        contradiction
  have ht₁_e2 : terminatesTo .ioFree e2 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h => exact h.2
    | inr h =>
        have : false = true := by rw [← h.1, hb₁_true]
        contradiction
  let ctxTrue := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
  have htc2' : typecheck .ioFree ctxTrue e2 fuel' = .ok res2 := by
    simpa [typecheck, Nat.succ_sub_one] using htc2
  have hwfTm_true : wfTagMeaningCtx tm ctxTrue := by
    simpa [wfTagMeaningCtx, ctxTrue] using hwfTm
  have hIH_e2 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e2 ctxTrue hwfTm_true res2 htc2'
  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred := by
    have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
      native_decide
    unfold typecheckIf at htcIf
    erw [hmatch] at htcIf
    simp [hregime_true, heq, bind, Except.bind] at htcIf
    rw [htc1] at htcIf
    simp at htcIf
    cases hq1 : res1.qualType with
    | mk etyp1 p1 pred1 =>
        simp [hq1] at htcIf
        have hbool1 : etyp1 = ETyp.bool := by
          simpa [hq1] using hbool
        rw [hbool1] at htcIf
        simp [htc2, pure, Except.pure] at htcIf
        cases hq2 : res2.qualType with
        | mk etyp2 p2 pred2 =>
            simp [hq2] at htcIf
            cases htcIf
            rfl
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_true : wfTypeContext ctxTrue := by
    simpa [wfTypeContext, ctxTrue] using hwf
  have hric₀1' : runtimeInstantiatesCtx ctxTrue cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hsub₀ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    exact
      runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
        (ctx := ctxᵢ) (res := res1) (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
        (k := k) (deps := deps)
        hsub₀ hric₀1
  have hric₁1' : runtimeInstantiatesCtx ctxTrue cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hsub₁ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    exact
      runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
        (ctx := ctxᵢ) (res := res1) (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
        (k := k) (deps := deps)
        hsub₁ hric₁1
  have htagR_true : regimeConsistentWithCtx ctxTrue := by
    unfold regimeConsistentWithCtx at htagR ⊢
    constructor
    · exact tagEnvConsistentWithRegime_insert_true
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR.1 hregime_true
    · simpa [ctxTrue] using htagR.2
  have hRbound_true : regimeBounded ctxTrue.regime := by
    simpa [ctxTrue] using hRbound
  have hcwr₀1' : consistentWithRegime predSat ctxTrue.regime ctxTrue cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    refine
      consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
        (predSat := predSat) (ctx := ctxᵢ) (res := res1)
        (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
        (kTrue := k) (depsTrue := deps)
        ?hreg_bridge ?hmem_bridge hcwr₀1
    · intro k' b hk
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b hk
    · intro l qt k' hlookup hguard hRdef
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt k' hlookup hguard hRdef
  have hcwr₁1' : consistentWithRegime predSat ctxTrue.regime ctxTrue cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    refine
      consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
        (predSat := predSat) (ctx := ctxᵢ) (res := res1)
        (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
        (kTrue := k) (depsTrue := deps)
        ?hreg_bridge1 ?hmem_bridge1 hcwr₁1
    · intro k' b hk
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b hk
    · intro l qt k' hlookup hguard hRdef
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt k' hlookup hguard hRdef
  have hagree1' :
      agreeOnClean predSat ctxTrue.regime ctxTrue
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    have hcleanBack :
        ∀ qt, qtypCleanUnder ctxTrue.regime qt → qtypCleanUnder res1.regime' qt := by
      intro qt hclean
      exact
        qtypCleanUnder_transport_pure_regime_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 qt (by simpa [ctxTrue] using hclean)
    have hlookupBackAll :
        ∀ k' b, ctxTrue.regime.lookup? k' = some b → res1.regime'.lookup? k' = some b := by
      intro k' b hk
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxTrue] using hk)
    have hmemberVars₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₀1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberCvcr₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberCvcrEvidence predSat ctxTrue.regime cfg₀1.memory θ₀1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberVars₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxTrue.regime cfg₁1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    have hmemberCvcr₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberCvcrEvidence predSat ctxTrue.regime cfg₁1.memory θ₁1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxTrue.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    constructor
    · intro l qt hlookup hclean
      have hlookupRes :
          res1.memEnv'.lookup l = some qt :=
        typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt (by simpa [ctxTrue] using hlookup)
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeLocUnder predSat res1.regime'
            cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt) :=
        hagree1.1 l qt (by simpa [ctxAfter] using hlookupRes) hcleanRes
      cases hagreeRes with
      | both_unrealized l qt hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxTrue.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxTrue.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV'
    · intro x qt hlookup hclean
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeVarUnder predSat res1.regime'
            cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
        hagree1.2 x qt (by simpa [ctxAfter, ctxTrue] using hlookup) hcleanRes
      cases hagreeRes with
      | both_none x qt hnone₀ hnone₁ =>
          exact agreeVarUnder.both_none x qt hnone₀ hnone₁
      | agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxTrue.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxTrue.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV'
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq :
      cfg₁1 =
        { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
          pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e2' : terminatesTo .ioFree e2
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e2
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e2 :=
    hIH_e2 hpredlaws hwfTm_true
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_true hric₀1' hric₁1' htagR_true hRbound_true
      hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e2 ht₁_e2'
  rcases hstep_e2 with ⟨hresTm2, hstep_e2⟩
  rcases hstep_e2 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀2, _hvtyp₁2, _hTm2, hwf2, hwfcf₀2, hwfcf₁2,
      hric₀2, hric₁2, htagR2, hcwr₀2, hcwr₁2, hagree2, _hvalc₀2, _hvalc₁2, hres_agree2⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxTrue res2 := by
    simp [ctxAfter, ctxTrue, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀2
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁2
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR2
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀2
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁2
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree2
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm res2.qualType res.qualType hresTm2 hetyp hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀2, hwfcf₁2,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · simpa [hetyp] using _hvtyp₀2
  · simpa [hetyp] using _hvtyp₁2
  · simpa [hctxAfter] using _hTm2
  · simpa [hctxAfter] using hwf2
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₀.memory θ₀2 o₀ := by
        simpa [hctxAfter] using hcap₂
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₂'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₂ : closureCapturedVarsRegime predSat (ctxAfter ctxTrue res2).regime res2.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁2
      have hcap₂' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res2.qualType cf₁.memory θ₁2 o₁ := by
        simpa [hctxAfter] using hcap₂
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₂'
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res2.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res2.qualType.poison = false := by
        calc
          joinPoison ctxᵢ.pc res2.qualType.poison = res.qualType.poison := by
            symm
            exact hpoison
          _ = false := hpoison_res
      exact (joinPoison_eq_false hjoin).2
    have hclean2 : qtypCleanUnder (ctxAfter ctxᵢ res).regime res2.qualType := by
      cases hclean with
      | clean hpoison_res =>
          exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k' htag _hreg _hnotfun =>
          exfalso
          simp [qtypGuardTag, hpredNo] at htag
    have hres_agree2' :
        resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ := by
      simpa [hctxAfter] using hres_agree2
    have hagree2' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res2.qualType o₀ o₁ :=
      hres_agree2' hclean2
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree2'

-- Mode 2: R(k) = some false (else-branch effective)
private lemma stepFR_ite_mode2
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_false : ctxᵢ.regime.lookup? k = some false)
  (res1 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc3 : let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩ }
          typecheckExpr .ioFree ctxFalse e3 fuel' = .ok res3)
  (hmemEnv : res.memEnv' = res3.memEnv')
  (htagEnv : res.tagEnv' = res3.tagEnv')
  (hnextLoc : res.nextLoc' = res3.nextLoc')
  (hnextTag : res.nextTag' = res3.nextTag')
  (hregime' : res.regime' = res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc res3.qualType.poison)
  (hetyp : res.qualType.etyp = res3.qualType.etyp) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by
    simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢
    exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwfTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  have hb₀_false : b₀ = false := by
    have howner₀ := matchGuard_ok_runtime_owner ctxᵢ μ₀ ρ₀ θ₀ e1 k deps hmatch hric₀
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₀ ρ₀ θ₀ a₀ pm
        hwfTm hpredlaws hcwr₀
        e1 k deps false b₀ cfg₀1
        howner₀
        hmatch hregime_false ht₀_e1
  have hb₁_false : b₁ = false := by
    have howner₁ := matchGuard_ok_runtime_owner ctxᵢ μ₁ ρ₁ θ₁ e1 k deps hmatch hric₁
    exact
      guard_branch_alignment predSat tm .ioFree
        ctxᵢ μ₁ ρ₁ θ₁ a₁ pm
        hwfTm hpredlaws hcwr₁
        e1 k deps false b₁ cfg₁1
        howner₁
        hmatch hregime_false ht₁_e1
  have ht₀_e3 : terminatesTo .ioFree e3 cfg₀1 cf₀ o₀ := by
    cases hbranch₀ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₀_false]
        contradiction
    | inr h => exact h.2
  have ht₁_e3 : terminatesTo .ioFree e3 cfg₁1 cf₁ o₁ := by
    cases hbranch₁ with
    | inl h =>
        have : true = false := by rw [← h.1, hb₁_false]
        contradiction
    | inr h => exact h.2
  let ctxFalse := { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩ }
  have htc3' : typecheck .ioFree ctxFalse e3 fuel' = .ok res3 := by
    simpa [typecheck, Nat.succ_sub_one] using htc3
  have hwfTm_false : wfTagMeaningCtx tm ctxFalse := by
    simpa [wfTagMeaningCtx, ctxFalse] using hwfTm
  have hIH_e3 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e3 ctxFalse hwfTm_false res3 htc3'
  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have hpredNo : res.qualType.pred = Predicate.noPred := by
    have heq : (LeanPoison.EvalMode.ioFree == LeanPoison.EvalMode.ioFree) = true := by
      native_decide
    unfold typecheckIf at htcIf
    erw [hmatch] at htcIf
    simp [hregime_false, heq, bind, Except.bind] at htcIf
    rw [htc1] at htcIf
    simp at htcIf
    cases hq1 : res1.qualType with
    | mk etyp1 p1 pred1 =>
        simp [hq1] at htcIf
        have hbool1 : etyp1 = ETyp.bool := by
          simpa [hq1] using hbool
        rw [hbool1] at htcIf
        simp [htc3, pure, Except.pure] at htcIf
        cases hq3 : res3.qualType with
        | mk etyp3 p3 pred3 =>
            simp [hq3] at htcIf
            cases htcIf
            rfl
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have hwf_false : wfTypeContext ctxFalse := by
    simpa [wfTypeContext, ctxFalse] using hwf
  have hric₀1' : runtimeInstantiatesCtx ctxFalse cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hsub₀ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    have hric₀1_true :
        runtimeInstantiatesCtx
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          cfg₀1.memory cfg₀1.varEnv θ₀1 := by
      exact
        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
          (ctx := ctxᵢ) (res := res1) (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
          (k := k) (deps := deps)
          hsub₀ hric₀1
    simpa [runtimeInstantiatesCtx, ctxFalse] using hric₀1_true
  have hric₁1' : runtimeInstantiatesCtx ctxFalse cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hsub₁ : ∀ l, res1.memEnv'.contains l → ctxᵢ.memEnv.contains l := by
      rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
      exact
        typecheckExpr_pure_mem_subset_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1
    have hric₁1_true :
        runtimeInstantiatesCtx
          { ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }
          cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      exact
        runtimeInstantiatesCtx_transport_mem_subset_tag_insert_true
          (ctx := ctxᵢ) (res := res1) (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
          (k := k) (deps := deps)
          hsub₁ hric₁1
    simpa [runtimeInstantiatesCtx, ctxFalse] using hric₁1_true
  have htagR_false : regimeConsistentWithCtx ctxFalse := by
    unfold regimeConsistentWithCtx at htagR ⊢
    constructor
    · exact tagEnvConsistentWithRegime_insert_false
        ctxᵢ.tagEnv ctxᵢ.regime k deps htagR.1
    · simpa [ctxFalse] using htagR.2
  have hRbound_false : regimeBounded ctxFalse.regime := by
    simpa [ctxFalse] using hRbound
  have hcwr₀1' : consistentWithRegime predSat ctxFalse.regime ctxFalse cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    have hcwr₀1_true :
        consistentWithRegime predSat
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
          cfg₀1.memory cfg₀1.varEnv θ₀1 := by
      refine
        consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
          (predSat := predSat) (ctx := ctxᵢ) (res := res1)
          (μ := cfg₀1.memory) (ρ := cfg₀1.varEnv) (θ := θ₀1)
          (kTrue := k) (depsTrue := deps)
          ?hreg_bridge ?hmem_bridge hcwr₀1
      · intro k' b hk
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_regime_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 k' b hk
      · intro l qt k' hlookup hguard hRdef
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 l qt k' hlookup hguard hRdef
    simpa [consistentWithRegime, ctxFalse] using hcwr₀1_true
  have hcwr₁1' : consistentWithRegime predSat ctxFalse.regime ctxFalse cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    have hcwr₁1_true :
        consistentWithRegime predSat
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ }).regime
          ({ ctxᵢ with tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩ })
          cfg₁1.memory cfg₁1.varEnv θ₁1 := by
      refine
        consistentWithRegime_transport_ctxAfter_pure_to_ctx_insert_true
          (predSat := predSat) (ctx := ctxᵢ) (res := res1)
          (μ := cfg₁1.memory) (ρ := cfg₁1.varEnv) (θ := θ₁1)
          (kTrue := k) (depsTrue := deps)
          ?hreg_bridge1 ?hmem_bridge1 hcwr₁1
      · intro k' b hk
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_regime_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 k' b hk
      · intro l qt k' hlookup hguard hRdef
        rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
        exact
          typecheckExpr_pure_guarded_mem_bridge_of_toPExpr
            (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
            hpe1 htc1 l qt k' hlookup hguard hRdef
    simpa [consistentWithRegime, ctxFalse] using hcwr₁1_true
  have hagree1' :
      agreeOnClean predSat ctxFalse.regime ctxFalse
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    rcases matchGuard_ok_toPExpr?_some ctxᵢ e1 k deps hmatch with ⟨pe1, hpe1⟩
    have hcleanBack :
        ∀ qt, qtypCleanUnder ctxFalse.regime qt → qtypCleanUnder res1.regime' qt := by
      intro qt hclean
      exact
        qtypCleanUnder_transport_pure_regime_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 qt (by simpa [ctxFalse] using hclean)
    have hlookupBackAll :
        ∀ k' b, ctxFalse.regime.lookup? k' = some b → res1.regime'.lookup? k' = some b := by
      intro k' b hk
      exact
        typecheckExpr_pure_regime_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 k' b (by simpa [ctxFalse] using hk)
    have hmemberVars₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₀1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₀1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberCvcr₀_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₀1.memory θ₀1 σcap ρcap →
            MemberCvcrEvidence predSat ctxFalse.regime cfg₀1.memory θ₀1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₀1.memory)
          hlookupBackAll h
    have hmemberVars₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberVarsRegimeEvidence predSat res1.regime' cfg₁1.memory σcap ρcap →
            MemberVarsRegimeEvidence predSat ctxFalse.regime cfg₁1.memory σcap ρcap := by
      intro σcap ρcap h
      exact
        memberVarsRegimeEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    have hmemberCvcr₁_transport :
        ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
          MemberCvcrEvidence predSat res1.regime' cfg₁1.memory θ₁1 σcap ρcap →
            MemberCvcrEvidence predSat ctxFalse.regime cfg₁1.memory θ₁1 σcap ρcap := by
      intro σcap ρcap h
      exact
        memberCvcrEvidence_transport_lookup_back
          (predSat := predSat) (R := res1.regime') (R' := ctxFalse.regime) (μ := cfg₁1.memory)
          hlookupBackAll h
    constructor
    · intro l qt hlookup hclean
      have hlookupRes :
          res1.memEnv'.lookup l = some qt :=
        typecheckExpr_pure_mem_lookup_bridge_of_toPExpr
          (ctx := ctxᵢ) (e := e1) (pe := pe1) (fuel := fuel') (res := res1)
          hpe1 htc1 l qt (by simpa [ctxFalse] using hlookup)
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeLocUnder predSat res1.regime'
            cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt) :=
        hagree1.1 l qt (by simpa [ctxAfter] using hlookupRes) hcleanRes
      cases hagreeRes with
      | both_unrealized l qt hnone₀ hnone₁ =>
          exact agreeLocUnder.both_unrealized l qt hnone₀ hnone₁
      | agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxFalse.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt (Value.num n₀) (Value.num n₁) :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxFalse.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ hreal₀ hreal₁ hlookup₀ hlookup₁ hagreeV'
    · intro x qt hlookup hclean
      have hcleanRes : qtypCleanUnder res1.regime' qt := hcleanBack qt hclean
      have hagreeRes :
          agreeVarUnder predSat res1.regime'
            cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
        hagree1.2 x qt (by simpa [ctxAfter, ctxFalse] using hlookup) hcleanRes
      cases hagreeRes with
      | both_none x qt hnone₀ hnone₁ =>
          exact agreeVarUnder.both_none x qt hnone₀ hnone₁
      | agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV =>
          have hagreeV' :
              agreeValueUnder predSat ctxFalse.regime
                cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 qt v₀ v₁ :=
            agreeValueUnder_clean_transport_by_cleanBack
              (predSat := predSat)
              (R := res1.regime')
              (R' := ctxFalse.regime)
              (h_clean_back := hcleanBack)
              (hmemberVars₀_transport := hmemberVars₀_transport)
              (hmemberCvcr₀_transport := hmemberCvcr₀_transport)
              (hmemberVars₁_transport := hmemberVars₁_transport)
              (hmemberCvcr₁_transport := hmemberCvcr₁_transport)
              hclean hagreeV
          exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagreeV'
  have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by rw [hpm₀1, hpm₁1]
  have hcfg₁1_eq :
      cfg₁1 =
        { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
          pureMode := cfg₀1.pureMode } := by
    cases cfg₁1
    simp only [Config.mk.injEq, true_and]
    exact hpm_eq
  have ht₁_e3' : terminatesTo .ioFree e3
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode }
      cf₁ o₁ := by
    rw [← hcfg₁1_eq]
    exact ht₁_e3
  have hwfcf₁1' : wfConfig
      { memory := cfg₁1.memory, varEnv := cfg₁1.varEnv, nextAddr := cfg₁1.nextAddr,
        pureMode := cfg₀1.pureMode } := by
    rw [← hcfg₁1_eq]
    exact hwfcf₁1
  have hstep_e3 :=
    hIH_e3 hpredlaws hwfTm_false
      cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
      cf₀ cf₁ o₀ o₁
      hθ₀1wf hθ₁1wf hwf_false hric₀1' hric₁1' htagR_false hRbound_false
      hcwr₀1' hcwr₁1' hagree1'
      cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
      ht₀_e3 ht₁_e3'
  rcases hstep_e3 with ⟨hresTm3, hstep_e3⟩
  rcases hstep_e3 with
    ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, _hvtyp₀3, _hvtyp₁3, _hTm3, hwf3, hwfcf₀3, hwfcf₁3,
      hric₀3, hric₁3, htagR3, hcwr₀3, hcwr₁3, hagree3, _hvalc₀3, _hvalc₁3, hres_agree3⟩
  have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
  have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
  have hctxAfter : ctxAfter ctxᵢ res = ctxAfter ctxFalse res3 := by
    simp [ctxAfter, ctxFalse, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
  have hric₀_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hric₀3
  have hric₁_final : runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hric₁3
  have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) := by
    simpa [hctxAfter] using htagR3
  have hcwr₀_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 := by
    simpa [hctxAfter] using hcwr₀3
  have hcwr₁_final :
      consistentWithRegime predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hcwr₁3
  have hagree_final :
      agreeOnClean predSat (ctxAfter ctxᵢ res).regime (ctxAfter ctxᵢ res)
        cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
    simpa [hctxAfter] using hagree3
  have hresTm : QTypRespectsTagMeaning tm res.qualType := by
    have hguard : qtypGuardDesc? res.qualType = none := by
      simp [qtypGuardDesc?, hpredNo]
    intro qt' k' d hinq hqd
    exact
      (QTypRespectsTagMeaning_transport_etyp_noGuard
        tm res3.qualType res.qualType hresTm3 hetyp hguard) hinq hqd
  refine ⟨hresTm, ?_⟩
  refine ⟨θ₀2, θ₁2, hθext₀, hθext₁, ?_, ?_, ?_, ?_, hwfcf₀3, hwfcf₁3,
    hric₀_final, hric₁_final, htag_final, hcwr₀_final, hcwr₁_final, hagree_final, ?_, ?_, ?_⟩
  · simpa [hetyp] using _hvtyp₀3
  · simpa [hetyp] using _hvtyp₁3
  · simpa [hctxAfter] using _hTm3
  · simpa [hctxAfter] using hwf3
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₀.memory) (v := o₀) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse res3).regime res3.qualType cf₀.memory θ₀2 o₀ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₀3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₀.memory θ₀2 o₀ := by
        simpa [hctxAfter] using hcap₃
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₃'
  · refine valueConsistentWithRegime.noTag (predSat := predSat) (R := (ctxAfter ctxᵢ res).regime)
      (qt := res.qualType) (μ := cf₁.memory) (v := o₁) ?_ ?_
    · simp [qtypGuardTag, hpredNo]
    · have hcap₃ : closureCapturedVarsRegime predSat (ctxAfter ctxFalse res3).regime res3.qualType cf₁.memory θ₁2 o₁ :=
        valueConsistentWithRegime_closureCapturedVarsRegime _hvalc₁3
      have hcap₃' : closureCapturedVarsRegime predSat (ctxAfter ctxᵢ res).regime res3.qualType cf₁.memory θ₁2 o₁ := by
        simpa [hctxAfter] using hcap₃
      exact closureCapturedVarsRegime_transport_etyp hetyp.symm hcap₃'
  · intro hclean
    have hpoison_imp : res.qualType.poison = false → res3.qualType.poison = false := by
      intro hpoison_res
      have hjoin : joinPoison ctxᵢ.pc res3.qualType.poison = false := by
        calc
          joinPoison ctxᵢ.pc res3.qualType.poison = res.qualType.poison := by
            symm
            exact hpoison
          _ = false := hpoison_res
      exact (joinPoison_eq_false hjoin).2
    have hclean3 : qtypCleanUnder (ctxAfter ctxᵢ res).regime res3.qualType := by
      cases hclean with
      | clean hpoison_res =>
          exact qtypCleanUnder.clean (hpoison_imp hpoison_res)
      | guard k' htag _hreg _hnotfun =>
          exfalso
          simp [qtypGuardTag, hpredNo] at htag
    have hres_agree3' :
        resultAgreesIfClean predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res3.qualType o₀ o₁ := by
      simpa [hctxAfter] using hres_agree3
    have hagree3' :
        agreeValueUnder predSat (ctxAfter ctxᵢ res).regime
          cf₀.memory cf₁.memory θ₀2 θ₁2 res3.qualType o₀ o₁ :=
      hres_agree3' hclean3
    exact agreeValueUnder_transport_clean hclean hetyp hpoison_imp hagree3'

-- Mode 3: R(k) = none (conservative join)
private lemma stepFR_ite_mode3
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (k : Tag) (deps : Deps) (hmatch : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .ok (k, deps))
  (hregime_none : ctxᵢ.regime.lookup? k = none)
  (res1 res2 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : let branchPc := joinPoison ctxᵢ.pc res1.qualType.poison
          let ctxTrue := { ctxᵢ with
            tagEnv := ctxᵢ.tagEnv.insert k ⟨true, deps⟩
            pc := branchPc
            regime := { ctxᵢ.regime with map := ctxᵢ.regime.map.insert k true } }
          typecheckExpr .ioFree ctxTrue e2 fuel' = .ok res2)
  (htc3 : let branchPc := joinPoison ctxᵢ.pc res1.qualType.poison
          let ctxFalse := { ctxᵢ with
            tagEnv := ctxᵢ.tagEnv.insert k ⟨false, deps⟩
            pc := branchPc
            regime := { ctxᵢ.regime with map := ctxᵢ.regime.map.insert k false } }
          let ctxFalse' := { ctxFalse with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
          typecheckExpr .ioFree ctxFalse' e3 fuel' = .ok res3)
  (hmemEnv : res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv')
  (htagEnv : res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' res3.nextLoc')
  (hnextTag : res.nextTag' = max res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = joinRegimes res2.regime' res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison
                          (joinPoison res2.qualType.poison res3.qualType.poison))) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert ite evaluation (world-free)
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  -- Apply IH to e1
  have htc1' : typecheck .ioFree { ctxᵢ with pureCtx := true } e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hwfTm_pure : wfTagMeaningCtx tm { ctxᵢ with pureCtx := true } := by simpa [wfTagMeaningCtx] using hwfTm
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 { ctxᵢ with pureCtx := true } hwfTm_pure res1 htc1'
  have hwf_pure : wfTypeContext { ctxᵢ with pureCtx := true } := by
    simp [wfTypeContext] at hwf ⊢; exact hwf
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm_pure μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf_pure hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, _hwf1, hwfcf₀1, hwfcf₁1, _hric₀1, _hric₁1, _htagR1, _hcwr₀1, _hcwr₁1, _hagree1, _hvalc₀1, _hvalc₁1, hres_agree1⟩
  -- In mode 3, we don't know which branch each run takes - need to handle all cases
  -- The key is that the joined result is conservative over both branches
  sorry -- Mode 3: complex proof with branch case analysis

-- Mode 4: matchGuard fails (standard join)
set_option maxHeartbeats 2000000 in
private lemma stepFR_ite_mode4
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (singleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res)
  (err : String) (hmatch_fail : matchGuard e1 ctxᵢ.memEnv ctxᵢ.varEnv fuel' = .error err)
  (res1 res2 res3 : TypeResult)
  (htc1 : typecheckExpr .ioFree ctxᵢ e1 fuel' = .ok res1)
  (hbool : res1.qualType.etyp = ETyp.bool)
  (htc2 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           typecheckExpr .ioFree ctx'' e2 fuel' = .ok res2))
  (htc3 : (let ctx' := { ctxᵢ with memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime' }
           let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
           let ctx'' := { ctx' with pc := pc' }
           let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
           typecheckExpr .ioFree ctxForE3 e3 fuel' = .ok res3))
  (hmemEnv : res.memEnv' = joinMemEnvsStrong res2.memEnv' res3.memEnv')
  (htagEnv : res.tagEnv' = joinTagEnvs res2.tagEnv' res3.tagEnv')
  (hnextLoc : res.nextLoc' = max res2.nextLoc' res3.nextLoc')
  (hnextTag : res.nextTag' = max res2.nextTag' res3.nextTag')
  (hregime' : res.regime' = joinRegimes res2.regime' res3.regime')
  (hpoison : res.qualType.poison = joinPoison ctxᵢ.pc (joinPoison res1.qualType.poison
                          (joinPoison res2.qualType.poison res3.qualType.poison))) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  intro hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀ ht₁
  -- Invert ite evaluation (world-free)
  have hstruct₀ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm } cf₀ o₀ ht₀
  rcases hstruct₀ with ⟨cfg₀1, b₀, ht₀_e1, hbranch₀, hpm₀1, hpm₀_final⟩
  have hstruct₁ := terminatesTo_ite_inv' e1 e2 e3
    { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm } cf₁ o₁ ht₁
  rcases hstruct₁ with ⟨cfg₁1, b₁, ht₁_e1, hbranch₁, hpm₁1, hpm₁_final⟩
  -- Apply IH to e1 (without pureCtx in this mode)
  have htc1' : typecheck .ioFree ctxᵢ e1 fuel' = .ok res1 := by
    simpa [typecheck, Nat.succ_sub_one] using htc1
  have hIH_e1 := IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
    e1 ctxᵢ hwfTm res1 htc1'
  have hstep_e1 :=
    hIH_e1 hpredlaws hwfTm μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cfg₀1 cfg₁1 (Value.bool b₀) (Value.bool b₁)
      hθ₀ hθ₁ hwf hric₀ hric₁ htagR hRbound hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ ht₀_e1 ht₁_e1
  rcases hstep_e1 with ⟨hresTm1, hstep_e1⟩
  rcases hstep_e1 with ⟨θ₀1, θ₁1, hθext₀1, hθext₁1, _hvtyp₀1, _hvtyp₁1, hwfTm1, hwf1, hwfcf₀1, hwfcf₁1, hric₀1, hric₁1, htagR1, hcwr₀1, hcwr₁1, hagree1, hvalc₀1, hvalc₁1, hres_agree1⟩
  let ctx' := { ctxᵢ with
    memEnv := res1.memEnv'
    tagEnv := res1.tagEnv'
    nextLoc := res1.nextLoc'
    nextTag := res1.nextTag'
    regime := res1.regime' }
  let pc' := joinPoison ctxᵢ.pc res1.qualType.poison
  let ctx'' := { ctx' with pc := pc' }
  let ctxForE3 := { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag' }
  let resJoin : TypeResult := {
    qualType := ⟨joinETyps res2.qualType.etyp res3.qualType.etyp
        res2.qualType.poison res3.qualType.poison,
      joinPoison pc' (joinPoison res2.qualType.poison res3.qualType.poison),
      match joinETyps res2.qualType.etyp res3.qualType.etyp
          res2.qualType.poison res3.qualType.poison with
      | ETyp.arrow _ _ _ _ => Predicate.noPred
      | ETyp.parrow _ _ _ _ => Predicate.noPred
      | _ => joinPredicates res2.qualType.pred res3.qualType.pred⟩
    memEnv' := joinMemEnvsStrong res2.memEnv' res3.memEnv'
    tagEnv' := joinTagEnvs res2.tagEnv' res3.tagEnv'
    nextLoc' := max res2.nextLoc' res3.nextLoc'
    nextTag' := max res2.nextTag' res3.nextTag'
    regime' := joinRegimes res2.regime' res3.regime' }
  have hθ₀1wf : wfRealizationMap θ₀1 := hθext₀1.2 hθ₀
  have hθ₁1wf : wfRealizationMap θ₁1 := hθext₁1.2 hθ₁
  have htcIf : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr_ite_succ] using htc
  have htc2' : typecheck .ioFree ctx'' e2 fuel' = .ok res2 := by
    simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2
  have htc3' : typecheck .ioFree ctxForE3 e3 fuel' = .ok res3 := by
    simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3
  have hpredNo : res.qualType.pred = Predicate.noPred := by
    exact
      typecheckIf_standard_pred_noPred
        ctxᵢ e1 e2 e3 (Nat.succ fuel') res htcIf
        ⟨err, by simpa [Nat.succ_sub_one] using hmatch_fail⟩
  have hetyp_res :
      res.qualType.etyp = joinETyps res2.qualType.etyp res3.qualType.etyp
        res2.qualType.poison res3.qualType.poison := by
    exact
      typecheckIf_standard_etyp'
        ctxᵢ e1 e2 e3 (Nat.succ fuel') res res1 res2 res3
        htcIf ⟨err, by simpa [Nat.succ_sub_one] using hmatch_fail⟩
        (by simpa [Nat.succ_sub_one] using htc1)
        hbool
        (by simpa [ctx'', ctx', pc', Nat.succ_sub_one] using htc2)
        (by simpa [ctxForE3, ctx'', ctx', pc', Nat.succ_sub_one] using htc3)
  have hcompat23 : beqETypSignature res2.qualType.etyp res3.qualType.etyp = true := by
    by_contra hcompat
    have hcompat' : beqETypSignature res2.qualType.etyp res3.qualType.etyp = false := by
      cases h : beqETypSignature res2.qualType.etyp res3.qualType.etyp <;> simp_all
    have htcIf_err :
        typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') =
          .error s!"Branches of if must have same type" := by
      cases hq1 : res1.qualType with
      | mk etyp1 p1 pred1 =>
          have hbool1 : etyp1 = ETyp.bool := by
            simpa [hq1] using hbool
          subst etyp1
          have hp1_eq : p1 = res1.qualType.poison := by
            simp [hq1]
          have htc2_expr :
              typecheckExpr .ioFree ctx'' e2 fuel' = .ok res2 := by
            simpa [ctx'', ctx', pc', Nat.succ_sub_one] using htc2
          have htc2_raw :
              typecheckExpr .ioFree
                { pc := joinPoison ctxᵢ.pc p1
                , regime := res1.regime'
                , memEnv := res1.memEnv'
                , varEnv := ctxᵢ.varEnv
                , tagEnv := res1.tagEnv'
                , nextLoc := res1.nextLoc'
                , nextTag := res1.nextTag'
                , pureCtx := ctxᵢ.pureCtx } e2 fuel' = .ok res2 := by
            simpa [ctx'', ctx', pc', hq1] using htc2_expr
          have htc3_expr :
              typecheckExpr .ioFree ctxForE3 e3 fuel' = .ok res3 := by
            simpa [ctxForE3, ctx'', ctx', pc', Nat.succ_sub_one] using htc3
          have htc3_raw :
              typecheckExpr .ioFree
                { pc := joinPoison ctxᵢ.pc p1
                , regime := res1.regime'
                , memEnv := res1.memEnv'
                , varEnv := ctxᵢ.varEnv
                , tagEnv := res1.tagEnv'
                , nextLoc := res2.nextLoc'
                , nextTag := res2.nextTag'
                , pureCtx := ctxᵢ.pureCtx } e3 fuel' = .ok res3 := by
            simpa [ctxForE3, ctx'', ctx', pc', hq1] using htc3_expr
          unfold typecheckIf
          rw [hmatch_fail, htc1]
          simp only [bind, Except.bind]
          simp [hq1]
          rw [htc2_raw]
          simp
          rw [htc3_raw]
          cases hq2 : res2.qualType with
          | mk etyp2 p2 pred2 =>
              cases hq3 : res3.qualType with
              | mk etyp3 p3 pred3 =>
                  have hcompat'' : beqETypSignature etyp2 etyp3 = false := by
                    simpa [hq2, hq3] using hcompat'
                  simp [Except.pure, hq3, hcompat'', pure]
    rw [htcIf_err] at htcIf
    cases htcIf
  have hjoin :
      joinTypeResults ctx'' res2 [res3] = .ok resJoin := by
    cases hq2 : res2.qualType with
    | mk etyp2 p2 pred2 =>
        cases hq3 : res3.qualType with
        | mk etyp3 p3 pred3 =>
            have hcompat23' : beqETypSignature etyp2 etyp3 = true := by
              simpa [hq2, hq3] using hcompat23
            unfold joinTypeResults
            simp [resJoin, ctx'', hq2, hq3, hcompat23', bind, Except.bind, pure, Except.pure]
            rfl
  have hresJoin_etyp : resJoin.qualType.etyp = res.qualType.etyp := by
    simpa [resJoin] using hetyp_res.symm
  have hresJoin_poison : resJoin.qualType.poison = res.qualType.poison := by
    simp [resJoin, pc', hpoison, joinPoison, Bool.or_assoc]
  have hmono1 : Regime.monotoneStep ctxᵢ.regime res1.regime' := by
    simpa [ctxAfter] using regime_monotone ctxᵢ e1 fuel' res1 htc1'
  have hmono2 : Regime.monotoneStep res1.regime' res2.regime' := by
    simpa [ctxAfter, ctx'', ctx', pc'] using regime_monotone ctx'' e2 fuel' res2 htc2'
  have hmono3 : Regime.monotoneStep res1.regime' res3.regime' := by
    simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using regime_monotone ctxForE3 e3 fuel' res3 htc3'
  have hRbound1 :
      regimeBounded (ctxAfter ctxᵢ res1).regime :=
    regimeBounded_of_monotoneStep ctxᵢ.regime (ctxAfter ctxᵢ res1).regime hRbound hmono1
  have hwf_ctx'' : wfTypeContext ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter, wfTypeContext] using hwf1
  have hwfTm_ctx'' : wfTagMeaningCtx tm ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter] using hwfTm1
  have hric₀1_ctx'' : runtimeInstantiatesCtx ctx'' cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₀1
  have hric₁1_ctx'' : runtimeInstantiatesCtx ctx'' cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₁1
  have hcwr₀1_ctx'' :
      consistentWithRegime predSat ctx''.regime ctx''
        cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₀1
  have hcwr₁1_ctx'' :
      consistentWithRegime predSat ctx''.regime ctx''
        cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₁1
  have htagR_ctx'' : regimeConsistentWithCtx ctx'' := by
    simpa [ctx'', ctx', pc', ctxAfter, regimeConsistentWithCtx] using htagR1
  have hRbound_ctx'' : regimeBounded ctx''.regime := by
    simpa [ctx'', ctx', pc', ctxAfter] using hRbound1
  have hagree1_ctx'' :
      agreeOnClean predSat ctx''.regime ctx''
        cfg₀1.memory cfg₀1.varEnv θ₀1 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctx'', ctx', pc', ctxAfter] using hagree1
  have hnextLoc_mono :
      res1.nextLoc' ≤ res2.nextLoc' := by
    have : ctx''.nextLoc ≤ res2.nextLoc' :=
      typecheck_nextLoc_mono ctx'' e2 fuel' res2
        (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
    simpa [ctx'', ctx'] using this
  have hnextTag_mono :
      res1.nextTag' ≤ res2.nextTag' := by
    have : ctx''.nextTag ≤ res2.nextTag' :=
      typecheck_nextTag_mono .ioFree ctx'' e2 fuel' res2
        (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
    simpa [ctx'', ctx'] using this
  have hwfTm_ctxForE3 : wfTagMeaningCtx tm ctxForE3 := by
    simpa [ctxForE3, ctx'', ctx', pc'] using hwfTm1
  have hwf_ctxForE3 : wfTypeContext ctxForE3 := by
    intro l hl
    simp only [ctxForE3, ctx'', ctx'] at hl ⊢
    exact Nat.lt_of_lt_of_le (hwf1 l hl) hnextLoc_mono
  have hric₀1_ctxForE3 :
      runtimeInstantiatesCtx ctxForE3 cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₀1
  have hric₁1_ctxForE3 :
      runtimeInstantiatesCtx ctxForE3 cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, runtimeInstantiatesCtx] using hric₁1
  have hcwr₀1_ctxForE3 :
      consistentWithRegime predSat ctxForE3.regime ctxForE3
        cfg₀1.memory cfg₀1.varEnv θ₀1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₀1
  have hcwr₁1_ctxForE3 :
      consistentWithRegime predSat ctxForE3.regime ctxForE3
        cfg₁1.memory cfg₁1.varEnv θ₁1 := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter, consistentWithRegime] using hcwr₁1
  have htagR_ctxForE3 : regimeConsistentWithCtx ctxForE3 := by
    constructor
    · show tagEnvConsistentWithRegime ctxForE3.tagEnv ctxForE3.regime
      simpa [ctxForE3, ctx'', ctx', pc', regimeConsistentWithCtx] using htagR1.1
    · show ctxForE3.regime.bound ≤ ctxForE3.nextTag
      simpa [ctxForE3, ctx'', ctx', pc'] using Nat.le_trans htagR1.2 hnextTag_mono
  have hRbound_ctxForE3 : regimeBounded ctxForE3.regime := by
    simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hRbound1
  cases hbranch₀ with
  | inl hbranch₀_true =>
      cases hbranch₁ with
      | inl hbranch₁_true =>
          have ht₀_e2 : terminatesTo .ioFree e2 cfg₀1 cf₀ o₀ := hbranch₀_true.2
          have ht₁_e2 : terminatesTo .ioFree e2 cfg₁1 cf₁ o₁ := hbranch₁_true.2
          have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
            rw [hpm₀1, hpm₁1]
          have hcfg₁1_eq :
              cfg₁1 =
                { memory := cfg₁1.memory
                , varEnv := cfg₁1.varEnv
                , nextAddr := cfg₁1.nextAddr
                , pureMode := cfg₀1.pureMode } := by
            cases cfg₁1
            simp only [Config.mk.injEq, true_and]
            exact hpm_eq
          have ht₁_e2' : terminatesTo .ioFree e2
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode }
              cf₁ o₁ := by
            rw [← hcfg₁1_eq]
            exact ht₁_e2
          have hwfcf₁1' : wfConfig
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode } := by
            rw [← hcfg₁1_eq]
            exact hwfcf₁1
          have hIH_e2 :=
            IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' hwfTm_ctx'' res2 htc2'
          have hstep_e2 :=
            hIH_e2 hpredlaws hwfTm_ctx''
              cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
              cf₀ cf₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwf_ctx'' hric₀1_ctx'' hric₁1_ctx'' htagR_ctx'' hRbound_ctx''
              hcwr₀1_ctx'' hcwr₁1_ctx'' hagree1_ctx''
              cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
              ht₀_e2 ht₁_e2'
          rcases hstep_e2 with ⟨_hresTm2, hstep_e2⟩
          rcases hstep_e2 with
            ⟨θ₀2, θ₁2, hθext₀2, hθext₁2, hvtyp₀2, hvtyp₁2, _hwfTm2, _hwf2, hwfcf₀2, hwfcf₁2,
              hric₀2, hric₁2, _htagR2, hcwr₀2, hcwr₁2, hagree2, hvalc₀2, hvalc₁2, hres_agree2⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
          have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
          have hric₀_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀2 := by
            refine
              ite_join_transport_runtimeInstantiatesCtx
                (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                hjoin ?_ hric₀2
            intro l hcontains
            rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
            rcases
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  res2.memEnv' res3.memEnv' l qt2 hlookup2
              with ⟨qt, hlookup_join⟩
            exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
          have hric₁_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁2 := by
            refine
              ite_join_transport_runtimeInstantiatesCtx
                (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                hjoin ?_ hric₁2
            intro l hcontains
            rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
            rcases
                joinMemEnvsStrong_lookup_some_of_left_lookup
                  res2.memEnv' res3.memEnv' l qt2 hlookup2
              with ⟨qt, hlookup_join⟩
            exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
          have hcwr₀_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀2 := by
            exact
              consistentWithRegime_join_from_left
                predSat ctx'' res2 res3 resJoin
                cf₀.memory cf₀.varEnv θ₀2
                rfl rfl hcwr₀2
          have hcwr₁_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₁.memory cf₁.varEnv θ₁2 := by
            exact
              consistentWithRegime_join_from_left
                predSat ctx'' res2 res3 resJoin
                cf₁.memory cf₁.varEnv θ₁2
                rfl rfl hcwr₁2
          have h_clean_join_to_res2 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                qtypCleanUnder (ctxAfter ctx'' res2).regime qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                have hk2 :
                    (ctxAfter ctx'' res2).regime.lookup? k = some true :=
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                    hjoin (by simp) k true hk
                exact qtypCleanUnder.guard k htag hk2 hnotfun
          have h_mem_from_res2_or_unrealized :
              ∀ l qt,
                (ctxAfter ctx'' resJoin).memEnv.lookup l = some qt →
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                ((∃ qt2,
                    (ctxAfter ctx'' res2).memEnv.lookup l = some qt2 ∧
                    qtypCleanUnder (ctxAfter ctx'' res2).regime qt2 ∧
                    qt.etyp = qt2.etyp ∧
                    (qt.poison = false → qt2.poison = false)) ∨
                  (θ₀2.lookup l = none ∧ θ₁2.lookup l = none)) := by
            intro l qt hlookup hclean
            by_cases hlookup2_none : (ctxAfter ctx'' res2).memEnv.lookup l = none
            · right
              have hnot_contains2 : ¬ (ctxAfter ctx'' res2).memEnv.contains l := by
                intro hcontains
                have hmem : l ∈ (ctxAfter ctx'' res2).memEnv :=
                  (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                have hlookup_isSome :
                    ((ctxAfter ctx'' res2).memEnv[l]?).isSome = true :=
                  (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                have hlookup_get_none :
                    (ctxAfter ctx'' res2).memEnv[l]? = none := by
                  simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
                simp [hlookup_get_none] at hlookup_isSome
              have hθ₀2_none :
                  θ₀2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res2))
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                  (l := l) hric₀2 hnot_contains2
              have hθ₁2_none :
                  θ₁2.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res2))
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                  (l := l) hric₁2 hnot_contains2
              exact ⟨hθ₀2_none, hθ₁2_none⟩
            · left
              rcases Option.ne_none_iff_exists'.1 hlookup2_none with ⟨qt2, hlookup2⟩
              have hclean2 : qtypCleanUnder (ctxAfter ctx'' res2).regime qt2 :=
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hclean hlookup2
              have hetyp2 : qt.etyp = qt2.etyp :=
                joinTypeResults_lookup_member_etyp_compat
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hlookup2
              have hpoison2 : qt.poison = false → qt2.poison = false :=
                joinTypeResults_lookup_member_poison_imp
                  (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt2 hlookup hlookup2
              exact ⟨qt2, hlookup2, hclean2, hetyp2, hpoison2⟩
          have hlookup_back_join_to_res2 :
              ∀ k b,
                (ctxAfter ctx'' resJoin).regime.lookup? k = some b →
                (ctxAfter ctx'' res2).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                hjoin (by simp) k b hk
          have hagree_join :
              agreeOnClean predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
            exact
              ite_join_transport_agreeOnClean_from_member
                (predSat := predSat)
                (ctx := ctx'')
                (first := res2)
                (src := res2)
                (rest := [res3])
                (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                (θ₀ := θ₀2) (θ₁ := θ₁2)
                hjoin (by simp) hagree2
                h_clean_join_to_res2
                h_mem_from_res2_or_unrealized
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res2 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res2).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res2 h)
          have hresTm :
              QTypRespectsTagMeaning tm res.qualType :=
            typecheckExpr_preserves_QTypRespectsTagMeaning
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwfTm_final : wfTagMeaningCtx tm (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_wfTagMeaningCtx
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀2 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvtyp₀2
          have hvtyp₁_join : valueHasETyp θ₁2 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvtyp₁2
          have hvtyp₀_final : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁2 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hagree_join
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀2 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvalc₀2
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁2 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvalc₁2
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀2 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀2 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀2 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁2 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁2 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁2 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hres_agree_join :
              resultAgreesIfClean predSat
                (ctxAfter ctx'' resJoin).regime
                cf₀.memory cf₁.memory θ₀2 θ₁2 resJoin.qualType o₀ o₁ := by
            exact
              joinTypeResults_transport_resultAgreesIfClean_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀2) (θ₁ := θ₁2)
                (o₀ := o₀) (o₁ := o₁)
                hjoin (by simp) hres_agree2
          have hres_agree_final :
              resultAgreesIfClean predSat
                (ctxAfter ctxᵢ res).regime
                cf₀.memory cf₁.memory θ₀2 θ₁2 res.qualType o₀ o₁ := by
            intro hclean
            have hclean_resJoin_reg :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime res.qualType := by
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hclean
            have hclean_join :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime resJoin.qualType := by
              cases hclean with
              | clean hpoison_res =>
                  exact qtypCleanUnder.clean (by simpa [hresJoin_poison] using hpoison_res)
              | guard k htag _hk _hnotfun =>
                  exfalso
                  simp [qtypGuardTag, hpredNo] at htag
            have hagree_join :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀2 θ₁2
                  resJoin.qualType o₀ o₁ :=
              hres_agree_join hclean_join
            have hpoison_imp :
                res.qualType.poison = false → resJoin.qualType.poison = false := by
              intro hpoison_res
              simpa [hresJoin_poison] using hpoison_res
            have hagree_res :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀2 θ₁2
                  res.qualType o₀ o₁ :=
              agreeValueUnder_transport_clean
                hclean_resJoin_reg hresJoin_etyp.symm hpoison_imp hagree_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hagree_res
          exact
            ⟨hresTm, θ₀2, θ₁2, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, hwfcf₀2, hwfcf₁2,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final, hres_agree_final⟩
      | inr hbranch₁_false =>
          have ht₀_e2 : terminatesTo .ioFree e2 cfg₀1 cf₀ o₀ := hbranch₀_true.2
          have ht₁_e3 : terminatesTo .ioFree e3 cfg₁1 cf₁ o₁ := hbranch₁_false.2
          have hpc_true : pc' = true := by
            cases hpc_val : pc' with
            | true =>
                rfl
            | false =>
                have hpoison1_false : res1.qualType.poison = false := by
                  have hjoin_false : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
                    simpa [pc'] using hpc_val
                  exact (joinPoison_eq_false hjoin_false).2
                have hclean1 :
                    qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                  qtypCleanUnder.clean hpoison1_false
                have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
                  intro ⟨ls, hls⟩
                  simp [hbool] at hls
                have hnotfun1 : res1.qualType.etyp.isFunctionType = false := by
                  simp [hbool, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hEq_bool : Value.bool b₀ = Value.bool b₁ :=
                  agreeValueUnder_nonref_eq_of_clean
                    hclean1 hnotref1 hnotfun1 (hres_agree1 hclean1)
                cases hEq_bool
                simp [hbranch₀_true.1] at hbranch₁_false
          have hpc'' : ctx''.pc = true := by
            simpa [ctx'', pc'] using hpc_true
          have hpcForE3 : ctxForE3.pc = true := by
            simpa [ctxForE3, ctx'', pc'] using hpc_true
          have hsingle_e2 :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' hwfTm_ctx'' res2 htc2'
          have hsingle_e3 :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 hwfTm_ctxForE3 res3 htc3'
          rcases
              hsingle_e2 hpredlaws hwfTm_ctx''
                cfg₀1.memory cfg₀1.varEnv θ₀1 cf₀ o₀
                hθ₀1wf hwf_ctx'' hric₀1_ctx'' htagR_ctx'' hRbound_ctx''
                hcwr₀1_ctx'' cfg₀1.nextAddr cfg₀1.pureMode hwfcf₀1 ht₀_e2 hpc''
            with ⟨θ₀2, hθext₀2, hvtyp₀2, hric₀2, hcwr₀2, hvalc₀2, hpres₂⟩
          rcases
              hsingle_e3 hpredlaws hwfTm_ctxForE3
                cfg₁1.memory cfg₁1.varEnv θ₁1 cf₁ o₁
                hθ₁1wf hwf_ctxForE3 hric₁1_ctxForE3 htagR_ctxForE3 hRbound_ctxForE3
                hcwr₁1_ctxForE3 cfg₁1.nextAddr cfg₁1.pureMode hwfcf₁1 ht₁_e3 hpcForE3
            with ⟨θ₁3, hθext₁3, hvtyp₁3, hric₁3, hcwr₁3, hvalc₁3, hpres₃⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀2 := wfExtendsMap_trans hθext₀1 hθext₀2
          have hθext₁ : wfExtendsMap θ₁ θ₁3 := wfExtendsMap_trans hθext₁1 hθext₁3
          have hlookup_back_final_to_res1 :
              ∀ k b,
                (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                res1.regime'.lookup? k = some b := by
            intro k b hk
            have hk_join : (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
              simpa [ctxAfter, hregime'] using hk
            have hk2 : res2.regime'.lookup? k = some b :=
              joinRegimes_lookup_some_left res2.regime' res3.regime' k b hk_join
            exact monotoneStep_lookup_back hmono2 k b hk2
          have hclean_final_to_res1 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                qtypCleanUnder res1.regime' qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                exact qtypCleanUnder.guard k htag (hlookup_back_final_to_res1 k true hk) hnotfun
          have hmemberVars₀_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberVarsRegimeEvidence predSat res1.regime' cf₀.memory σcap ρcap →
                  MemberVarsRegimeEvidence predSat res.regime' cf₀.memory σcap ρcap := by
            intro σcap ρcap h
            exact
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₀.memory)
                hlookup_back_final_to_res1 h
          have hmemberCvcr₀_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberCvcrEvidence predSat res1.regime' cf₀.memory θ₀2 σcap ρcap →
                  MemberCvcrEvidence predSat res.regime' cf₀.memory θ₀2 σcap ρcap := by
            intro σcap ρcap h
            exact
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₀.memory)
                hlookup_back_final_to_res1 h
          have hmemberVars₁_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberVarsRegimeEvidence predSat res1.regime' cf₁.memory σcap ρcap →
                  MemberVarsRegimeEvidence predSat res.regime' cf₁.memory σcap ρcap := by
            intro σcap ρcap h
            exact
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₁.memory)
                hlookup_back_final_to_res1 h
          have hmemberCvcr₁_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberCvcrEvidence predSat res1.regime' cf₁.memory θ₁3 σcap ρcap →
                  MemberCvcrEvidence predSat res.regime' cf₁.memory θ₁3 σcap ρcap := by
            intro σcap ρcap h
            exact
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₁.memory)
                hlookup_back_final_to_res1 h
          have hclean_back_to_res1 :
              ∀ l qt_out,
                res.memEnv'.lookup l = some qt_out →
                qtypCleanUnder res.regime' qt_out →
                ∃ qt_mid,
                  res1.memEnv'.lookup l = some qt_mid ∧
                  qtypCleanUnder res1.regime' qt_mid := by
            intro l qt_out hlookup_out hclean_out
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [hmemEnv] using hlookup_out
            have hcontains_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
              memEnv_contains_of_lookup_some
                (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
            rcases
                joinMemEnvsStrong_contains_implies_or
                  res2.memEnv' res3.memEnv' l hcontains_join
              with hcontains2 | hcontains3
            · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                ⟨qt2, hlookup2⟩
              have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                cases hclean_out with
                | clean hpoison_out =>
                    have henv2 : res2.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup2] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_left
                          res2.memEnv' res3.memEnv' l qt_out
                          hlookup_join hpoison_out henv2
                      with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                    have hqt2 : qt2 = qt2' := by
                      rw [hlookup2] at hlookup2'
                      injection hlookup2'
                    cases hqt2
                    exact qtypCleanUnder.clean hpoison2
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [hregime'] using hk
                    have htag2 : qtypGuardTag qt2 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_left
                        res2.memEnv' res3.memEnv' l qt_out qt2 k
                        hlookup_join hlookup2 htag
                    have hk2 : res2.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_left
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun2 : qt2.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                      native_decide
                    exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
              exact
                typecheckExpr_clean_lookup_origin_of_pc_true
                  ctx'' e2 fuel' res2 htc2' hpc''
                  l qt2 hlookup2 hclean2
            · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                ⟨qt3, hlookup3⟩
              have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                cases hclean_out with
                | clean hpoison_out =>
                    have henv3 : res3.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup3] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_right
                          res2.memEnv' res3.memEnv' l qt_out
                          hlookup_join hpoison_out henv3
                      with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                    have hqt3 : qt3 = qt3' := by
                      rw [hlookup3] at hlookup3'
                      injection hlookup3'
                    cases hqt3
                    exact qtypCleanUnder.clean hpoison3
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [hregime'] using hk
                    have htag3 : qtypGuardTag qt3 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_right
                        res2.memEnv' res3.memEnv' l qt_out qt3 k
                        hlookup_join hlookup3 htag
                    have hk3 : res3.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_right
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun3 : qt3.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                      native_decide
                    exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
              exact
                typecheckExpr_clean_lookup_origin_of_pc_true
                  ctxForE3 e3 fuel' res3 htc3' hpcForE3
                  l qt3 hlookup3 hclean3
          have hric₁3_src :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₁3
          have hcwr₁3_src :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc', consistentWithRegime] using hcwr₁3
          have hvar_cf₀ : cf₀.varEnv = cfg₀1.varEnv := by
            rcases ht₀_e2 with ⟨fuel₀w, verbose₀w, hpure₀w⟩
            have heq₀w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₀w
            have ht₀w :
                terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld
                  e2 cfg₀1 cf₀ o₀ := by
              exact ⟨fuel₀w, verbose₀w, by simpa [pure] using heq₀w⟩
            rcases ht₀w with ⟨fuel₀', verbose₀', heval₀'⟩
            have hvar_eq :=
              beval_preserves_varEnv .ioFree e2 fuel₀' verbose₀'
                cfg₀1 cf₀ o₀
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₀'⟩
            simpa using hvar_eq.symm
          have hvar_cf₁ : cf₁.varEnv = cfg₁1.varEnv := by
            rcases ht₁_e3 with ⟨fuel₁w, verbose₁w, hpure₁w⟩
            have heq₁w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₁w
            have ht₁w :
                terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld
                  e3 cfg₁1 cf₁ o₁ := by
              exact ⟨fuel₁w, verbose₁w, by simpa [pure] using heq₁w⟩
            rcases ht₁w with ⟨fuel₁', verbose₁', heval₁'⟩
            have hvar_eq :=
              beval_preserves_varEnv .ioFree e3 fuel₁' verbose₁'
                cfg₁1 cf₁ o₁
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₁'⟩
            simpa using hvar_eq.symm
          have hresTm :
              QTypRespectsTagMeaning tm res.qualType :=
            typecheckExpr_preserves_QTypRespectsTagMeaning
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwfTm_final : wfTagMeaningCtx tm (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_wfTagMeaningCtx
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀2 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvtyp₀2
          have hvtyp₁_join : valueHasETyp θ₁3 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvtyp₁3
          have hvtyp₀_final : valueHasETyp θ₀2 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀2 := by
            have hric₀_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀2 := by
              refine
                ite_join_transport_runtimeInstantiatesCtx
                  (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀2)
                  hjoin ?_ hric₀2
              intro l hcontains
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
              rcases
                  joinMemEnvsStrong_lookup_some_of_left_lookup
                    res2.memEnv' res3.memEnv' l qt2 hlookup2
                with ⟨qt, hlookup_join⟩
              exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁3 := by
            have hric₁_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁3 := by
              unfold runtimeInstantiatesCtx at hric₁3_src ⊢
              constructor
              · intro l a hθlookup
                rcases hric₁3_src.1 l a hθlookup with ⟨hcontains3, hmem⟩
                rcases
                    memEnv_lookup_some_of_contains
                      (ctxAfter ctx'' res3).memEnv l hcontains3
                  with ⟨qt3, hlookup3ctx⟩
                have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                  simpa [ctxAfter] using hlookup3ctx
                rcases
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      res2.memEnv' res3.memEnv' l qt3 hlookup3
                  with ⟨qt, hlookup_join⟩
                have hcontains_join :
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                  memEnv_contains_of_lookup_some
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                exact ⟨by simpa [ctxAfter] using hcontains_join, hmem⟩
              · intro x qt hlookup
                have hlookup' :
                    (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                  simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                exact hric₁3_src.2 hlookup'
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 := by
            have hcwr₀_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₀.memory cf₀.varEnv θ₀2 := by
              exact
                consistentWithRegime_join_from_left
                  predSat ctx'' res2 res3 resJoin
                  cf₀.memory cf₀.varEnv θ₀2
                  rfl rfl hcwr₀2
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁3 := by
            have hcwr₁_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₁.memory cf₁.varEnv θ₁3 := by
              exact
                consistentWithRegime_join_from_right
                  predSat ctx'' res2 res3 resJoin
                  cf₁.memory cf₁.varEnv θ₁3
                  rfl rfl hcwr₁3_src
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀2 cf₁.memory cf₁.varEnv θ₁3 := by
            constructor
            · intro l qt hlookup hclean
              have hlookup_res : res.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup
              have hlookup_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                simpa [hmemEnv] using hlookup_res
              rcases hclean_back_to_res1 l qt hlookup_res (by simpa [ctxAfter] using hclean) with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              have hcontains_mid :
                  res1.memEnv'.contains l :=
                memEnv_contains_of_lookup_some res1.memEnv' l qt_mid hlookup_mid
              have hcontains2 : res2.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved
                  ctx'' e2 fuel' res2
                  (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                  l
                  (by simpa [ctx'', ctx'] using hcontains_mid)
              have hcontains3 : res3.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved
                  ctxForE3 e3 fuel' res3
                  (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                  l
                  (by simpa [ctxForE3, ctx'', ctx'] using hcontains_mid)
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
              have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                cases hclean with
                | clean hpoison_out =>
                    have henv2 : res2.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup2] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_left
                          res2.memEnv' res3.memEnv' l qt
                          hlookup_join hpoison_out henv2
                      with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                    have hqt2 : qt2 = qt2' := by
                      rw [hlookup2] at hlookup2'
                      injection hlookup2'
                    cases hqt2
                    exact qtypCleanUnder.clean hpoison2
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [ctxAfter, hregime'] using hk
                    have htag2 : qtypGuardTag qt2 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_left
                        res2.memEnv' res3.memEnv' l qt qt2 k
                        hlookup_join hlookup2 htag
                    have hk2 : res2.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_left
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun2 : qt2.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                      native_decide
                    exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
              have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                cases hclean with
                | clean hpoison_out =>
                    have henv3 : res3.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup3] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_right
                          res2.memEnv' res3.memEnv' l qt
                          hlookup_join hpoison_out henv3
                      with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                    have hqt3 : qt3 = qt3' := by
                      rw [hlookup3] at hlookup3'
                      injection hlookup3'
                    cases hqt3
                    exact qtypCleanUnder.clean hpoison3
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [ctxAfter, hregime'] using hk
                    have htag3 : qtypGuardTag qt3 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_right
                        res2.memEnv' res3.memEnv' l qt qt3 k
                        hlookup_join hlookup3 htag
                    have hk3 : res3.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_right
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun3 : qt3.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                      native_decide
                    exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
              have hlookup_mid_ctx'' : ctx''.memEnv.lookup l = some qt_mid := by
                simpa [ctx'', ctx'] using hlookup_mid
              have hlookup_mid_ctxForE3 : ctxForE3.memEnv.lookup l = some qt_mid := by
                simpa [ctxForE3, ctx'', ctx'] using hlookup_mid
              have hpres_l₀ :
                  PreservesInheritedCleanLocOneRun cfg₀1.memory cf₀.memory θ₀1 θ₀2 l :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctx'') (res := res2)
                  (μ_in := cfg₀1.memory) (μ_out := cf₀.memory)
                  (θ_in := θ₀1) (θ_out := θ₀2)
                  hpres₂ hlookup_mid_ctx'' hlookup2 hclean2
              have hpres_l₁ :
                  PreservesInheritedCleanLocOneRun cfg₁1.memory cf₁.memory θ₁1 θ₁3 l :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxForE3) (res := res3)
                  (μ_in := cfg₁1.memory) (μ_out := cf₁.memory)
                  (θ_in := θ₁1) (θ_out := θ₁3)
                  hpres₃ hlookup_mid_ctxForE3 hlookup3 hclean3
              have hagree_mid :
                  agreeLocUnder predSat res1.regime'
                    cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt_mid) :=
                hagree1.1 l qt_mid (by simpa [ctxAfter] using hlookup_mid) hclean_mid
              cases hagree_mid with
              | both_unrealized _ _ hnone₀ hnone₁ =>
                  have hnone₀' : θ₀2.lookup l = none := by
                    cases hpres_l₀ with
                    | both_unrealized _ hnone_out =>
                        exact hnone_out
                    | preserve_value _ _ hsome_in _ _ _ =>
                        exact False.elim (Option.noConfusion (hnone₀.symm.trans hsome_in))
                  have hnone₁' : θ₁3.lookup l = none := by
                    cases hpres_l₁ with
                    | both_unrealized _ hnone_out =>
                        exact hnone_out
                    | preserve_value _ _ hsome_in _ _ _ =>
                        exact False.elim (Option.noConfusion (hnone₁.symm.trans hsome_in))
                  exact agreeLocUnder.both_unrealized l qt hnone₀' hnone₁'
              | agree_values _ _ a₀m a₁m n₀ n₁ hreal₀m hreal₁m hmem₀m hmem₁m hagreeVmid =>
                  cases hpres_l₀ with
                  | both_unrealized hnone_in _ =>
                      exact False.elim (Option.noConfusion (hreal₀m.symm.trans hnone_in))
                  | preserve_value a₀' n₀' hθ₀in hμ₀in hθ₀out hμ₀out =>
                      cases hpres_l₁ with
                      | both_unrealized hnone_in _ =>
                          exact False.elim (Option.noConfusion (hreal₁m.symm.trans hnone_in))
                      | preserve_value a₁' n₁' hθ₁in hμ₁in hθ₁out hμ₁out =>
                          have ha₀ : a₀' = a₀m := by
                            exact Option.some.inj (hθ₀in.symm.trans hreal₀m)
                          have hn₀ : n₀' = n₀ := by
                            rw [ha₀] at hμ₀in
                            exact Option.some.inj (hμ₀in.symm.trans hmem₀m)
                          have ha₁ : a₁' = a₁m := by
                            exact Option.some.inj (hθ₁in.symm.trans hreal₁m)
                          have hn₁ : n₁' = n₁ := by
                            rw [ha₁] at hμ₁in
                            exact Option.some.inj (hμ₁in.symm.trans hmem₁m)
                          cases ha₀
                          cases hn₀
                          cases ha₁
                          cases hn₁
                          have hnotref_mid : ¬ ∃ ls, qt_mid.etyp = ETyp.ref ls := by
                            intro ⟨ls, hls⟩
                            rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid] at hls
                            simp at hls
                          have hnotfun_mid : qt_mid.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid]
                            native_decide
                          have hEq_vals : Value.num n₀ = Value.num n₁ :=
                            agreeValueUnder_nonref_eq_of_clean
                              hclean_mid hnotref_mid hnotfun_mid hagreeVmid
                          have hnotref_final : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
                            intro ⟨ls, hls⟩
                            rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup] at hls
                            simp at hls
                          have hagreeV_final :
                              agreeValueUnder predSat res.regime'
                                cf₀.memory cf₁.memory θ₀2 θ₁3 qt (Value.num n₀) (Value.num n₁) := by
                            cases hclean with
                            | clean hpoison =>
                                have hnotfun_final : qt.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup]
                                  native_decide
                                exact
                                  agreeValueUnder.clean_eq_nonref_nonarrow
                                    hpoison hnotfun_final hnotref_final hEq_vals
                            | guard k htag hk hnotfun =>
                                exact
                                  agreeValueUnder.withPred_true_eq
                                    k htag hk hnotfun hnotref_final hEq_vals
                          exact
                            agreeLocUnder.agree_values
                              l qt a₀m a₁m n₀ n₁
                              hθ₀out hθ₁out hμ₀out hμ₁out hagreeV_final
            · intro x qt hlookup hclean
              have hclean_mid : qtypCleanUnder res1.regime' qt :=
                hclean_final_to_res1 qt hclean
              have hagree_mid :
                  agreeVarUnder predSat res1.regime'
                    cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
                hagree1.2 x qt (by simpa [ctxAfter] using hlookup) hclean_mid
              cases hagree_mid with
              | both_none _ _ hnone₀ hnone₁ =>
                  exact
                    agreeVarUnder.both_none x qt
                      (by simpa [hvar_cf₀] using hnone₀)
                      (by simpa [hvar_cf₁] using hnone₁)
              | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagreeVmid =>
                  have hagreeV_ext :
                      agreeValueUnder predSat res1.regime'
                        cf₀.memory cf₁.memory θ₀2 θ₁3 qt v₀ v₁ := by
                    exact
                      agreeValueUnder_clean_extends_transport_mem
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 cfg₀1.memory cf₀.memory)
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 cfg₁1.memory cf₁.memory)
                        hclean_mid hθext₀2.1 hθext₁3.1 hagreeVmid
                  have hagreeV_final :
                      agreeValueUnder predSat res.regime'
                        cf₀.memory cf₁.memory θ₀2 θ₁3 qt v₀ v₁ :=
                    agreeValueUnder_clean_transport_by_cleanBack
                      (predSat := predSat)
                      (R := res1.regime') (R' := res.regime')
                      (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                      (θ₀ := θ₀2) (θ₁ := θ₁3)
                      (qt := qt) (v₀ := v₀) (v₁ := v₁)
                      hclean_final_to_res1
                      hmemberVars₀_transport hmemberCvcr₀_transport
                      hmemberVars₁_transport hmemberCvcr₁_transport
                      hclean hagreeV_ext
                  exact
                    agreeVarUnder.agree_values x qt v₀ v₁
                      (by simpa [hvar_cf₀] using hlookup₀)
                      (by simpa [hvar_cf₁] using hlookup₁)
                      hagreeV_final
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀2 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀2) (v := o₀)
                hjoin (by simp) hvalc₀2
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁3 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvalc₁3
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀2 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀2 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀2 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁3 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁3 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁3 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hwfcf₀_final : wfConfig cf₀ := by
            exact (wfConfig_preserved .ioFree e2 _ cf₀ o₀ ht₀_e2 hwfcf₀1).1
          have hwfcf₁_final : wfConfig cf₁ := by
            exact (wfConfig_preserved .ioFree e3 _ cf₁ o₁ ht₁_e3 hwfcf₁1).1
          have hres_poison_true : res.qualType.poison = true := by
            calc
              res.qualType.poison =
                  joinPoison ctxᵢ.pc
                    (joinPoison res1.qualType.poison
                      (joinPoison res2.qualType.poison res3.qualType.poison)) := hpoison
              _ = true := by
                have hpc_or : ctxᵢ.pc = true ∨ res1.qualType.poison = true := by
                  have hpc_res1 : joinPoison ctxᵢ.pc res1.qualType.poison = true := by
                    simpa [pc'] using hpc_true
                  cases hctx : ctxᵢ.pc <;> cases hp1 : res1.qualType.poison <;>
                    simp [joinPoison, hctx, hp1] at hpc_res1 ⊢
                cases hpc_or with
                | inl hctx =>
                    simp [joinPoison, hctx]
                | inr hp1 =>
                    simp [joinPoison, hp1]
          exact
            ⟨hresTm, θ₀2, θ₁3, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, hwfcf₀_final, hwfcf₁_final,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final,
              resultAgreesIfClean_of_poison_noPred hres_poison_true hpredNo⟩
  | inr hbranch₀_false =>
      cases hbranch₁ with
      | inl hbranch₁_true =>
          have ht₀_e3 : terminatesTo .ioFree e3 cfg₀1 cf₀ o₀ := hbranch₀_false.2
          have ht₁_e2 : terminatesTo .ioFree e2 cfg₁1 cf₁ o₁ := hbranch₁_true.2
          have hpc_true : pc' = true := by
            cases hpc_val : pc' with
            | true =>
                rfl
            | false =>
                have hpoison1_false : res1.qualType.poison = false := by
                  have hjoin_false : joinPoison ctxᵢ.pc res1.qualType.poison = false := by
                    simpa [pc'] using hpc_val
                  exact (joinPoison_eq_false hjoin_false).2
                have hclean1 :
                    qtypCleanUnder (ctxAfter ctxᵢ res1).regime res1.qualType :=
                  qtypCleanUnder.clean hpoison1_false
                have hnotref1 : ¬ ∃ ls, res1.qualType.etyp = ETyp.ref ls := by
                  intro ⟨ls, hls⟩
                  simp [hbool] at hls
                have hnotfun1 : res1.qualType.etyp.isFunctionType = false := by
                  simp [hbool, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                have hEq_bool : Value.bool b₀ = Value.bool b₁ :=
                  agreeValueUnder_nonref_eq_of_clean
                    hclean1 hnotref1 hnotfun1 (hres_agree1 hclean1)
                cases hEq_bool
                simp [hbranch₀_false.1] at hbranch₁_true
          have hpc'' : ctx''.pc = true := by
            simpa [ctx'', pc'] using hpc_true
          have hpcForE3 : ctxForE3.pc = true := by
            simpa [ctxForE3, ctx'', pc'] using hpc_true
          have hsingle_e2 :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e2 ctx'' hwfTm_ctx'' res2 htc2'
          have hsingle_e3 :=
            singleIH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 hwfTm_ctxForE3 res3 htc3'
          rcases
              hsingle_e3 hpredlaws hwfTm_ctxForE3
                cfg₀1.memory cfg₀1.varEnv θ₀1 cf₀ o₀
                hθ₀1wf hwf_ctxForE3 hric₀1_ctxForE3 htagR_ctxForE3 hRbound_ctxForE3
                hcwr₀1_ctxForE3 cfg₀1.nextAddr cfg₀1.pureMode hwfcf₀1 ht₀_e3 hpcForE3
            with ⟨θ₀3, hθext₀3, hvtyp₀3, hric₀3, hcwr₀3, hvalc₀3, hpres₃⟩
          rcases
              hsingle_e2 hpredlaws hwfTm_ctx''
                cfg₁1.memory cfg₁1.varEnv θ₁1 cf₁ o₁
                hθ₁1wf hwf_ctx'' hric₁1_ctx'' htagR_ctx'' hRbound_ctx''
                hcwr₁1_ctx'' cfg₁1.nextAddr cfg₁1.pureMode hwfcf₁1 ht₁_e2 hpc''
            with ⟨θ₁2, hθext₁2, hvtyp₁2, hric₁2, hcwr₁2, hvalc₁2, hpres₂⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀3 := wfExtendsMap_trans hθext₀1 hθext₀3
          have hθext₁ : wfExtendsMap θ₁ θ₁2 := wfExtendsMap_trans hθext₁1 hθext₁2
          have hlookup_back_final_to_res1 :
              ∀ k b,
                (ctxAfter ctxᵢ res).regime.lookup? k = some b →
                res1.regime'.lookup? k = some b := by
            intro k b hk
            have hk_join : (joinRegimes res2.regime' res3.regime').lookup? k = some b := by
              simpa [ctxAfter, hregime'] using hk
            have hk2 : res2.regime'.lookup? k = some b :=
              joinRegimes_lookup_some_left res2.regime' res3.regime' k b hk_join
            exact monotoneStep_lookup_back hmono2 k b hk2
          have hclean_final_to_res1 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctxᵢ res).regime qt →
                qtypCleanUnder res1.regime' qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                exact qtypCleanUnder.guard k htag (hlookup_back_final_to_res1 k true hk) hnotfun
          have hmemberVars₀_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberVarsRegimeEvidence predSat res1.regime' cf₀.memory σcap ρcap →
                  MemberVarsRegimeEvidence predSat res.regime' cf₀.memory σcap ρcap := by
            intro σcap ρcap h
            exact
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₀.memory)
                hlookup_back_final_to_res1 h
          have hmemberCvcr₀_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberCvcrEvidence predSat res1.regime' cf₀.memory θ₀3 σcap ρcap →
                  MemberCvcrEvidence predSat res.regime' cf₀.memory θ₀3 σcap ρcap := by
            intro σcap ρcap h
            exact
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₀.memory)
                hlookup_back_final_to_res1 h
          have hmemberVars₁_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberVarsRegimeEvidence predSat res1.regime' cf₁.memory σcap ρcap →
                  MemberVarsRegimeEvidence predSat res.regime' cf₁.memory σcap ρcap := by
            intro σcap ρcap h
            exact
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₁.memory)
                hlookup_back_final_to_res1 h
          have hmemberCvcr₁_transport :
              ∀ {σcap : CapturedVarEnv} {ρcap : VarEnv},
                MemberCvcrEvidence predSat res1.regime' cf₁.memory θ₁2 σcap ρcap →
                  MemberCvcrEvidence predSat res.regime' cf₁.memory θ₁2 σcap ρcap := by
            intro σcap ρcap h
            exact
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := res1.regime') (R' := res.regime')
                (μ := cf₁.memory)
                hlookup_back_final_to_res1 h
          have hclean_back_to_res1 :
              ∀ l qt_out,
                res.memEnv'.lookup l = some qt_out →
                qtypCleanUnder res.regime' qt_out →
                ∃ qt_mid,
                  res1.memEnv'.lookup l = some qt_mid ∧
                  qtypCleanUnder res1.regime' qt_mid := by
            intro l qt_out hlookup_out hclean_out
            have hlookup_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt_out := by
              simpa [hmemEnv] using hlookup_out
            have hcontains_join :
                (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
              memEnv_contains_of_lookup_some
                (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt_out hlookup_join
            rcases
                joinMemEnvsStrong_contains_implies_or
                  res2.memEnv' res3.memEnv' l hcontains_join
              with hcontains2 | hcontains3
            · rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with
                ⟨qt2, hlookup2⟩
              have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                cases hclean_out with
                | clean hpoison_out =>
                    have henv2 : res2.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup2] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_left
                          res2.memEnv' res3.memEnv' l qt_out
                          hlookup_join hpoison_out henv2
                      with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                    have hqt2 : qt2 = qt2' := by
                      rw [hlookup2] at hlookup2'
                      injection hlookup2'
                    cases hqt2
                    exact qtypCleanUnder.clean hpoison2
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [hregime'] using hk
                    have htag2 : qtypGuardTag qt2 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_left
                        res2.memEnv' res3.memEnv' l qt_out qt2 k
                        hlookup_join hlookup2 htag
                    have hk2 : res2.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_left
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun2 : qt2.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                      native_decide
                    exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
              exact
                typecheckExpr_clean_lookup_origin_of_pc_true
                  ctx'' e2 fuel' res2 htc2' hpc''
                  l qt2 hlookup2 hclean2
            · rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with
                ⟨qt3, hlookup3⟩
              have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                cases hclean_out with
                | clean hpoison_out =>
                    have henv3 : res3.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup3] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_right
                          res2.memEnv' res3.memEnv' l qt_out
                          hlookup_join hpoison_out henv3
                      with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                    have hqt3 : qt3 = qt3' := by
                      rw [hlookup3] at hlookup3'
                      injection hlookup3'
                    cases hqt3
                    exact qtypCleanUnder.clean hpoison3
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [hregime'] using hk
                    have htag3 : qtypGuardTag qt3 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_right
                        res2.memEnv' res3.memEnv' l qt_out qt3 k
                        hlookup_join hlookup3 htag
                    have hk3 : res3.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_right
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun3 : qt3.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                      native_decide
                    exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
              exact
                typecheckExpr_clean_lookup_origin_of_pc_true
                  ctxForE3 e3 fuel' res3 htc3' hpcForE3
                  l qt3 hlookup3 hclean3
          have hric₀3_src :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₀3
          have hcwr₀3_src :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc', consistentWithRegime] using hcwr₀3
          have hvar_cf₀ : cf₀.varEnv = cfg₀1.varEnv := by
            rcases ht₀_e3 with ⟨fuel₀w, verbose₀w, hpure₀w⟩
            have heq₀w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₀w
            have ht₀w :
                terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld
                  e3 cfg₀1 cf₀ o₀ := by
              exact ⟨fuel₀w, verbose₀w, by simpa [pure] using heq₀w⟩
            rcases ht₀w with ⟨fuel₀', verbose₀', heval₀'⟩
            have hvar_eq :=
              beval_preserves_varEnv .ioFree e3 fuel₀' verbose₀'
                cfg₀1 cf₀ o₀
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₀'⟩
            simpa using hvar_eq.symm
          have hvar_cf₁ : cf₁.varEnv = cfg₁1.varEnv := by
            rcases ht₁_e2 with ⟨fuel₁w, verbose₁w, hpure₁w⟩
            have heq₁w := LeanProofs.evalAtWorld_eq LeanProofs.defaultWorld hpure₁w
            have ht₁w :
                terminatesToW .ioFree LeanProofs.defaultWorld LeanProofs.defaultWorld
                  e2 cfg₁1 cf₁ o₁ := by
              exact ⟨fuel₁w, verbose₁w, by simpa [pure] using heq₁w⟩
            rcases ht₁w with ⟨fuel₁', verbose₁', heval₁'⟩
            have hvar_eq :=
              beval_preserves_varEnv .ioFree e2 fuel₁' verbose₁'
                cfg₁1 cf₁ o₁
                ⟨LeanProofs.defaultWorld, LeanProofs.defaultWorld, heval₁'⟩
            simpa using hvar_eq.symm
          have hresTm :
              QTypRespectsTagMeaning tm res.qualType :=
            typecheckExpr_preserves_QTypRespectsTagMeaning
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwfTm_final : wfTagMeaningCtx tm (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_wfTagMeaningCtx
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀3 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvtyp₀3
          have hvtyp₁_join : valueHasETyp θ₁2 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvtyp₁2
          have hvtyp₀_final : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁2 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀3 := by
            have hric₀_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀3 := by
              unfold runtimeInstantiatesCtx at hric₀3_src ⊢
              constructor
              · intro l a hθlookup
                rcases hric₀3_src.1 l a hθlookup with ⟨hcontains3, hmem⟩
                rcases
                    memEnv_lookup_some_of_contains
                      (ctxAfter ctx'' res3).memEnv l hcontains3
                  with ⟨qt3, hlookup3ctx⟩
                have hlookup3 : res3.memEnv'.lookup l = some qt3 := by
                  simpa [ctxAfter] using hlookup3ctx
                rcases
                    joinMemEnvsStrong_lookup_some_of_right_lookup
                      res2.memEnv' res3.memEnv' l qt3 hlookup3
                  with ⟨qt, hlookup_join⟩
                have hcontains_join :
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv').contains l :=
                  memEnv_contains_of_lookup_some
                    (joinMemEnvsStrong res2.memEnv' res3.memEnv') l qt hlookup_join
                exact ⟨by simpa [ctxAfter] using hcontains_join, hmem⟩
              · intro x qt hlookup
                have hlookup' :
                    (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                  simpa [ctxAfter, ctx'', ctx', pc'] using hlookup
                exact hric₀3_src.2 hlookup'
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁2 := by
            have hric₁_join :
                runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁2 := by
              refine
                ite_join_transport_runtimeInstantiatesCtx
                  (ctx := ctx'') (first := res2) (rest := [res3]) (res := resJoin)
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁2)
                  hjoin ?_ hric₁2
              intro l hcontains
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains with ⟨qt2, hlookup2⟩
              rcases
                  joinMemEnvsStrong_lookup_some_of_left_lookup
                    res2.memEnv' res3.memEnv' l qt2 hlookup2
                with ⟨qt, hlookup_join⟩
              exact memEnv_contains_of_lookup_some _ _ _ hlookup_join
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 := by
            have hcwr₀_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₀.memory cf₀.varEnv θ₀3 := by
              exact
                consistentWithRegime_join_from_right
                  predSat ctx'' res2 res3 resJoin
                  cf₀.memory cf₀.varEnv θ₀3
                  rfl rfl hcwr₀3_src
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁2 := by
            have hcwr₁_join :
                consistentWithRegime predSat
                  (ctxAfter ctx'' resJoin).regime
                  (ctxAfter ctx'' resJoin)
                  cf₁.memory cf₁.varEnv θ₁2 := by
              exact
                consistentWithRegime_join_from_left
                  predSat ctx'' res2 res3 resJoin
                  cf₁.memory cf₁.varEnv θ₁2
                  rfl rfl hcwr₁2
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁2 := by
            constructor
            · intro l qt hlookup hclean
              have hlookup_res : res.memEnv'.lookup l = some qt := by
                simpa [ctxAfter] using hlookup
              have hlookup_join :
                  (joinMemEnvsStrong res2.memEnv' res3.memEnv').lookup l = some qt := by
                simpa [hmemEnv] using hlookup_res
              rcases hclean_back_to_res1 l qt hlookup_res (by simpa [ctxAfter] using hclean) with
                ⟨qt_mid, hlookup_mid, hclean_mid⟩
              have hcontains_mid :
                  res1.memEnv'.contains l :=
                memEnv_contains_of_lookup_some res1.memEnv' l qt_mid hlookup_mid
              have hcontains2 : res2.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved
                  ctx'' e2 fuel' res2
                  (by simpa [ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc2)
                  l
                  (by simpa [ctx'', ctx'] using hcontains_mid)
              have hcontains3 : res3.memEnv'.contains l :=
                typecheckExpr_mem_contains_preserved
                  ctxForE3 e3 fuel' res3
                  (by simpa [ctxForE3, ctx'', ctx', pc', typecheck, Nat.succ_sub_one] using htc3)
                  l
                  (by simpa [ctxForE3, ctx'', ctx'] using hcontains_mid)
              rcases memEnv_lookup_some_of_contains res2.memEnv' l hcontains2 with ⟨qt2, hlookup2⟩
              rcases memEnv_lookup_some_of_contains res3.memEnv' l hcontains3 with ⟨qt3, hlookup3⟩
              have hclean2 : qtypCleanUnder res2.regime' qt2 := by
                cases hclean with
                | clean hpoison_out =>
                    have henv2 : res2.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup2] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_left
                          res2.memEnv' res3.memEnv' l qt
                          hlookup_join hpoison_out henv2
                      with ⟨qt2', hlookup2', _hetyp2, hpoison2⟩
                    have hqt2 : qt2 = qt2' := by
                      rw [hlookup2] at hlookup2'
                      injection hlookup2'
                    cases hqt2
                    exact qtypCleanUnder.clean hpoison2
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [ctxAfter, hregime'] using hk
                    have htag2 : qtypGuardTag qt2 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_left
                        res2.memEnv' res3.memEnv' l qt qt2 k
                        hlookup_join hlookup2 htag
                    have hk2 : res2.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_left
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun2 : qt2.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res2.memEnv' l qt2 hlookup2]
                      native_decide
                    exact qtypCleanUnder.guard k htag2 hk2 hnotfun2
              have hclean3 : qtypCleanUnder res3.regime' qt3 := by
                cases hclean with
                | clean hpoison_out =>
                    have henv3 : res3.memEnv'.lookup l ≠ none := by
                      intro hnone
                      rw [hlookup3] at hnone
                      contradiction
                    rcases
                        joinMemEnvsStrong_lookup_clean_right
                          res2.memEnv' res3.memEnv' l qt
                          hlookup_join hpoison_out henv3
                      with ⟨qt3', hlookup3', _hetyp3, hpoison3⟩
                    have hqt3 : qt3 = qt3' := by
                      rw [hlookup3] at hlookup3'
                      injection hlookup3'
                    cases hqt3
                    exact qtypCleanUnder.clean hpoison3
                | guard k htag hk hnotfun =>
                    have hk_join :
                        (joinRegimes res2.regime' res3.regime').lookup? k = some true := by
                      simpa [ctxAfter, hregime'] using hk
                    have htag3 : qtypGuardTag qt3 = some k :=
                      joinMemEnvsStrong_lookup_guardTag_right
                        res2.memEnv' res3.memEnv' l qt qt3 k
                        hlookup_join hlookup3 htag
                    have hk3 : res3.regime'.lookup? k = some true :=
                      joinRegimes_lookup_some_right
                        res2.regime' res3.regime' k true hk_join
                    have hnotfun3 : qt3.etyp.isFunctionType = false := by
                      rw [memEnv_lookup_etyp_int res3.memEnv' l qt3 hlookup3]
                      native_decide
                    exact qtypCleanUnder.guard k htag3 hk3 hnotfun3
              have hlookup_mid_ctx'' : ctx''.memEnv.lookup l = some qt_mid := by
                simpa [ctx'', ctx'] using hlookup_mid
              have hlookup_mid_ctxForE3 : ctxForE3.memEnv.lookup l = some qt_mid := by
                simpa [ctxForE3, ctx'', ctx'] using hlookup_mid
              have hpres_l₀ :
                  PreservesInheritedCleanLocOneRun cfg₀1.memory cf₀.memory θ₀1 θ₀3 l :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctxForE3) (res := res3)
                  (μ_in := cfg₀1.memory) (μ_out := cf₀.memory)
                  (θ_in := θ₀1) (θ_out := θ₀3)
                  hpres₃ hlookup_mid_ctxForE3 hlookup3 hclean3
              have hpres_l₁ :
                  PreservesInheritedCleanLocOneRun cfg₁1.memory cf₁.memory θ₁1 θ₁2 l :=
                PreservesInheritedFinalCleanLocsOneRun.apply
                  (ctx := ctx'') (res := res2)
                  (μ_in := cfg₁1.memory) (μ_out := cf₁.memory)
                  (θ_in := θ₁1) (θ_out := θ₁2)
                  hpres₂ hlookup_mid_ctx'' hlookup2 hclean2
              have hagree_mid :
                  agreeLocUnder predSat res1.regime'
                    cfg₀1.memory cfg₁1.memory θ₀1 θ₁1 (l, qt_mid) :=
                hagree1.1 l qt_mid (by simpa [ctxAfter] using hlookup_mid) hclean_mid
              cases hagree_mid with
              | both_unrealized _ _ hnone₀ hnone₁ =>
                  have hnone₀' : θ₀3.lookup l = none := by
                    cases hpres_l₀ with
                    | both_unrealized _ hnone_out =>
                        exact hnone_out
                    | preserve_value _ _ hsome_in _ _ _ =>
                        exact False.elim (Option.noConfusion (hnone₀.symm.trans hsome_in))
                  have hnone₁' : θ₁2.lookup l = none := by
                    cases hpres_l₁ with
                    | both_unrealized _ hnone_out =>
                        exact hnone_out
                    | preserve_value _ _ hsome_in _ _ _ =>
                        exact False.elim (Option.noConfusion (hnone₁.symm.trans hsome_in))
                  exact agreeLocUnder.both_unrealized l qt hnone₀' hnone₁'
              | agree_values _ _ a₀m a₁m n₀ n₁ hreal₀m hreal₁m hmem₀m hmem₁m hagreeVmid =>
                  cases hpres_l₀ with
                  | both_unrealized hnone_in _ =>
                      exact False.elim (Option.noConfusion (hreal₀m.symm.trans hnone_in))
                  | preserve_value a₀' n₀' hθ₀in hμ₀in hθ₀out hμ₀out =>
                      cases hpres_l₁ with
                      | both_unrealized hnone_in _ =>
                          exact False.elim (Option.noConfusion (hreal₁m.symm.trans hnone_in))
                      | preserve_value a₁' n₁' hθ₁in hμ₁in hθ₁out hμ₁out =>
                          have ha₀ : a₀' = a₀m := by
                            exact Option.some.inj (hθ₀in.symm.trans hreal₀m)
                          have hn₀ : n₀' = n₀ := by
                            rw [ha₀] at hμ₀in
                            exact Option.some.inj (hμ₀in.symm.trans hmem₀m)
                          have ha₁ : a₁' = a₁m := by
                            exact Option.some.inj (hθ₁in.symm.trans hreal₁m)
                          have hn₁ : n₁' = n₁ := by
                            rw [ha₁] at hμ₁in
                            exact Option.some.inj (hμ₁in.symm.trans hmem₁m)
                          cases ha₀
                          cases hn₀
                          cases ha₁
                          cases hn₁
                          have hnotref_mid : ¬ ∃ ls, qt_mid.etyp = ETyp.ref ls := by
                            intro ⟨ls, hls⟩
                            rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid] at hls
                            simp at hls
                          have hnotfun_mid : qt_mid.etyp.isFunctionType = false := by
                            rw [memEnv_lookup_etyp_int res1.memEnv' l qt_mid hlookup_mid]
                            native_decide
                          have hEq_vals : Value.num n₀ = Value.num n₁ :=
                            agreeValueUnder_nonref_eq_of_clean
                              hclean_mid hnotref_mid hnotfun_mid hagreeVmid
                          have hnotref_final : ¬ ∃ ls, qt.etyp = ETyp.ref ls := by
                            intro ⟨ls, hls⟩
                            rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup] at hls
                            simp at hls
                          have hagreeV_final :
                              agreeValueUnder predSat res.regime'
                                cf₀.memory cf₁.memory θ₀3 θ₁2 qt (Value.num n₀) (Value.num n₁) := by
                            cases hclean with
                            | clean hpoison =>
                                have hnotfun_final : qt.etyp.isFunctionType = false := by
                                  rw [memEnv_lookup_etyp_int (ctxAfter ctxᵢ res).memEnv l qt hlookup]
                                  native_decide
                                exact
                                  agreeValueUnder.clean_eq_nonref_nonarrow
                                    hpoison hnotfun_final hnotref_final hEq_vals
                            | guard k htag hk hnotfun =>
                                exact
                                  agreeValueUnder.withPred_true_eq
                                    k htag hk hnotfun hnotref_final hEq_vals
                          exact
                            agreeLocUnder.agree_values
                              l qt a₀m a₁m n₀ n₁
                              hθ₀out hθ₁out hμ₀out hμ₁out hagreeV_final
            · intro x qt hlookup hclean
              have hclean_mid : qtypCleanUnder res1.regime' qt :=
                hclean_final_to_res1 qt hclean
              have hagree_mid :
                  agreeVarUnder predSat res1.regime'
                    cfg₀1.memory cfg₀1.varEnv cfg₁1.memory cfg₁1.varEnv θ₀1 θ₁1 (x, qt) :=
                hagree1.2 x qt (by simpa [ctxAfter] using hlookup) hclean_mid
              cases hagree_mid with
              | both_none _ _ hnone₀ hnone₁ =>
                  exact
                    agreeVarUnder.both_none x qt
                      (by simpa [hvar_cf₀] using hnone₀)
                      (by simpa [hvar_cf₁] using hnone₁)
              | agree_values _ _ v₀ v₁ hlookup₀ hlookup₁ hagreeVmid =>
                  have hagreeV_ext :
                      agreeValueUnder predSat res1.regime'
                        cf₀.memory cf₁.memory θ₀3 θ₁2 qt v₀ v₁ := by
                    exact
                      agreeValueUnder_clean_extends_transport_mem
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₀1 cfg₀1.memory cf₀.memory)
                        (qtypPredHolds_mem_compat_of_predSatLaws hpredlaws θ₁1 cfg₁1.memory cf₁.memory)
                        hclean_mid hθext₀3.1 hθext₁2.1 hagreeVmid
                  have hagreeV_final :
                      agreeValueUnder predSat res.regime'
                        cf₀.memory cf₁.memory θ₀3 θ₁2 qt v₀ v₁ :=
                    agreeValueUnder_clean_transport_by_cleanBack
                      (predSat := predSat)
                      (R := res1.regime') (R' := res.regime')
                      (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                      (θ₀ := θ₀3) (θ₁ := θ₁2)
                      (qt := qt) (v₀ := v₀) (v₁ := v₁)
                      hclean_final_to_res1
                      hmemberVars₀_transport hmemberCvcr₀_transport
                      hmemberVars₁_transport hmemberCvcr₁_transport
                      hclean hagreeV_ext
                  exact
                    agreeVarUnder.agree_values x qt v₀ v₁
                      (by simpa [hvar_cf₀] using hlookup₀)
                      (by simpa [hvar_cf₁] using hlookup₁)
                      hagreeV_final
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀3 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvalc₀3
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁2 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res2) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁2) (v := o₁)
                hjoin (by simp) hvalc₁2
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀3 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀3 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀3 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁2 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁2 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁2 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hwfcf₀_final : wfConfig cf₀ := by
            exact (wfConfig_preserved .ioFree e3 _ cf₀ o₀ ht₀_e3 hwfcf₀1).1
          have hwfcf₁_final : wfConfig cf₁ := by
            exact (wfConfig_preserved .ioFree e2 _ cf₁ o₁ ht₁_e2 hwfcf₁1).1
          have hres_poison_true : res.qualType.poison = true := by
            calc
              res.qualType.poison =
                  joinPoison ctxᵢ.pc
                    (joinPoison res1.qualType.poison
                      (joinPoison res2.qualType.poison res3.qualType.poison)) := hpoison
              _ = true := by
                have hpc_or : ctxᵢ.pc = true ∨ res1.qualType.poison = true := by
                  have hpc_res1 : joinPoison ctxᵢ.pc res1.qualType.poison = true := by
                    simpa [pc'] using hpc_true
                  cases hctx : ctxᵢ.pc <;> cases hp1 : res1.qualType.poison <;>
                    simp [joinPoison, hctx, hp1] at hpc_res1 ⊢
                cases hpc_or with
                | inl hctx =>
                    simp [joinPoison, hctx]
                | inr hp1 =>
                    simp [joinPoison, hp1]
          exact
            ⟨hresTm, θ₀3, θ₁2, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, hwfcf₀_final, hwfcf₁_final,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final,
              resultAgreesIfClean_of_poison_noPred hres_poison_true hpredNo⟩
      | inr hbranch₁_false =>
          have ht₀_e3 : terminatesTo .ioFree e3 cfg₀1 cf₀ o₀ := hbranch₀_false.2
          have ht₁_e3 : terminatesTo .ioFree e3 cfg₁1 cf₁ o₁ := hbranch₁_false.2
          have hpm_eq : cfg₁1.pureMode = cfg₀1.pureMode := by
            rw [hpm₀1, hpm₁1]
          have hcfg₁1_eq :
              cfg₁1 =
                { memory := cfg₁1.memory
                , varEnv := cfg₁1.varEnv
                , nextAddr := cfg₁1.nextAddr
                , pureMode := cfg₀1.pureMode } := by
            cases cfg₁1
            simp only [Config.mk.injEq, true_and]
            exact hpm_eq
          have ht₁_e3' : terminatesTo .ioFree e3
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode }
              cf₁ o₁ := by
            rw [← hcfg₁1_eq]
            exact ht₁_e3
          have hwfcf₁1' : wfConfig
              { memory := cfg₁1.memory
              , varEnv := cfg₁1.varEnv
              , nextAddr := cfg₁1.nextAddr
              , pureMode := cfg₀1.pureMode } := by
            rw [← hcfg₁1_eq]
            exact hwfcf₁1
          have hIH_e3 :=
            IH fuel' (by exact Nat.lt_succ_of_lt (Nat.lt_succ_self fuel'))
              e3 ctxForE3 hwfTm_ctxForE3 res3 htc3'
          have hstep_e3 :=
            hIH_e3 hpredlaws hwfTm_ctxForE3
              cfg₀1.memory cfg₁1.memory cfg₀1.varEnv cfg₁1.varEnv θ₀1 θ₁1
              cf₀ cf₁ o₀ o₁
              hθ₀1wf hθ₁1wf hwf_ctxForE3 hric₀1_ctxForE3 hric₁1_ctxForE3 htagR_ctxForE3 hRbound_ctxForE3
              hcwr₀1_ctxForE3 hcwr₁1_ctxForE3
              (by simpa [ctxForE3, ctx'', ctx', pc', ctxAfter] using hagree1)
              cfg₀1.nextAddr cfg₁1.nextAddr cfg₀1.pureMode hwfcf₀1 hwfcf₁1'
              ht₀_e3 ht₁_e3'
          rcases hstep_e3 with ⟨_hresTm3, hstep_e3⟩
          rcases hstep_e3 with
            ⟨θ₀3, θ₁3, hθext₀3, hθext₁3, hvtyp₀3, hvtyp₁3, _hwfTm3, _hwf3, hwfcf₀3, hwfcf₁3,
              hric₀3, hric₁3, _htagR3, hcwr₀3, hcwr₁3, hagree3, hvalc₀3, hvalc₁3, hres_agree3⟩
          have hθext₀ : wfExtendsMap θ₀ θ₀3 := wfExtendsMap_trans hθext₀1 hθext₀3
          have hθext₁ : wfExtendsMap θ₁ θ₁3 := wfExtendsMap_trans hθext₁1 hθext₁3
          have hric₀3_ctx'' :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₀3
          have hric₁3_ctx'' :
              runtimeInstantiatesCtx (ctxAfter ctx'' res3) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hric₁3
          have hcwr₀3_ctx'' :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hcwr₀3
          have hcwr₁3_ctx'' :
              consistentWithRegime predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hcwr₁3
          have hagree3_ctx'' :
              agreeOnClean predSat
                (ctxAfter ctx'' res3).regime
                (ctxAfter ctx'' res3)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hagree3
          have hric₀_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₀.memory cf₀.varEnv θ₀3 := by
            have hsrc_mem_to_join :
                ∀ l, res3.memEnv'.contains l → resJoin.memEnv'.contains l :=
              joinTypeResults_mem_contains_of_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp)
            constructor
            · intro l a hθ
              have hloc_src := hric₀3_ctx''.1 l a hθ
              rcases hloc_src with ⟨hcontains_src, hmem_contains⟩
              exact ⟨hsrc_mem_to_join l hcontains_src, hmem_contains⟩
            · intro x qt hlookup
              have hlookup_src :
                  (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              rcases hric₀3_ctx''.2 hlookup_src with ⟨v, hlookup_v, hv_typ⟩
              exact ⟨v, hlookup_v, hv_typ⟩
          have hric₁_join :
              runtimeInstantiatesCtx (ctxAfter ctx'' resJoin) cf₁.memory cf₁.varEnv θ₁3 := by
            have hsrc_mem_to_join :
                ∀ l, res3.memEnv'.contains l → resJoin.memEnv'.contains l :=
              joinTypeResults_mem_contains_of_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp)
            constructor
            · intro l a hθ
              have hloc_src := hric₁3_ctx''.1 l a hθ
              rcases hloc_src with ⟨hcontains_src, hmem_contains⟩
              exact ⟨hsrc_mem_to_join l hcontains_src, hmem_contains⟩
            · intro x qt hlookup
              have hlookup_src :
                  (ctxAfter ctx'' res3).varEnv.lookup x = some qt := by
                simpa [ctxAfter] using hlookup
              rcases hric₁3_ctx''.2 hlookup_src with ⟨v, hlookup_v, hv_typ⟩
              exact ⟨v, hlookup_v, hv_typ⟩
          have hcwr₀_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀3 := by
            exact
              consistentWithRegime_join_from_right
                predSat ctx'' res2 res3 resJoin
                cf₀.memory cf₀.varEnv θ₀3
                rfl rfl hcwr₀3_ctx''
          have hcwr₁_join :
              consistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₁.memory cf₁.varEnv θ₁3 := by
            exact
              consistentWithRegime_join_from_right
                predSat ctx'' res2 res3 resJoin
                cf₁.memory cf₁.varEnv θ₁3
                rfl rfl hcwr₁3_ctx''
          have h_clean_join_to_res3 :
              ∀ qt,
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                qtypCleanUnder (ctxAfter ctx'' res3).regime qt := by
            intro qt hclean
            cases hclean with
            | clean hpoison =>
                exact qtypCleanUnder.clean hpoison
            | guard k htag hk hnotfun =>
                have hk3 :
                    (ctxAfter ctx'' res3).regime.lookup? k = some true :=
                  joinTypeResults_lookup_member_regime_compat
                    (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                    hjoin (by simp) k true hk
                exact qtypCleanUnder.guard k htag hk3 hnotfun
          have h_mem_from_res3_or_unrealized :
              ∀ l qt,
                (ctxAfter ctx'' resJoin).memEnv.lookup l = some qt →
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime qt →
                ((∃ qt3,
                    (ctxAfter ctx'' res3).memEnv.lookup l = some qt3 ∧
                    qtypCleanUnder (ctxAfter ctx'' res3).regime qt3 ∧
                    qt.etyp = qt3.etyp ∧
                    (qt.poison = false → qt3.poison = false)) ∨
                  (θ₀3.lookup l = none ∧ θ₁3.lookup l = none)) := by
            intro l qt hlookup hclean
            by_cases hlookup3_none : (ctxAfter ctx'' res3).memEnv.lookup l = none
            · right
              have hnot_contains3 : ¬ (ctxAfter ctx'' res3).memEnv.contains l := by
                intro hcontains
                have hmem : l ∈ (ctxAfter ctx'' res3).memEnv :=
                  (Std.ExtTreeMap.contains_iff_mem).1 hcontains
                have hlookup_isSome :
                    ((ctxAfter ctx'' res3).memEnv[l]?).isSome = true :=
                  (Std.ExtTreeMap.mem_iff_isSome_getElem?).1 hmem
                have hlookup_get_none :
                    (ctxAfter ctx'' res3).memEnv[l]? = none := by
                  simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup3_none
                simp [hlookup_get_none] at hlookup_isSome
              have hθ₀3_none :
                  θ₀3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res3))
                  (μ := cf₀.memory) (ρ := cf₀.varEnv) (θ := θ₀3)
                  (l := l) hric₀3_ctx'' hnot_contains3
              have hθ₁3_none :
                  θ₁3.lookup l = none :=
                theta_not_contains_if_not_in_memEnv
                  (ctx := (ctxAfter ctx'' res3))
                  (μ := cf₁.memory) (ρ := cf₁.varEnv) (θ := θ₁3)
                  (l := l) hric₁3_ctx'' hnot_contains3
              exact ⟨hθ₀3_none, hθ₁3_none⟩
            · left
              rcases Option.ne_none_iff_exists'.1 hlookup3_none with ⟨qt3, hlookup3⟩
              have hclean3 : qtypCleanUnder (ctxAfter ctx'' res3).regime qt3 :=
                joinTypeResults_lookup_member_clean_compat
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hclean hlookup3
              have hetyp3 : qt.etyp = qt3.etyp :=
                joinTypeResults_lookup_member_etyp_compat
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hlookup3
              have hpoison3 : qt.poison = false → qt3.poison = false :=
                joinTypeResults_lookup_member_poison_imp
                  (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                  hjoin (by simp) l qt qt3 hlookup hlookup3
              exact ⟨qt3, hlookup3, hclean3, hetyp3, hpoison3⟩
          have hlookup_back_join_to_res3 :
              ∀ k b,
                (ctxAfter ctx'' resJoin).regime.lookup? k = some b →
                (ctxAfter ctx'' res3).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                hjoin (by simp) k b hk
          have hagree_join :
              agreeOnClean predSat
                (ctxAfter ctx'' resJoin).regime
                (ctxAfter ctx'' resJoin)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            exact
              ite_join_transport_agreeOnClean_from_member
                (predSat := predSat)
                (ctx := ctx'')
                (first := res2)
                (src := res3)
                (rest := [res3])
                (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (ρ₀ := cf₀.varEnv) (ρ₁ := cf₁.varEnv)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                hjoin (by simp) hagree3_ctx''
                h_clean_join_to_res3
                h_mem_from_res3_or_unrealized
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₀.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res3 h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx'' res3).regime)
                    (R' := (ctxAfter ctx'' resJoin).regime)
                    (μ := cf₁.memory)
                    hlookup_back_join_to_res3 h)
          have hresTm :
              QTypRespectsTagMeaning tm res.qualType :=
            typecheckExpr_preserves_QTypRespectsTagMeaning
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwfTm_final : wfTagMeaningCtx tm (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_wfTagMeaningCtx
              tm ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwfTm htc
          have hwf_final : wfTypeContext (ctxAfter ctxᵢ res) :=
            wfTypeContext_of_wfTypeResult ctxᵢ res
              (typecheckExpr_preserves_wfTypeResult
                ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res hwf htc)
          have htag_final : regimeConsistentWithCtx (ctxAfter ctxᵢ res) :=
            typecheckExpr_preserves_regimeConsistentWithCtx
              ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) res htagR htc
          have hvtyp₀_join : valueHasETyp θ₀3 o₀ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₀3) (v := o₀)
                hjoin (by simp) hvtyp₀3
          have hvtyp₁_join : valueHasETyp θ₁3 o₁ resJoin.qualType.etyp := by
            exact
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (θ := θ₁3) (v := o₁)
                hjoin (by simp) hvtyp₁3
          have hvtyp₀_final : valueHasETyp θ₀3 o₀ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₀_join
          have hvtyp₁_final : valueHasETyp θ₁3 o₁ res.qualType.etyp := by
            simpa [hresJoin_etyp] using hvtyp₁_join
          have hric₀_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₀_join
          have hric₁_final :
              runtimeInstantiatesCtx (ctxAfter ctxᵢ res) cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hric₁_join
          have hcwr₀_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₀_join
          have hcwr₁_final :
              consistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hcwr₁_join
          have hagree_final :
              agreeOnClean predSat
                (ctxAfter ctxᵢ res).regime
                (ctxAfter ctxᵢ res)
                cf₀.memory cf₀.varEnv θ₀3 cf₁.memory cf₁.varEnv θ₁3 := by
            simpa [ctxAfter, ctx'', ctx', pc', resJoin, hmemEnv, htagEnv, hnextLoc, hnextTag, hregime']
              using hagree_join
          have hvalc₀_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₀.memory θ₀3 o₀ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₀.memory) (θ := θ₀3) (v := o₀)
                hjoin (by simp) (by simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hvalc₀3)
          have hvalc₁_join :
              valueConsistentWithRegime predSat
                (ctxAfter ctx'' resJoin).regime
                resJoin.qualType cf₁.memory θ₁3 o₁ := by
            exact
              joinTypeResults_transport_valueConsistentWithRegime_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ := cf₁.memory) (θ := θ₁3) (v := o₁)
                hjoin (by simp) (by simpa [ctxAfter, ctxForE3, ctx'', ctx', pc'] using hvalc₁3)
          have hvalc₀_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₀.memory θ₀3 o₀ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₀.memory θ₀3 o₀ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₀_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₀.memory θ₀3 o₀ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              simpa [ctxAfter, ctx'', ctx', pc', resJoin, hregime'] using hcap_res
          have hvalc₁_final :
              valueConsistentWithRegime predSat
                (ctxAfter ctxᵢ res).regime
                res.qualType cf₁.memory θ₁3 o₁ := by
            refine valueConsistentWithRegime.noTag ?_ ?_
            · simp [qtypGuardTag, hpredNo]
            · have hcap_join :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    resJoin.qualType cf₁.memory θ₁3 o₁ :=
                valueConsistentWithRegime_closureCapturedVarsRegime hvalc₁_join
              have hcap_res :
                  closureCapturedVarsRegime predSat
                    (ctxAfter ctx'' resJoin).regime
                    res.qualType cf₁.memory θ₁3 o₁ :=
                closureCapturedVarsRegime_transport_etyp hresJoin_etyp hcap_join
              have hreg_final :
                  (ctxAfter ctx'' resJoin).regime = (ctxAfter ctxᵢ res).regime := by
                change joinRegimes res2.regime' res3.regime' = res.regime'
                exact hregime'.symm
              exact hreg_final ▸ hcap_res
          have hsrc_res3 : res3 ∈ res2 :: [res3] := by
            simp
          have hres_agree_join :
              resultAgreesIfClean predSat
                (ctxAfter ctx'' resJoin).regime
                cf₀.memory cf₁.memory θ₀3 θ₁3 resJoin.qualType o₀ o₁ := by
            exact
              joinTypeResults_transport_resultAgreesIfClean_from_member
                (predSat := predSat)
                (ctx := ctx'') (first := res2) (src := res3) (rest := [res3]) (res := resJoin)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                (o₀ := o₀) (o₁ := o₁)
                hjoin hsrc_res3 hres_agree3
          have hres_agree_final :
              resultAgreesIfClean predSat
                (ctxAfter ctxᵢ res).regime
                cf₀.memory cf₁.memory θ₀3 θ₁3 res.qualType o₀ o₁ := by
            have hreg_final :
                (ctxAfter ctx'' resJoin).regime = (ctxAfter ctxᵢ res).regime := by
              change joinRegimes res2.regime' res3.regime' = res.regime'
              exact hregime'.symm
            intro hclean
            have hclean_resJoin_reg :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime res.qualType := by
              exact hreg_final.symm ▸ hclean
            have hclean_join :
                qtypCleanUnder (ctxAfter ctx'' resJoin).regime resJoin.qualType := by
              cases hclean with
              | clean hpoison_res =>
                  exact qtypCleanUnder.clean (by simpa [hresJoin_poison] using hpoison_res)
              | guard k htag _hk _hnotfun =>
                  exfalso
                  simp [qtypGuardTag, hpredNo] at htag
            have hagree_join :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀3 θ₁3
                  resJoin.qualType o₀ o₁ :=
              hres_agree_join hclean_join
            have hpoison_imp :
                res.qualType.poison = false → resJoin.qualType.poison = false := by
              intro hpoison_res
              simpa [hresJoin_poison] using hpoison_res
            have hagree_res :
                agreeValueUnder predSat
                  (ctxAfter ctx'' resJoin).regime
                  cf₀.memory cf₁.memory θ₀3 θ₁3
                  res.qualType o₀ o₁ :=
              agreeValueUnder_transport_clean
                (predSat := predSat)
                (R := (ctxAfter ctx'' resJoin).regime)
                (μ₀ := cf₀.memory) (μ₁ := cf₁.memory)
                (θ₀ := θ₀3) (θ₁ := θ₁3)
                (qt := res.qualType) (qt2 := resJoin.qualType)
                (o₀ := o₀) (o₁ := o₁)
                hclean_resJoin_reg hresJoin_etyp.symm hpoison_imp hagree_join
            exact hreg_final ▸ hagree_res
          exact
            ⟨hresTm, θ₀3, θ₁3, hθext₀, hθext₁, hvtyp₀_final, hvtyp₁_final,
              hwfTm_final, hwf_final, hwfcf₀3, hwfcf₁3,
              hric₀_final, hric₁_final, htag_final,
              hcwr₀_final, hcwr₁_final, hagree_final,
              hvalc₀_final, hvalc₁_final, hres_agree_final⟩

-- Main lemma that dispatches to mode-specific lemmas
lemma stepFR_ite
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 e3 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (singleIH : StepFRSingleRunFinalCleanPcTrue_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.ite e1 e2 e3) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.ite e1 e2 e3) res predSat tm := by
  classical
  -- Parse typecheck result
  have htc' : typecheckIf .ioFree ctxᵢ e1 e2 e3 (Nat.succ fuel') = .ok res := by
    simpa [typecheck, typecheckExpr] using htc
  have hstruct := typecheckIf_structure ctxᵢ e1 e2 e3 (Nat.succ fuel') res htc'
  -- Case split on typecheck structure (4 modes)
  cases hstruct with
  | inl h_mode1 =>
    -- Mode 1: R(k) = some true (then-branch effective)
    obtain ⟨k, deps, hmatch, hregime_true, res1, htc1, hbool, res2, htc2,
            hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp⟩ := h_mode1
    exact stepFR_ite_mode1 ctxᵢ predSat tm e1 e2 e3 fuel' res IH htc k deps hmatch hregime_true
      res1 res2 htc1 hbool htc2 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison hetyp
  | inr h_rest =>
    cases h_rest with
    | inl h_mode2 =>
      -- Mode 2: R(k) = some false (else-branch effective)
      obtain ⟨k, deps, hmatch, hregime_false, res1, htc1, hbool, res3, htc3,
              hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, hetyp⟩ := h_mode2
      exact stepFR_ite_mode2 ctxᵢ predSat tm e1 e2 e3 fuel' res IH htc k deps hmatch hregime_false
        res1 res3 htc1 hbool htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison hetyp
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_mode3 =>
        -- Mode 3: R(k) = none (conservative join)
        obtain ⟨k, deps, hmatch, hregime_none, res1, htc1, hbool, res2, htc2, res3, htc3,
                hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, _hetyp, _hpred⟩ := h_mode3
        exact stepFR_ite_mode3 ctxᵢ predSat tm e1 e2 e3 fuel' res IH k deps hmatch hregime_none
          res1 res2 res3 htc1 hbool htc2 htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison
      | inr h_mode4 =>
        -- Mode 4: matchGuard fails (standard join)
        obtain ⟨⟨err, hmatch_fail⟩, res1, htc1, hbool, res2, htc2, res3, htc3,
                hmemEnv, htagEnv, hnextLoc, hnextTag, hregime', hpoison, _hetyp, _hpred⟩ := h_mode4
        exact stepFR_ite_mode4 ctxᵢ predSat tm e1 e2 e3 fuel' res IH singleIH htc err hmatch_fail
          res1 res2 res3 htc1 hbool htc2 htc3 hmemEnv htagEnv hnextLoc hnextTag hregime' hpoison
