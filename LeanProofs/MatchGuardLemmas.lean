/-
  MatchGuardLemmas.lean - Structure lemmas for `matchGuard`.

  When `matchGuard` selects a guard for a condition, the condition has a pure
  view, the selected guard closure has an owner in the context (a variable, or
  the cells of a clean reference), it is in scope, and the set it returns
  contains the locations of its in-scope variables and the set the extraction
  computes for the closure. Used by `StepFRIte` and `FootprintTyping`.
-/
import LeanProofs.StepFR

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
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (S : VarTypeEnv) (arg : PExpr)
    (qt : QTyp) (fuel : Nat) :
    TypecheckM (Option (Tag × Deps)) := do
  matchGuard_checkNoPredOnArrow qt
  match qt.pred with
  | Predicate.noPred => return none
  | Predicate.guardOnly _tag => return none
  | Predicate.guardClosure tag arg_name pred_body var_env =>
      -- Use `... = true` conditionals to stay syntactically aligned with the unfolded
      -- `matchGuard` implementation (which often normalizes Bool-ifs this way).
      if PExpr.usesArg arg_name pred_body = true then
        if (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, arg)) fuel && guardScopeAgrees arg_name pred_body var_env S) = true then do
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
    match matchGuard_checkPredicate conditionPExpr sCaptured ctx.varEnv arg qt fuel with
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
              if (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                  (some (arg_name, arg)) fuel &&
                    guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true then
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
    (conditionPExpr : PExpr) (sCaptured : CapturedVarEnv) (S : VarTypeEnv) (arg : PExpr)
    (qt : QTyp) (fuel : Nat)
    (k : Tag) (deps : Deps)
    (h :
      matchGuard_checkPredicate conditionPExpr sCaptured S arg qt fuel = .ok (some (k, deps))) :
    ∃ arg_name pred_body var_env,
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
      (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
        (some (arg_name, arg)) fuel && guardScopeAgrees arg_name pred_body var_env S) = true ∧
      extractDepsFromPred (Predicate.guardClosure k arg_name pred_body var_env) fuel = .ok deps := by
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
            cases hA : PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                (some (arg_name, arg)) fuel with
            | false => simp [hA] at h
            | true =>
              cases hB : guardScopeAgrees arg_name pred_body var_env S with
              | false => simp [hA, hB] at h
              | true =>
                simp [hA, hB] at h
                cases hdeps : extractDepsFromPred (Predicate.guardClosure k' arg_name pred_body var_env) fuel with
                | error err =>
                    have : False := by
                      simp [hdeps] at h
                      cases h
                    exact False.elim this
                | ok d =>
                    simp [hdeps] at h
                    cases h
                    exact ⟨arg_name, pred_body, var_env, rfl, by simp [hA, hB], hdeps⟩
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
        match matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) ctx.varEnv arg qt fuel with
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
      bind, Except.bind] using! hmatch
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
          simpa [href0, bind, Except.bind] using! hmatch2
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
            matchGuard_checkPredicate conditionPExpr (VarTypeEnv.toCaptured ctx.varEnv) ctx.varEnv
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
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env ∧
          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, PExpr.var x)) fuel &&
              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
              extractDepsFromPred (Predicate.guardClosure kd.1 arg_name pred_body var_env) fuel = .ok kd.2) →
      ∀ kd, kd ∈ List.foldl
        (fun acc entry =>
          let name := entry.1
          let qt := entry.2
          let arg := PExpr.var name
          match matchGuard_checkPredicate conditionPExpr sCaptured ctx.varEnv arg qt fuel with
          | .ok (some kd) => kd :: acc
          | .ok none => acc
          | .error _ => acc) acc entries →
        ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env ∧
          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, PExpr.var x)) fuel &&
              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
              extractDepsFromPred (Predicate.guardClosure kd.1 arg_name pred_body var_env) fuel = .ok kd.2 := by
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
        (match matchGuard_checkPredicate conditionPExpr sCaptured ctx.varEnv (PExpr.var name) qt fuel with
        | .ok (some kd) => kd :: acc
        | .ok none => acc
        | .error _ => acc)
      have hacc1 :
          ∀ kd, kd ∈ acc1 →
            ∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
              ctx.varEnv.lookup x = some qt ∧
              qt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env ∧
              (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                (some (arg_name, PExpr.var x)) fuel &&
                  guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
                  extractDepsFromPred (Predicate.guardClosure kd.1 arg_name pred_body var_env) fuel = .ok kd.2 := by
        intro kd' hmem'
        dsimp [acc1] at hmem'
        cases hcp : matchGuard_checkPredicate conditionPExpr sCaptured ctx.varEnv (PExpr.var name) qt fuel with
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
                      matchGuard_checkPredicate conditionPExpr sCaptured ctx.varEnv (PExpr.var name) qt fuel = .ok (some kd') := by
                    simp [hcp]
                  rcases matchGuard_checkPredicate_ok_some_guardClosure
                    conditionPExpr sCaptured ctx.varEnv (PExpr.var name) qt fuel kd'.1 kd'.2 hcp'
                    with ⟨arg_name, pred_body, var_env, hpred, heqv, hdeps⟩
                  exact ⟨name, qt, arg_name, pred_body, var_env, hlookup_name, hpred, heqv, hdeps⟩
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
      qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
      (PExpr.equalWithEnvs pred_body var_env conditionPExpr
        (VarTypeEnv.toCaptured ctx.varEnv) (some (arg_name, PExpr.var x)) fuel &&
          guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
          extractDepsFromPred (Predicate.guardClosure k arg_name pred_body var_env) fuel = .ok deps := by
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

/-- One step of the fold `matchGuard` uses to collect the dependency set of a
    reference: the location and the set of its cell's predicate. -/
private def matchGuard_refDepsFoldF (ctx : TypeContext) (fuel : Nat)
    (dacc : Deps) (l : Loc) : TypecheckM Deps := do
  match ctx.memEnv.lookup l with
  | some memQt =>
      matchGuard_checkNoPredOnArrow memQt
      let deps ← extractDepsFromPred memQt.pred fuel
      pure (LocSet.union dacc (LocSet.union (LocSet.singleton l) deps))
  | none => throw s!"Location {l} not found in memory environment during matchGuard"

private lemma mem_LocSet_union {l : Loc} {s t : LocSet} :
    l ∈ LocSet.union s t ↔ l ∈ s ∨ l ∈ t := by
  simp [LocSet.union, ExtTreeSet.mem_union_iff]

private lemma list_foldlM_matchGuard_refDeps (ctx : TypeContext) (fuel : Nat) :
    ∀ (xs : List Loc) (acc r : Deps),
      List.foldlM (matchGuard_refDepsFoldF ctx fuel) acc xs = .ok r →
      (∀ y, y ∈ acc → y ∈ r) ∧
      (∀ l, l ∈ xs → ∀ memQt, ctx.memEnv.lookup l = some memQt →
        ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ r) := by
  intro xs
  induction xs with
  | nil =>
      intro acc r h
      simp [List.foldlM_nil, pure, Except.pure] at h
      subst h
      exact ⟨fun y hy => hy, fun l hl => by cases hl⟩
  | cons x xs ih =>
      intro acc r h
      simp only [List.foldlM_cons] at h
      cases hfx : matchGuard_refDepsFoldF ctx fuel acc x with
      | error err => simp [hfx, bind, Except.bind] at h
      | ok acc' =>
          simp [hfx, bind, Except.bind] at h
          obtain ⟨hsub, htail⟩ := ih acc' r h
          cases hlookup : ctx.memEnv.lookup x with
          | none =>
              simp [matchGuard_refDepsFoldF, hlookup] at hfx
          | some memQt0 =>
              cases hchk : matchGuard_checkNoPredOnArrow memQt0 with
              | error err =>
                  simp [matchGuard_refDepsFoldF, hlookup, hchk, bind, Except.bind] at hfx
              | ok _ =>
                  cases hd0 : extractDepsFromPred memQt0.pred fuel with
                  | error err =>
                      simp [matchGuard_refDepsFoldF, hlookup, hchk, hd0, bind, Except.bind] at hfx
                  | ok d0 =>
                      simp [matchGuard_refDepsFoldF, hlookup, hchk, hd0, bind, Except.bind, pure,
                        Except.pure] at hfx
                      subst hfx
                      refine ⟨fun y hy => hsub y (mem_LocSet_union.2 (Or.inl hy)), ?_⟩
                      intro l hl memQt hmem
                      rcases List.mem_cons.mp hl with rfl | hl'
                      · rw [hlookup] at hmem
                        cases hmem
                        exact ⟨d0, hd0, fun y hy =>
                          hsub y (mem_LocSet_union.2 (Or.inr (mem_LocSet_union.2 (Or.inr hy))))⟩
                      · exact htail l hl' memQt hmem

/-- The dependency set `matchGuard` collects for a reference contains the set of
    the predicate of each cell the reference may target. -/
private lemma matchGuard_refDeps_foldM_mem (ctx : TypeContext) (fuel : Nat) (ls : LocSet)
    (depsMerged : Deps)
    (hfold : LocSet.foldM ls (init := LocSet.empty) (matchGuard_refDepsFoldF ctx fuel) =
      .ok depsMerged) :
    ∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
      ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ depsMerged := by
  unfold LocSet.foldM at hfold
  rw [ExtTreeSet.foldlM_eq_foldlM_toList] at hfold
  intro l hl
  exact (list_foldlM_matchGuard_refDeps ctx fuel ls.toList _ _ hfold).2 l (by simpa using hl)

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
          qt.poison = false ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) ∧
          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
              (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
                ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ kd.2))
    (hstep : matchGuard_refStep conditionPExpr sCaptured ctx acc (name, qt) fuel = .ok acc1) :
    ∀ kd, kd ∈ acc1 →
      ∃ (x : Name) (qt : QTyp) (ls : LocSet)
        (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
        ctx.varEnv.lookup x = some qt ∧
        qt.etyp = ETyp.ref ls ∧
        qt.poison = false ∧
        ls.isEmpty = false ∧
        (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
            memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) ∧
        (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
          (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
            guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
            (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
              ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ kd.2) := by
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
                          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                            (some (arg_name, PExpr.deref (PExpr.var name))) fuel &&
                              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true
                        · have hacc1eq : acc1 = (tag, depsMerged) :: acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            have hAB := (Bool.and_eq_true _ _).mp heqvT
                            simp [husesT, hAB.1, hAB.2] at hstep'
                            cases hstep'
                            rfl
                          subst hacc1eq
                          rcases (List.mem_cons.mp hmem) with hhead | htail
                          · subst hhead
                            refine ⟨name, qt, ls, arg_name, pred_body, var_env, hlookup_name, hEt, hpoisonF, hlsEmptyF,
                              ?_, heqvT,
                              matchGuard_refDeps_foldM_mem ctx fuel ls depsMerged
                                (by simpa [matchGuard_refDepsFoldF] using! hdeps)⟩
                            have hmerged' :
                                LocSet.foldM ls (init := (none : Option Predicate))
                                  (matchGuard_refPredFoldF ctx) = .ok merged? := by
                              simpa [matchGuard_refPredFoldF] using! hmerged
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
                              (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                (some (arg_name, PExpr.deref (PExpr.var name))) fuel &&
                                  guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = false := by
                            cases heqv :
                                (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                  (some (arg_name, PExpr.deref (PExpr.var name))) fuel &&
                                    guardScopeAgrees arg_name pred_body var_env ctx.varEnv) with
                            | false =>
                                rfl
                            | true =>
                                simp [heqv] at heqvT
                          have hcases :
                              PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                  (some (arg_name, PExpr.deref (PExpr.var name))) fuel = false ∨
                                guardScopeAgrees arg_name pred_body var_env ctx.varEnv = false := by
                            cases hA : PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                                (some (arg_name, PExpr.deref (PExpr.var name))) fuel with
                            | false => exact Or.inl rfl
                            | true =>
                                right
                                simpa [hA] using heqvF
                          have hacc1eq : acc1 = acc := by
                            have hstep' := hstep0
                            unfold matchGuard_refStep at hstep'
                            simp [hEt, hpoisonF, hlsEmptyF] at hstep'
                            erw [hmerged] at hstep'
                            erw [hdeps] at hstep'
                            simp [bind, Except.bind] at hstep'
                            erw [hmg] at hstep'
                            rcases hcases with hAf | hBf
                            · simp [husesT, hAf] at hstep'
                              cases hstep'
                              rfl
                            · simp [husesT, hBf] at hstep'
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
          qt.poison = false ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) ∧
          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
              (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
                ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ kd.2)) →
      ∀ acc',
        List.foldlM (fun acc entry => matchGuard_refStep conditionPExpr sCaptured ctx acc entry fuel) acc entries =
          .ok acc' →
      ∀ kd, kd ∈ acc' →
        ∃ (x : Name) (qt : QTyp) (ls : LocSet)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          qt.poison = false ∧
          ls.isEmpty = false ∧
          (∀ l, l ∈ ls →
            ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
              memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) ∧
          (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
            (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
              guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
              (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
                ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ kd.2) := by
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
                  qt.poison = false ∧
                  ls.isEmpty = false ∧
                  (∀ l, l ∈ ls →
                    ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                      memQt.pred = Predicate.guardClosure kd.1 arg_name pred_body var_env) ∧
                  (PExpr.equalWithEnvs pred_body var_env conditionPExpr sCaptured
                    (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
                      guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
                      (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
                        ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ kd.2) := by
            exact
              matchGuard_refStep_preserves_invariant
                ctx conditionPExpr sCaptured name qt acc acc1 fuel hlookup_name hacc hstep
          have hentries_tail :
              ∀ name qt, (name, qt) ∈ entries → ctx.varEnv.lookup name = some qt := by
            intro name' qt' hmem'
            exact hentries name' qt' (List.mem_cons_of_mem _ hmem')
          exact ih hentries_tail acc1 hacc1 acc' hfold kd hmem

/-- Ref-side extraction from refMatches membership, with the owner clean. -/
private lemma ref_match_from_refMatches_clean
    (ctx : TypeContext) (conditionPExpr : PExpr) (k : Tag) (deps : Deps)
    (refMatches : List (Tag × Deps))
    (fuel : Nat)
    (href : matchGuard_refMatches conditionPExpr ctx fuel = .ok refMatches)
    (hmem : (k, deps) ∈ refMatches) :
    ∃ (x : Name) (qt : QTyp) (ls : LocSet)
      (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ctx.varEnv.lookup x = some qt ∧
      qt.etyp = ETyp.ref ls ∧
      qt.poison = false ∧
      ls.isEmpty = false ∧
      (∀ l, l ∈ ls →
        ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ∧
      (PExpr.equalWithEnvs pred_body var_env conditionPExpr
        (VarTypeEnv.toCaptured ctx.varEnv)
        (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
          guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true ∧
          (∀ l, l ∈ ls → ∀ memQt, ctx.memEnv.lookup l = some memQt →
            ∃ d, extractDepsFromPred memQt.pred fuel = .ok d ∧ ∀ y, y ∈ d → y ∈ deps) := by
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
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ∧
      (PExpr.equalWithEnvs pred_body var_env conditionPExpr
        (VarTypeEnv.toCaptured ctx.varEnv)
        (some (arg_name, PExpr.deref (PExpr.var x))) fuel &&
          guardScopeAgrees arg_name pred_body var_env ctx.varEnv) = true := by
  rcases ref_match_from_refMatches_clean ctx conditionPExpr k deps refMatches fuel href hmem with
    ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, _hpois, hne, hls, hboth, _hdeps⟩
  exact ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hne, hls, hboth⟩

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

/-- A successful `matchGuard` exposes the matched owner.  The condition has a
    pure-expression view, and a variable or a clean reference of the context carries the
    guard closure for `k` whose body, with the owner substituted for the closure argument,
    is equal to the condition in the sense of `PExpr.equalWithEnvs`. -/
theorem matchGuard_ok_matched_owner
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ conditionPExpr, cond.toPExpr? = some conditionPExpr ∧
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr)
            (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            PExpr.equalWithEnvs pred_body var_env conditionPExpr
              (VarTypeEnv.toCaptured ctx.varEnv) (some (arg_name, PExpr.var x)) fuel = true)
        ∨
        (∃ (x : Name) (qt : QTyp) (ls : LocSet)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            ls.isEmpty = false ∧
            (∀ l, l ∈ ls →
              ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ∧
            PExpr.equalWithEnvs pred_body var_env conditionPExpr
              (VarTypeEnv.toCaptured ctx.varEnv)
              (some (arg_name, PExpr.deref (PExpr.var x))) fuel = true) ) := by
  rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
  have hcond : cond.toPExpr = .ok conditionPExpr := by
    unfold Expr.toPExpr
    rw [hcond_some]
    simp [pure, Except.pure]
  refine ⟨conditionPExpr, hcond_some, ?_⟩
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  rcases singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall with hvar | hrefMem
  · left
    rcases var_match_from_varMatches ctx conditionPExpr k deps fuel hvar with
      ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, hboth, _hdeps⟩
    exact ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, ((Bool.and_eq_true _ _).mp hboth).1⟩
  · right
    rcases ref_match_from_refMatches ctx conditionPExpr k deps refMatches fuel href hrefMem with
      ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hne, hls, hboth⟩
    exact ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hne, hls,
      ((Bool.and_eq_true _ _).mp hboth).1⟩

/-- A guard closure with argument `argName`, body `body` and captured environment
    `capEnv` is in scope in the environment `S`: the body does not dereference its
    argument (`PExpr.derefsArg`), and every free variable of the body other than its
    argument (`PExpr.freeVars`; a name bound by a `let` of the body is not free) has
    one qualified type in the captured environment and in `S`, clean, a reference
    to a single location. -/
structure GuardInScope (S : VarTypeEnv) (argName : Name) (body : PExpr)
    (capEnv : CapturedVarEnv) : Prop where
  noDerefArg : PExpr.derefsArg [argName] body = false
  reads : ∀ x, x ∈ PExpr.freeVars [argName] body →
    ∃ (qt : QTyp) (ls : LocSet) (l : Loc),
      (VarTypeEnv.ofCaptured capEnv).lookup x = some qt ∧
      S.lookup x = some qt ∧
      qt.poison = false ∧
      qt.etyp = ETyp.ref ls ∧
      ls.toList = [l]

/-- `guardScopeAgrees` decides `GuardInScope`, in the direction `matchGuard` uses. -/
theorem GuardInScope.of_guardScopeAgrees {S : VarTypeEnv} {argName : Name} {body : PExpr}
    {capEnv : CapturedVarEnv}
    (h : guardScopeAgrees argName body capEnv S = true) :
    GuardInScope S argName body capEnv := by
  unfold guardScopeAgrees at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hnd, hall⟩ := h
  refine ⟨by simpa using hnd, ?_⟩
  intro x hx
  have hx' := hall x hx
  split at hx'
  · rename_i q1 q2 h1 h2
    simp only [Bool.and_eq_true] at hx'
    obtain ⟨⟨hbeq, hpois⟩, het⟩ := hx'
    have hq : q1 = q2 := eq_of_beq (show (q1 == q2) = true from hbeq)
    subst hq
    split at het
    · rename_i ls hE
      split at het
      · rename_i l hL
        exact ⟨q1, ls, l, h1, h2, by simpa using hpois, hE, hL⟩
      · simp at het
    · simp at het
  · simp at hx'

/-- `matchGuard_ok_matched_owner`, with the matched guard closure in scope in the
    context's environment (`GuardInScope`), and in the reference case a clean owner. -/
theorem matchGuard_ok_matched_owner_inScope
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps)
    {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ conditionPExpr, cond.toPExpr? = some conditionPExpr ∧
      ( (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr)
            (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
            PExpr.equalWithEnvs pred_body var_env conditionPExpr
              (VarTypeEnv.toCaptured ctx.varEnv) (some (arg_name, PExpr.var x)) fuel = true ∧
            GuardInScope ctx.varEnv arg_name pred_body var_env)
        ∨
        (∃ (x : Name) (qt : QTyp) (ls : LocSet)
            (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            qt.poison = false ∧
            ls.isEmpty = false ∧
            (∀ l, l ∈ ls →
              ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ∧
            PExpr.equalWithEnvs pred_body var_env conditionPExpr
              (VarTypeEnv.toCaptured ctx.varEnv)
              (some (arg_name, PExpr.deref (PExpr.var x))) fuel = true ∧
            GuardInScope ctx.varEnv arg_name pred_body var_env) ) := by
  rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
  have hcond : cond.toPExpr = .ok conditionPExpr := by
    unfold Expr.toPExpr
    rw [hcond_some]
    simp [pure, Except.pure]
  refine ⟨conditionPExpr, hcond_some, ?_⟩
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  rcases singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall with hvar | hrefMem
  · left
    rcases var_match_from_varMatches ctx conditionPExpr k deps fuel hvar with
      ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, hboth, _hdeps⟩
    have hAB := (Bool.and_eq_true _ _).mp hboth
    exact ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, hAB.1,
      GuardInScope.of_guardScopeAgrees hAB.2⟩
  · right
    rcases ref_match_from_refMatches_clean ctx conditionPExpr k deps refMatches fuel href
        hrefMem with
      ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hpois, hne, hls, hboth, _hdeps⟩
    have hAB := (Bool.and_eq_true _ _).mp hboth
    exact ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hpois, hne, hls, hAB.1,
      GuardInScope.of_guardScopeAgrees hAB.2⟩

/-- Each free variable of reference type of a pure expression contributes its
    locations to the set `extractDepsFromPExpr` computes. -/
private lemma extractDepsFromPExpr_freeVar_ref :
    ∀ (fuel : Nat) (pe : PExpr) (bound : List Name) (env : VarTypeEnv) (deps : Deps),
      extractDepsFromPred.extractDepsFromPExpr pe bound env fuel = .ok deps →
      ∀ x, x ∈ PExpr.freeVars bound pe →
      ∀ (qt : QTyp) (ls : LocSet), env.lookup x = some qt → qt.etyp = ETyp.ref ls →
      ∀ l, l ∈ ls → l ∈ deps := by
  intro fuel
  induction fuel with
  | zero =>
      intro pe bound env deps h
      simp [extractDepsFromPred.extractDepsFromPExpr, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
      intro pe bound env deps h x hx qt ls hlook hety l hl
      cases pe with
      | unit => simp [PExpr.freeVars] at hx
      | num _ => simp [PExpr.freeVars] at hx
      | bool _ => simp [PExpr.freeVars] at hx
      | str _ => simp [PExpr.freeVars] at hx
      | var y =>
          by_cases hb : y ∈ bound
          · simp [PExpr.freeVars, hb] at hx
          · have hxy : x = y := by simpa [PExpr.freeVars, hb] using hx
            subst hxy
            have hget : env[x]? = some qt := by
              simpa [VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?] using hlook
            simp [extractDepsFromPred.extractDepsFromPExpr, hb, hget, hety, pure, Except.pure] at h
            subst h
            exact hl
      | deref p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact ih p bound env deps h x (by simpa [PExpr.freeVars] using hx) qt ls hlook hety l hl
      | unaryop o p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact ih p bound env deps h x (by simpa [PExpr.freeVars] using hx) qt ls hlook hety l hl
      | op p o q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
              subst h
              simp only [PExpr.freeVars, List.mem_append] at hx
              rcases hx with hx | hx
              · exact mem_LocSet_union.2 (Or.inl (ih p bound env d1 h1 x hx qt ls hlook hety l hl))
              · exact mem_LocSet_union.2 (Or.inr (ih q bound env d2 h2 x hx qt ls hlook hety l hl))
      | app p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
              subst h
              simp only [PExpr.freeVars, List.mem_append] at hx
              rcases hx with hx | hx
              · exact mem_LocSet_union.2 (Or.inl (ih p bound env d1 h1 x hx qt ls hlook hety l hl))
              · exact mem_LocSet_union.2 (Or.inr (ih q bound env d2 h2 x hx qt ls hlook hety l hl))
      | vlet y p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q (y :: bound) env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
              subst h
              simp only [PExpr.freeVars, List.mem_append] at hx
              rcases hx with hx | hx
              · exact mem_LocSet_union.2 (Or.inl (ih p bound env d1 h1 x hx qt ls hlook hety l hl))
              · exact mem_LocSet_union.2
                  (Or.inr (ih q (y :: bound) env d2 h2 x hx qt ls hlook hety l hl))
      | ite p q r =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              cases h3 : extractDepsFromPred.extractDepsFromPExpr r bound env f with
              | error e => simp [h1, h2, h3, bind, Except.bind] at h
              | ok d3 =>
                simp [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
                subst h
                simp only [PExpr.freeVars, List.mem_append] at hx
                rcases hx with (hx | hx) | hx
                · exact mem_LocSet_union.2 (Or.inl (mem_LocSet_union.2
                    (Or.inl (ih p bound env d1 h1 x hx qt ls hlook hety l hl))))
                · exact mem_LocSet_union.2 (Or.inl (mem_LocSet_union.2
                    (Or.inr (ih q bound env d2 h2 x hx qt ls hlook hety l hl))))
                · exact mem_LocSet_union.2 (Or.inr (ih r bound env d3 h3 x hx qt ls hlook hety l hl))

/-- Each set `extractDepsFromPred` computes for a guard closure contains the
    locations of every variable of reference type the closure reads. -/
private lemma extractDepsFromPred_freeVar_ref {k : Tag} {argName : Name} {body : PExpr}
    {capEnv : CapturedVarEnv} {fuel : Nat} {deps : Deps}
    (h : extractDepsFromPred (Predicate.guardClosure k argName body capEnv) fuel = .ok deps) :
    ∀ y, y ∈ PExpr.freeVars [argName] body →
      ∀ (qt : QTyp) (ls : LocSet), (VarTypeEnv.ofCaptured capEnv).lookup y = some qt →
      qt.etyp = ETyp.ref ls → ∀ l, l ∈ ls → l ∈ deps := by
  simp only [extractDepsFromPred] at h
  exact extractDepsFromPExpr_freeVar_ref fuel body [argName] _ deps h

/-- The guard closure a successful `matchGuard` selects, with its owner (a variable,
    or the cells of a clean reference) and in scope in the context's environment:
    every location of a variable the closure reads is in the set `matchGuard`
    returns. -/
theorem matchGuard_ok_inScope_locs_mem
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps) {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ( (∃ (x : Name) (qt : QTyp),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
        ∨
        (∃ (x : Name) (qt : QTyp) (ls : LocSet),
            ctx.varEnv.lookup x = some qt ∧
            qt.etyp = ETyp.ref ls ∧
            qt.poison = false ∧
            ls.isEmpty = false ∧
            (∀ l, l ∈ ls →
              ∃ memQt, ctx.memEnv.lookup l = some memQt ∧
                memQt.pred = Predicate.guardClosure k arg_name pred_body var_env)) ) ∧
      GuardInScope ctx.varEnv arg_name pred_body var_env ∧
      ∀ y, y ∈ PExpr.freeVars [arg_name] pred_body →
        ∀ (qt : QTyp) (ls : LocSet), ctx.varEnv.lookup y = some qt → qt.etyp = ETyp.ref ls →
        ∀ l, l ∈ ls → l ∈ deps := by
  rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
  have hcond : cond.toPExpr = .ok conditionPExpr := by
    unfold Expr.toPExpr
    rw [hcond_some]
    simp [pure, Except.pure]
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  have hlocs : ∀ {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv} {d : Deps},
      GuardInScope ctx.varEnv arg_name pred_body var_env →
      extractDepsFromPred (Predicate.guardClosure k arg_name pred_body var_env) fuel = .ok d →
      (∀ y, y ∈ d → y ∈ deps) →
      ∀ y, y ∈ PExpr.freeVars [arg_name] pred_body →
        ∀ (qt : QTyp) (ls : LocSet), ctx.varEnv.lookup y = some qt → qt.etyp = ETyp.ref ls →
        ∀ l, l ∈ ls → l ∈ deps := by
    intro arg_name pred_body var_env d hscope hd hsub y hy qt ls hS hety l hl
    obtain ⟨qt', _, _, hcap, hS', _, _, _⟩ := hscope.reads y hy
    have hq : qt' = qt := Option.some.inj (hS'.symm.trans hS)
    subst hq
    exact hsub l (extractDepsFromPred_freeVar_ref hd y hy qt' ls hcap hety l hl)
  rcases singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall with hvar | hrefMem
  · rcases var_match_from_varMatches ctx conditionPExpr k deps fuel hvar with
      ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, hboth, hdeps⟩
    have hscope := GuardInScope.of_guardScopeAgrees ((Bool.and_eq_true _ _).mp hboth).2
    exact ⟨arg_name, pred_body, var_env, Or.inl ⟨x, qt, hlook, hpred⟩, hscope,
      hlocs hscope hdeps (fun y hy => hy)⟩
  · rcases ref_match_from_refMatches_clean ctx conditionPExpr k deps refMatches fuel href
        hrefMem with
      ⟨x, qt, ls, arg_name, pred_body, var_env, hlook, hEt, hpois, hne, hls, hboth, hdeps⟩
    have hscope := GuardInScope.of_guardScopeAgrees ((Bool.and_eq_true _ _).mp hboth).2
    obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∈ ls :=
      Classical.byContradiction fun hnone =>
        (ExtTreeSet.isEmpty_eq_false_iff.mp hne)
          (ExtTreeSet.eq_empty_iff_forall_not_mem.mpr fun a ha => hnone ⟨a, ha⟩)
    obtain ⟨memQt, hmem, hmpred⟩ := hls l0 hl0
    obtain ⟨d, hd, hsub⟩ := hdeps l0 hl0 memQt hmem
    rw [hmpred] at hd
    exact ⟨arg_name, pred_body, var_env, Or.inr ⟨x, qt, ls, hlook, hEt, hpois, hne, hls⟩, hscope,
      hlocs hscope hd hsub⟩

/-- The set a successful `matchGuard` returns contains the set the dependency
    extraction computes for the selected guard closure, whose owner is a variable
    or a cell of the context. -/
theorem matchGuard_ok_extract_sub
    (ctx : TypeContext) (cond : Expr) (k : Tag) (deps : Deps) {fuel : Nat}
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
      ( (∃ (x : Name) (qt : QTyp),
            ctx.varEnv.lookup x = some qt ∧
            qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
        ∨
        (∃ (l0 : Loc) (memQt : QTyp),
            ctx.memEnv.lookup l0 = some memQt ∧
            memQt.pred = Predicate.guardClosure k arg_name pred_body var_env) ) ∧
      ∃ d, extractDepsFromPred (Predicate.guardClosure k arg_name pred_body var_env) fuel = .ok d ∧
        ∀ y, y ∈ d → y ∈ deps := by
  rcases matchGuard_ok_toPExpr?_some ctx cond k deps hmatch with ⟨conditionPExpr, hcond_some⟩
  have hcond : cond.toPExpr = .ok conditionPExpr := by
    unfold Expr.toPExpr
    rw [hcond_some]
    simp [pure, Except.pure]
  rcases matchGuard_ok_allMatches_singleton ctx cond k deps conditionPExpr fuel hcond hmatch
    with ⟨refMatches, href, hall⟩
  rcases singleton_allMatches_implies_var_or_ref (matchGuard_varMatches conditionPExpr ctx fuel)
      refMatches k deps hall with hvar | hrefMem
  · rcases var_match_from_varMatches ctx conditionPExpr k deps fuel hvar with
      ⟨x, qt, arg_name, pred_body, var_env, hlook, hpred, _hboth, hdeps⟩
    exact ⟨arg_name, pred_body, var_env, Or.inl ⟨x, qt, hlook, hpred⟩, deps, hdeps, fun _ hy => hy⟩
  · rcases ref_match_from_refMatches_clean ctx conditionPExpr k deps refMatches fuel href
        hrefMem with
      ⟨x, qt, ls, arg_name, pred_body, var_env, _hlook, _hEt, _hpois, hne, hls, _hboth, hdeps⟩
    obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∈ ls :=
      Classical.byContradiction fun hnone =>
        (ExtTreeSet.isEmpty_eq_false_iff.mp hne)
          (ExtTreeSet.eq_empty_iff_forall_not_mem.mpr fun a ha => hnone ⟨a, ha⟩)
    obtain ⟨memQt, hmem, hmpred⟩ := hls l0 hl0
    obtain ⟨d, hd, hsub⟩ := hdeps l0 hl0 memQt hmem
    rw [hmpred] at hd
    exact ⟨arg_name, pred_body, var_env, Or.inr ⟨l0, memQt, hmem, hmpred⟩, d, hd, hsub⟩
