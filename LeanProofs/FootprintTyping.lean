/-
  FootprintTyping.lean - The records of a typing run cover the footprints of
  their guards.

  A tag environment records, for each tag a test or an extern call has
  determined, a set of locations. `RecordsCover P env` says that each such set
  contains the footprint of the tag's descriptor in the table `P` (every set the
  dependency extraction computes for its guard closure). A successful typing run
  keeps this (`typecheck_preserves_recordsCover`), for every table that contains
  the starting table and every allocation of the run; `typingKeepsRecordsCover`
  states it for the tables the step theorems use.

  Pieces: the extraction gives one set at every fuel at which it succeeds
  (`extractDepsFromPred_fuel_det`); `RecordsCover` under a smaller table, a
  filter (both invalidations), an insert of a covering record, the join of two
  branches, the guards an extern call installs, and the record a matched `if`
  makes.
-/
import LeanProofs.MatchGuardLemmas

open List
open Std

private theorem foldlM_ok_mono {α β ε : Type} (l : List α) (F G : β → α → Except ε β) (init r : β)
    (hFG : ∀ acc x r, x ∈ l → F acc x = .ok r → G acc x = .ok r) :
    l.foldlM F init = .ok r → l.foldlM G init = .ok r := by
  induction l generalizing init with
  | nil => intro h; simpa using h
  | cons x xs ih =>
      intro h
      simp only [List.foldlM_cons] at h ⊢
      cases hF : F init x with
      | error e => simp [hF, bind, Except.bind] at h
      | ok r1 =>
          have hG := hFG init x r1 (List.mem_cons_self ..) hF
          simp only [hF, bind, Except.bind] at h
          simp only [hG, bind, Except.bind]
          exact ih r1 (fun acc y r hy => hFG acc y r (List.mem_cons_of_mem _ hy)) h

private theorem bind_ok_mono {ε α β : Type} {X Y : Except ε α} {F : α → β} {r : β}
    (h : ∀ d, X = .ok d → Y = .ok d) :
    (do let d ← X; pure (F d) : Except ε β) = .ok r → (do let d ← Y; pure (F d) : Except ε β) = .ok r := by
  cases hX : X with
  | error e => simp [bind, Except.bind]
  | ok d => rw [h d hX]; exact id

private theorem extract_fuel_mono :
    ∀ (f : Nat) (pe : PExpr) (bound : List Name) (env : VarTypeEnv) (deps : Deps),
      extractDepsFromPred.extractDepsFromPExpr pe bound env f = .ok deps →
      ∀ f', f ≤ f' → extractDepsFromPred.extractDepsFromPExpr pe bound env f' = .ok deps := by
  intro f
  induction f with
  | zero =>
      intro pe bound env deps h
      simp [extractDepsFromPred.extractDepsFromPExpr, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
      intro pe bound env deps h f' hf'
      obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
      have hfg : f ≤ g := by omega
      cases pe with
      | var y =>
          revert h
          simp only [extractDepsFromPred.extractDepsFromPExpr]
          split
          · exact id
          · split
            · split
              · exact id
              · rename_i tcls _
                intro h
                refine foldlM_ok_mono _ _ _ _ _ ?_ h
                intro acc tcl r _ hx
                cases tcl with
                | regular argName body varEnv' =>
                    revert hx
                    simp only
                    cases h1 : extractDepsFromPred.extractDepsFromPExpr body [argName]
                        (VarTypeEnv.ofCaptured varEnv') f with
                    | error e => simp [bind, Except.bind]
                    | ok d1 =>
                        simp only [ih _ _ _ d1 h1 g hfg]
                        exact id
                | extern _eid argName retSpec capEnv _argQt captures =>
                    revert hx
                    simp only
                    split
                    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
                    · intro hx
                      refine bind_ok_mono (fun d hd => ?_) hx
                      refine foldlM_ok_mono _ _ _ _ _ ?_ hd
                      intro dacc x r _ hy
                      revert hy
                      cases h2 : extractDepsFromPred.extractDepsFromPExpr (PExpr.var x.1) x.2
                          (VarTypeEnv.ofCaptured capEnv) f with
                      | error e => simp [bind, Except.bind]
                      | ok d2 =>
                          simp only [ih _ _ _ d2 h2 g hfg]
                          exact id
              · simp [throw, throwThe, MonadExceptOf.throw]
              · exact id
            · simp [throw, throwThe, MonadExceptOf.throw]
      | deref p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          exact ih p bound env deps h g hfg
      | unaryop o p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          exact ih p bound env deps h g hfg
      | op p o q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp only [h1, h2, bind, Except.bind] at h
              simp only [ih p bound env d1 h1 g hfg, ih q bound env d2 h2 g hfg, bind, Except.bind]
              exact h
      | app p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp only [h1, h2, bind, Except.bind] at h
              simp only [ih p bound env d1 h1 g hfg, ih q bound env d2 h2 g hfg, bind, Except.bind]
              exact h
      | vlet y p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q (y :: bound) env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              simp only [h1, h2, bind, Except.bind] at h
              simp only [ih p bound env d1 h1 g hfg, ih q (y :: bound) env d2 h2 g hfg, bind, Except.bind]
              exact h
      | ite p q r =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          cases h1 : extractDepsFromPred.extractDepsFromPExpr p bound env f with
          | error e => simp [h1, bind, Except.bind] at h
          | ok d1 =>
            cases h2 : extractDepsFromPred.extractDepsFromPExpr q bound env f with
            | error e => simp [h1, h2, bind, Except.bind] at h
            | ok d2 =>
              cases h3 : extractDepsFromPred.extractDepsFromPExpr r bound env f with
              | error e => simp [h1, h2, h3, bind, Except.bind] at h
              | ok d3 =>
                simp only [h1, h2, h3, bind, Except.bind] at h
                simp only [ih p bound env d1 h1 g hfg, ih q bound env d2 h2 g hfg,
                  ih r bound env d3 h3 g hfg, bind, Except.bind]
                exact h
      | _ =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h ⊢
          exact h

/-- Two fuels at which the extraction succeeds give the same set. -/
private theorem extract_fuel_det {pe : PExpr} {bound : List Name} {env : VarTypeEnv} {f₁ f₂ : Nat}
    {d₁ d₂ : Deps}
    (h₁ : extractDepsFromPred.extractDepsFromPExpr pe bound env f₁ = .ok d₁)
    (h₂ : extractDepsFromPred.extractDepsFromPExpr pe bound env f₂ = .ok d₂) : d₁ = d₂ := by
  rcases Nat.le_total f₁ f₂ with h | h
  · have := extract_fuel_mono f₁ pe bound env d₁ h₁ f₂ h
    rw [this] at h₂; exact Except.ok.inj h₂
  · have := extract_fuel_mono f₂ pe bound env d₂ h₂ f₁ h
    rw [this] at h₁; exact (Except.ok.inj h₁).symm

/-- The same for a predicate. -/
theorem extractDepsFromPred_fuel_det {pred : Predicate} {f₁ f₂ : Nat} {d₁ d₂ : Deps}
    (h₁ : extractDepsFromPred pred f₁ = .ok d₁) (h₂ : extractDepsFromPred pred f₂ = .ok d₂) :
    d₁ = d₂ := by
  cases pred with
  | guardClosure k arg body cap =>
      exact extract_fuel_det (by simpa [extractDepsFromPred] using h₁) (by simpa [extractDepsFromPred] using h₂)
  | guardOnly k =>
      simp [extractDepsFromPred, pure, Except.pure] at h₁ h₂; rw [← h₁, ← h₂]
  | noPred =>
      simp [extractDepsFromPred, pure, Except.pure] at h₁ h₂; rw [← h₁, ← h₂]

/-! ### `RecordsCover` under the operations on tag environments -/

private theorem mem_union {l : Loc} {s t : LocSet} :
    l ∈ LocSet.union s t ↔ l ∈ s ∨ l ∈ t := by
  simp [LocSet.union, ExtTreeSet.mem_union_iff]

private theorem contains_union_left {l : Loc} {s t : LocSet} (h : s.contains l = true) :
    (LocSet.union s t).contains l = true :=
  ExtTreeSet.contains_iff_mem.mpr (mem_union.mpr (Or.inl (ExtTreeSet.contains_iff_mem.mp h)))

private theorem contains_union_right {l : Loc} {s t : LocSet} (h : t.contains l = true) :
    (LocSet.union s t).contains l = true :=
  ExtTreeSet.contains_iff_mem.mpr (mem_union.mpr (Or.inr (ExtTreeSet.contains_iff_mem.mp h)))

/-- The records only get easier to cover on a smaller table. -/
theorem RecordsCover.anti {P tm : TagMeaning} {env : TagEnv} (h : RecordsCover P env)
    (hsub : tm ⊑ P) : RecordsCover tm env :=
  fun k tv d hk hd l hl => h k tv d hk (hsub k d hd) l hl

/-- A filter of the records keeps them covering. -/
theorem RecordsCover.filter {P : TagMeaning} {env : TagEnv} {f : Tag → TagVal → Bool}
    (h : RecordsCover P env) : RecordsCover P (env.filter f) := by
  intro k tv d hk hd l hl
  have hk' : env.get? k = some tv := by
    rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_filter'] at hk
    cases hget : env[k]? with
    | none => simp [hget] at hk
    | some tv' =>
        simp only [hget, Option.filter] at hk
        split at hk
        · cases hk; simpa [ExtTreeMap.get?_eq_getElem?] using hget
        · cases hk
  exact h k tv d hk' hd l hl

theorem RecordsCover.invalidateTagDeps {P : TagMeaning} {env : TagEnv} {ls : LocSet}
    (h : RecordsCover P env) : RecordsCover P (invalidateTagDeps env ls) :=
  RecordsCover.filter h

/-- Inserting a record that covers its tag's footprint keeps the records covering. -/
theorem RecordsCover.insert {P : TagMeaning} {env : TagEnv} {k : Tag} {tv : TagVal}
    (h : RecordsCover P env)
    (hk : ∀ d, P.lookup k = some d → ∀ l, InFootprint k d l → tv.deps.contains l = true) :
    RecordsCover P (env.insert k tv) := by
  intro k' tv' d hk' hd l hl
  by_cases hkk : k = k'
  · subst hkk
    have : tv' = tv := by
      simpa [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert_self] using hk'.symm
    subst this
    exact hk d hd l hl
  · have hk'' : env.get? k' = some tv' := by
      have hcmp : compare k k' ≠ Ordering.eq := by
        intro hc; exact hkk (Nat.compare_eq_eq.mp hc)
      simpa [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, hcmp] using hk'
    exact h k' tv' d hk'' hd l hl

/-- A record of the join of two tag environments has a record on each side and
    unites their sets. -/
private theorem joinTagEnvs_get_some {env₁ env₂ : TagEnv} {k : Tag} {tv : TagVal}
    (hget : (joinTagEnvs env₁ env₂).get? k = some tv) :
    ∃ tv₁ tv₂, env₁.get? k = some tv₁ ∧ env₂.get? k = some tv₂ ∧
      tv.deps = LocSet.union tv₁.deps tv₂.deps := by
  unfold joinTagEnvs at hget
  let f : Tag → Option TagVal → Option TagVal → Option TagVal := fun _ otv1 otv2 =>
    match otv1, otv2 with
    | some ⟨b1, deps1⟩, some ⟨b2, deps2⟩ =>
        if b1 == b2 then some ⟨b1, LocSet.union deps1 deps2⟩ else none
    | some _, none => none
    | none, some _ => none
    | none, none => none
  have hcombine : (combineExtTreeMaps env₁ env₂ f).get? k = some tv := hget
  simp only [combineExtTreeMaps] at hcombine
  have hk_mem : k ∈ (env₁.keys ++ env₂.keys).eraseDups := by
    by_contra hnot
    have := combineExtTreeMaps_go_get_not_mem env₁ env₂ f
      (env₁.keys ++ env₂.keys).eraseDups ({} : TagEnv) k hnot
    simp [this] at hcombine
  have hgo := combineExtTreeMaps_go_get_mem env₁ env₂ f
    (env₁.keys ++ env₂.keys).eraseDups ({} : TagEnv) k hk_mem
  simp only [ExtTreeMap.get?_eq_getElem?] at hcombine hgo
  rw [hcombine] at hgo
  simp only [f] at hgo
  cases h1 : env₁.get? k <;> cases h2 : env₂.get? k
  · simp [← ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · simp [← ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · simp [← ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
  · rename_i val1 val2
    rcases val1 with ⟨b1, deps1⟩
    rcases val2 with ⟨b2, deps2⟩
    refine ⟨⟨b1, deps1⟩, ⟨b2, deps2⟩, rfl, rfl, ?_⟩
    by_cases hb : b1 = b2
    · subst hb
      simp [← ExtTreeMap.get?_eq_getElem?, h1, h2] at hgo
      subst hgo
      rfl
    · simp [← ExtTreeMap.get?_eq_getElem?, h1, h2, hb] at hgo

theorem RecordsCover.join {P : TagMeaning} {env₁ env₂ : TagEnv}
    (h₁ : RecordsCover P env₁) (_h₂ : RecordsCover P env₂) :
    RecordsCover P (joinTagEnvs env₁ env₂) := by
  intro k tv d hk hd l hl
  obtain ⟨tv₁, tv₂, hk₁, _hk₂, hdeps⟩ := joinTagEnvs_get_some hk
  rw [hdeps]
  exact contains_union_left (h₁ k tv₁ d hk₁ hd l hl)

/-- A record of an extraction's set covers the footprint of the closure. -/
private theorem covers_of_extract {k : Tag} {arg : Name} {body : PExpr} {cap : CapturedVarEnv}
    {fuel : Nat} {deps : Deps}
    (hx : extractDepsFromPred (Predicate.guardClosure k arg body cap) fuel = .ok deps) :
    ∀ l, InFootprint k { argName := arg, body := body, capEnv := cap } l → deps.contains l = true := by
  intro l ⟨f', d', hx', hl⟩
  have := extractDepsFromPred_fuel_det hx' hx
  subst this
  exact hl

/-- The guard an extern call installs on its returned value keeps the records
    covering, when the table's descriptor of its tag is the installed closure. -/
theorem RecordsCover.installReturnGuard {P : TagMeaning} {env : TagEnv} {pred : Predicate}
    {R : Regime} {fuel : Nat} (h : RecordsCover P env)
    (hdesc : ∀ k arg body cap, pred = Predicate.guardClosure k arg body cap →
      ∀ d, P.lookup k = some d → d = { argName := arg, body := body, capEnv := cap }) :
    RecordsCover P (_root_.installReturnGuard env pred R fuel) := by
  unfold _root_.installReturnGuard
  split
  · rename_i k arg body cap
    split
    · rename_i b _
      split
      · rename_i deps hx
        refine RecordsCover.insert h ?_
        intro d hd l hl
        have hdd := hdesc k arg body cap rfl d hd
        subst hdd
        exact covers_of_extract hx l hl
      · exact h
    · exact h
  · exact h

private theorem cover_aux {P : TagMeaning} {k : Tag} {arg : Name} {body : PExpr} {cap : CapturedVarEnv}
    {fuel : Nat} {deps : Deps}
    (hd' : ∀ d, P.lookup k = some d → d = { argName := arg, body := body, capEnv := cap })
    (hx : extractDepsFromPred (Predicate.guardClosure k arg body cap) fuel = .ok deps) :
    ∀ d, P.lookup k = some d → ∀ l, InFootprint k d l → deps.contains l = true := by
  intro d hd l hl
  have := hd' d hd
  subst this
  exact covers_of_extract hx l hl

/-- The guards an extern call installs on the cells its effects write keep the
    records covering, when the table's descriptor of each such tag is the
    resolved closure. -/
theorem RecordsCover.installEffectGuards {P : TagMeaning} {env : TagEnv} {effects : List Effect}
    {unifiedEnv : VarTypeEnv} {tagMapping : TagMapping} {pc : Poison} {R : Regime} {fuel : Nat}
    (h : RecordsCover P env)
    (hdesc : ∀ effect ∈ effects, ∀ k arg body cap,
      resolveSyntaxPred effect.pred unifiedEnv tagMapping = .ok (Predicate.guardClosure k arg body cap) →
      ∀ d, P.lookup k = some d → d = { argName := arg, body := body, capEnv := cap }) :
    RecordsCover P (_root_.installEffectGuards env effects unifiedEnv tagMapping pc R fuel) := by
  unfold _root_.installEffectGuards
  induction effects generalizing env with
  | nil => simpa using h
  | cons eff effs ih =>
      simp only [List.foldl_cons]
      apply ih _ (fun e he => hdesc e (List.mem_cons_of_mem _ he))
      have hd₀ := hdesc eff (List.mem_cons_self ..)
      repeat' split
      all_goals first
        | exact h
        | exact RecordsCover.insert h (fun d hd l hl => contains_union_right (contains_union_right
            (cover_aux (hd₀ _ _ _ _ (by assumption)) (by assumption) d hd l hl)))
        | exact RecordsCover.insert h (fun d hd l hl => contains_union_right
            (cover_aux (hd₀ _ _ _ _ (by assumption)) (by assumption) d hd l hl))

/-- The record a matched `if` makes covers the footprint of the matched tag, in a
    table the context respects. -/
theorem RecordsCover.matched {P : TagMeaning} {ctx : TypeContext} {cond : Expr}
    {k : Tag} {deps : Deps} {fuel : Nat} {b : Bool}
    (hwf : wfTagMeaningCtx P ctx) (h : RecordsCover P ctx.tagEnv)
    (hmatch : matchGuard cond ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    RecordsCover P (ctx.tagEnv.insert k ⟨b, deps⟩) := by
  obtain ⟨arg, body, cap, howner, d, hd, hsub⟩ := matchGuard_ok_extract_sub ctx cond k deps hmatch
  have hdesc : P.lookup k = some { argName := arg, body := body, capEnv := cap } := by
    rcases howner with ⟨x, qt, hlook, hpred⟩ | ⟨l0, memQt, hmem, hpred⟩
    · exact wfTagMeaningCtx_var_lookup_qtyp P ctx x qt hwf hlook (QTypInQTyp.self qt)
        (by simp [qtypGuardDesc?, hpred])
    · exact wfTagMeaningCtx_mem_lookup_qtyp P ctx l0 memQt hwf hmem (QTypInQTyp.self memQt)
        (by simp [qtypGuardDesc?, hpred])
  refine RecordsCover.insert h ?_
  intro d' hd' l hl
  rw [hdesc] at hd'
  cases hd'
  have hcov := covers_of_extract hd l hl
  exact ExtTreeSet.contains_iff_mem.mpr (hsub l (ExtTreeSet.contains_iff_mem.mp hcov))

/-! ### Helpers for the induction -/

/-- After a sub-run, a table for its final context inside `P`. -/
private theorem next_table {fuel : Nat} {ctx : TypeContext} {e : Expr} {res : TypeResult}
    {tm P : TagMeaning}
    (htc : typecheck ctx e fuel = .ok res) (hwf : wfTagMeaningCtx tm ctx)
    (hb : TagMeaningBounded tm ctx.nextTag) (hsub : tm ⊑ P) (hL : LogIn res.tagLog' P) :
    ∃ tm', wfTagMeaningCtx tm' (ctxAfter ctx res) ∧ TagMeaningBounded tm' res.nextTag' ∧ tm' ⊑ P := by
  obtain ⟨tm', hcanon, hsub'⟩ := typecheck_canonical_sub P tm ctx e fuel res hwf hb hsub hL htc
  exact ⟨tm', hcanon.wfCtx, hcanon.bounded, hsub'⟩

/-- A guard closure that `resolveSyntaxPred` gives for a predicate of `preds` is an
    allocation of `externTagLog preds` over the same environment and mapping. -/
private theorem resolve_mem_externTagLog {pred : SyntaxPredicate} {preds : List SyntaxPredicate}
    {env : VarTypeEnv} {mapping : TagMapping} {k : Tag} {arg : Name} {body : PExpr}
    {cap : CapturedVarEnv}
    (hmem : pred ∈ preds)
    (hres : resolveSyntaxPred pred env mapping = .ok (Predicate.guardClosure k arg body cap)) :
    ∃ a ∈ externTagLog preds env mapping, a.tag = k ∧
      a.desc = { argName := arg, body := body, capEnv := cap } := by
  cases pred with
  | noPred => simp [resolveSyntaxPred, pure, Except.pure] at hres
  | guardOnly idx =>
      simp only [resolveSyntaxPred] at hres
      split at hres <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hres
  | guardClosure idx a b =>
      simp only [resolveSyntaxPred, bind, Except.bind] at hres
      split at hres
      · rename_i tag htag
        cases hb : b.toPExpr with
        | error e => simp [hb] at hres
        | ok pb =>
            simp [hb, pure, Except.pure] at hres
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hres
            refine ⟨{ tag := tag, argName := a, body := pb, capEnv := VarTypeEnv.toCaptured env }, ?_, rfl, rfl⟩
            simp only [externTagLog, List.mem_filterMap]
            refine ⟨_, hmem, ?_⟩
            simp only [htag, hb]
      · simp [throw, throwThe, MonadExceptOf.throw] at hres

/-- In a table that records the log, the descriptor of an installed tag is the
    resolved closure. -/
private theorem desc_of_resolve {P : TagMeaning} {pred : SyntaxPredicate}
    {preds : List SyntaxPredicate} {env : VarTypeEnv} {mapping : TagMapping}
    (hL : LogIn (externTagLog preds env mapping) P) (hmem : pred ∈ preds) :
    ∀ k arg body cap, resolveSyntaxPred pred env mapping = .ok (Predicate.guardClosure k arg body cap) →
      ∀ d, P.lookup k = some d → d = { argName := arg, body := body, capEnv := cap } := by
  intro k arg body cap hres d hd
  obtain ⟨a, ha, hak, had⟩ := resolve_mem_externTagLog hmem hres
  have := hL a ha
  rw [hak, had, hd] at this
  exact Option.some.inj this

/-! ### The invariant along a typing run -/

/-- The join of two environments: a record is covered when the left side covers it. -/
private theorem RecordsCover.join_left {P : TagMeaning} {env₁ env₂ : TagEnv}
    (h₁ : RecordsCover P env₁) : RecordsCover P (joinTagEnvs env₁ env₂) := by
  intro k tv d hk hd l hl
  obtain ⟨tv₁, _tv₂, hk₁, _hk₂, hdeps⟩ := joinTagEnvs_get_some hk
  rw [hdeps]
  exact contains_union_left (h₁ k tv₁ d hk₁ hd l hl)

/-- The join of the results of closure members keeps the records of the first member. -/
private theorem joinTypeResults_records {P : TagMeaning}
    (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult) (res : TypeResult)
    (h_join : joinTypeResults ctx first rest = .ok res)
    (h_first : RecordsCover P first.tagEnv') :
    RecordsCover P res.tagEnv' := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun (acc : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) (result : TypeResult) =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        RecordsCover P acc.2.2.2.2.1 →
        RecordsCover P acc'.2.2.2.2.1 := by
    intro rs' acc acc' hfold hacc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        exact hacc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv',
                joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred,
                joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc',
                max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hacc1 : RecordsCover P acc1.2.2.2.2.1 :=
              RecordsCover.join_left hacc
            exact ih (acc := acc1) hfold_tail hacc1
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at h_join
          simp at h_join
      | ok _ =>
          erw [hcheck] at h_join
          simp at h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                  first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at h_join
              simp at h_join
          | ok a =>
              erw [hfold] at h_join
              simp at h_join
              subst res
              have hres :=
                h_fold rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                    first.nextLoc', first.nextTag')
                  a hfold h_first
              simpa using hres

/-- The assignment's tag environment: the invalidation of the second run's. -/
private theorem assign_tagEnv {ctx : TypeContext} {e1 e2 : Expr} {fuel : Nat}
    {res result1 result2 : TypeResult} {ls : LocSet}
    (h : typecheckAssign ctx e1 e2 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok result1)
    (hls : result1.qualType.etyp = ETyp.ref ls)
    (h2 : typecheckExpr (updateCtxFromResult ctx result1) e2 (fuel - 1) = .ok result2) :
    res.tagEnv' = invalidateTagDeps result2.tagEnv' ls := by
  cases fuel with
  | zero => simp [typecheckAssign, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel, updateCtxFromResult] at h1 h2
    unfold typecheckAssign at h
    simp only [bind, Except.bind, h1, h2] at h
    generalize hq1 : result1.qualType = q1 at h hls
    obtain ⟨etyp1, p1, pred1⟩ := q1
    simp only at hls
    subst hls
    simp only at h
    generalize hq2 : result2.qualType = q2 at h
    obtain ⟨etyp2, p2, pred2⟩ := q2
    simp only at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl

/-- The predicates of the effects are among the predicates of the call. -/
private theorem effect_pred_mem_collect (retSpec : ExternReturn) (effects : List Effect)
    (effect : Effect) (hmem : effect ∈ effects) :
    effect.pred ∈ collectExternPreds retSpec effects := by
  cases retSpec with
  | simple _ _ pred =>
    simp only [collectExternPreds]
    exact List.mem_append_right _ (List.mem_map_of_mem hmem)
  | nestedFn _ _ _ _ _ _ _ _ =>
    simp only [collectExternPreds]
    exact List.mem_map_of_mem hmem
  | nestedPfn _ _ _ _ _ _ _ =>
    simp only [collectExternPreds]
    exact List.mem_map_of_mem hmem

/-- An impure extern call that returns a value with a guard. -/
private theorem records_externSimple {P : TagMeaning} {tagEnv : TagEnv} {locs : LocSet}
    {R : Regime} {fuel : Nat} {effects : List Effect} {unifiedEnv : VarTypeEnv}
    {tagMapping : TagMapping} {pc : Poison} {preds : List SyntaxPredicate}
    {pred : SyntaxPredicate} {resolvedPred : Predicate}
    (hrec : RecordsCover P tagEnv)
    (hL : LogIn (externTagLog preds unifiedEnv tagMapping) P)
    (hpred : pred ∈ preds) (hpreds : ∀ e ∈ effects, e.pred ∈ preds)
    (hres : resolveSyntaxPred pred unifiedEnv tagMapping = .ok resolvedPred) :
    RecordsCover P (installEffectGuards
      (installReturnGuard (invalidateTagDeps tagEnv locs) resolvedPred R fuel)
      effects unifiedEnv tagMapping pc R fuel) := by
  refine RecordsCover.installEffectGuards ?_ (fun eff he => desc_of_resolve hL (hpreds eff he))
  refine RecordsCover.installReturnGuard (RecordsCover.invalidateTagDeps hrec) ?_
  intro k arg body cap hp
  exact desc_of_resolve hL hpred k arg body cap (by rw [hres, hp])

/-- An impure extern call that returns a function. -/
private theorem records_externEffects {P : TagMeaning} {tagEnv : TagEnv} {locs : LocSet}
    {R : Regime} {fuel : Nat} {effects : List Effect} {unifiedEnv : VarTypeEnv}
    {tagMapping : TagMapping} {pc : Poison} {preds : List SyntaxPredicate}
    (hrec : RecordsCover P tagEnv)
    (hL : LogIn (externTagLog preds unifiedEnv tagMapping) P)
    (hpreds : ∀ e ∈ effects, e.pred ∈ preds) :
    RecordsCover P (installEffectGuards (invalidateTagDeps tagEnv locs)
      effects unifiedEnv tagMapping pc R fuel) :=
  RecordsCover.installEffectGuards (RecordsCover.invalidateTagDeps hrec)
    (fun eff he => desc_of_resolve hL (hpreds eff he))

/-- An application of an impure extern closure keeps the records covering. -/
private theorem records_applyFnExtern {P : TagMeaning}
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (r1 r2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect)
    (capturedEnv : CapturedVarEnv) (declaredArgQt : QTyp) {captures : List Capture}
    (happly : applyFnTClosure
      (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx r1 fuel = .ok r2)
    (hL : LogIn r2.tagLog' P) (hrec : RecordsCover P r1.tagEnv') :
    RecordsCover P r2.tagEnv' := by
  unfold applyFnTClosure at happly
  cases fuel with
  | zero => simp at happly
  | succ n =>
      simp only [bind, Except.bind] at happly
      split at happly
      · exact nomatch happly
      simp only [pure, Except.pure] at happly
      split at happly
      · exact nomatch happly
      · next tmRes hcollect =>
        obtain ⟨tm, nt'⟩ := tmRes
        split at happly
        · exact nomatch happly
        · split at happly
          · -- ExternReturn.simple
            split at happly
            · exact nomatch happly
            · next resolvedPred hresolve =>
              split at happly
              · exact nomatch happly
              · split at happly
                · exact nomatch happly
                cases happly
                exact records_externSimple hrec hL (by simp [collectExternPreds])
                  (fun e he => effect_pred_mem_collect _ _ e he) hresolve
          · -- ExternReturn.nestedFn
            split at happly
            · exact nomatch happly
            · next v hargCond =>
              split at happly
              · exact nomatch happly
              cases happly
              exact records_externEffects hrec hL
                (fun e he => effect_pred_mem_collect _ _ e he)
          · -- ExternReturn.nestedPfn
            split at happly
            · exact nomatch happly
            · next v hargCond =>
              split at happly
              · exact nomatch happly
              cases happly
              exact records_externEffects hrec hL
                (fun e he => effect_pred_mem_collect _ _ e he)

/-- An application of a pure extern closure keeps the records covering. -/
private theorem records_applyPFnExtern {P : TagMeaning}
    (ctx : TypeContext) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (r1 r2 : TypeResult) (fuel : Nat)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (capturedEnv : CapturedVarEnv)
    (declaredArgQt : QTyp) {captures : List Capture}
    (happly : applyPFnTClosure
      (PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures) st1 st2 p p1
      argEtyp argPoison argPred ctx r1 fuel = .ok r2)
    (hL : LogIn r2.tagLog' P) (hrec : RecordsCover P r1.tagEnv') :
    RecordsCover P r2.tagEnv' := by
  unfold applyPFnTClosure at happly
  cases fuel with
  | zero => simp at happly
  | succ n =>
      simp only [bind, Except.bind] at happly
      split at happly
      · exact nomatch happly
      simp only [pure, Except.pure] at happly
      split at happly
      · -- ExternReturn.simple
        split at happly
        · exact nomatch happly
        · next tmRes hcollect =>
          obtain ⟨tm, nt'⟩ := tmRes
          split at happly
          · exact nomatch happly
          · next resolvedPred hresolve =>
            split at happly
            · exact nomatch happly
            · split at happly
              · exact nomatch happly
              cases happly
              refine RecordsCover.installReturnGuard hrec ?_
              intro k arg body cap hp
              exact desc_of_resolve hL (List.mem_singleton_self _) k arg body cap
                (by rw [hresolve, hp])
      · -- ExternReturn.nestedFn
        split at happly
        · exact nomatch happly
        · cases happly; exact hrec
      · -- ExternReturn.nestedPfn
        split at happly
        · exact nomatch happly
        · cases happly; exact hrec

/-- A successful typing run keeps the records covering the footprints of their tags,
    in every table that contains the starting table and the run's allocations. -/
theorem typecheck_preserves_recordsCover :
    ∀ (fuel : Nat) (tm P : TagMeaning) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    wfTagMeaningCtx tm ctx → TagMeaningBounded tm ctx.nextTag → tm ⊑ P →
    LogIn res.tagLog' P →
    RecordsCover P ctx.tagEnv →
    typecheck ctx e fuel = .ok res →
    RecordsCover P res.tagEnv' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro tm P ctx e res hwf hb hsub hL hrec htc
    unfold typecheck at htc
    cases fuel with
    | zero =>
        unfold typecheckExpr at htc
        simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact hrec
        | bool _b =>
            unfold typecheckBool at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact hrec
        | unit =>
            unfold typecheckUnit at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact hrec
        | str _s =>
            unfold typecheckString at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact hrec
        | var x =>
            simp at htc
            unfold typecheckVar at htc
            simp only [bind, Except.bind] at htc
            cases hlookup : ctx.varEnv.lookup x with
            | none => simp [hlookup] at htc
            | some qt =>
              simp [hlookup] at htc
              cases qt with
              | mk etyp poison pred =>
                simp at htc
                cases pred with
                | noPred =>
                    simp [pure, Except.pure] at htc
                    cases htc
                    exact hrec
                | guardOnly k =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          exact hrec
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                exact hrec
                | guardClosure k tcls ptcls body_t =>
                    simp at htc
                    by_cases hfn : etyp.isFunctionType
                    · simp [hfn] at htc
                    · simp [hfn] at htc
                      revert htc
                      generalize htv : ctx.tagEnv[k]? = tv
                      cases tv with
                      | none =>
                          intro htc
                          simp at htc
                          cases htc
                          exact hrec
                      | some tv =>
                          cases tv with
                          | mk val deps =>
                              cases val <;> intro htc <;> simp at htc <;> cases htc <;>
                                exact hrec
        | fn _ _ _ _ =>
            have hfn := typecheckFn_ok_eq htc
            subst hfn
            exact hrec
        | pfn x st1 body st2 =>
            unfold typecheckPfn at htc
            simp [bind, Except.bind] at htc
            cases h_topexpr : body.toPExpr with
            | error _ => simp [h_topexpr] at htc
            | ok _ =>
                simp [h_topexpr, pure, Except.pure] at htc
                subst htc
                exact hrec
        | externVal id typ poison pred =>
            have htc' : typecheckExternVal ctx id typ poison pred fuel' = .ok res := htc
            obtain ⟨_, tagMapping, _, resolvedPred, _, _halloc, hres, _, rfl⟩ :=
              typecheckExternVal_ok_shape htc'
            refine RecordsCover.installReturnGuard hrec ?_
            intro k arg body cap hp
            exact desc_of_resolve hL (List.mem_singleton_self _) k arg body cap
              (by rw [hres, hp])
        | externRef _ _ _ _ _ =>
            simp only [typecheckExternRef] at htc
            simp [Bind.bind, Except.bind, pure, Except.pure] at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            split at htc <;> simp (config := { failIfUnchanged := false }) at htc
            cases htc
            exact hrec
        | externFn id arg argTyp argPoison argPred retSpec effects cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternFn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec effects res htc
            rw [hres]
            exact hrec
        | externPfn id arg argTyp argPoison argPred retSpec cap =>
            obtain ⟨argQt, _, hres⟩ :=
              typecheckExternPfn_ok_res_eq ctx id arg argTyp argPoison argPred retSpec res htc
            rw [hres]
            exact hrec
        | unaryop op e1 =>
            have hstruct := typecheckUnaryOp_structure ctx op e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, htag, _, _hnextTag, _hreg', _, _, _⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              (hL.of_log_eq (typecheckUnaryOp_tagLog htc htc1)) hrec htc1'
            rw [htag]
            exact hIH
        | deref e1 =>
            have hstruct := typecheckDeref_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, htc1, _, htag, _, _hnextTag, _hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              (hL.of_log_eq (typecheckDeref_tagLog htc htc1)) hrec htc1'
            rw [htag]
            exact hIH
        | newRef e1 =>
            have hstruct := typecheckNewRef_structure ctx e1 fuel' res htc
            rcases hstruct with ⟨result1, _, htc1, _, _, _, _, _, _, htag, _, _hnextTag, _hreg'⟩
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            have hIH := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              (hL.of_log_eq (typecheckNewRef_tagLog htc htc1)) hrec htc1'
            rw [htag]
            exact hIH
        | op e1 op e2 =>
            have hstruct := typecheckOp_structure ctx e1 e2 op fuel' res htc
            rcases hstruct with ⟨result1, result2, _, htc1, htc2, _, _, htag, _, _hnextTag, _hregime', _, _, _⟩
            have hLs := hL.of_log_eq (typecheckOp_tagLog htc htc1 htc2)
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            obtain ⟨tm1, hcanon1, hP1⟩ :=
              typecheck_canonical_sub P tm ctx e1 (fuel' - 1) result1 hwf hb hsub hLs.left htc1'
            have hIH1 := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              hLs.left hrec htc1'
            have hwf_mid : wfTagMeaningCtx tm1 (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
                IsCanonicalExtension.wfCtx hcanon1
            have hb_mid : TagMeaningBounded tm1 (updateCtxFromResult ctx result1).nextTag := by
              simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
            have htc2' :
                typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            have hIH2 := IH (fuel' - 1) (by omega) tm1 P (updateCtxFromResult ctx result1) e2
              result2 hwf_mid hb_mid hP1 hLs.right (by simpa [updateCtxFromResult] using hIH1) htc2'
            rw [htag]
            exact hIH2
        | seq e1 e2 =>
            have hstruct := typecheckSeq_structure ctx e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, ctx', result2, htc1, hctx', htc2, rfl⟩
            subst hctx'
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            obtain ⟨tm1, hcanon1, hP1⟩ :=
              typecheck_canonical_sub P tm ctx e1 (fuel' - 1) result1 hwf hb hsub hL.left htc1'
            have hIH1 := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              hL.left hrec htc1'
            have hwf_mid : wfTagMeaningCtx tm1 (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
                IsCanonicalExtension.wfCtx hcanon1
            have hb_mid : TagMeaningBounded tm1 (updateCtxFromResult ctx result1).nextTag := by
              simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
            have htc2' :
                typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            exact IH (fuel' - 1) (by omega) tm1 P (updateCtxFromResult ctx result1) e2
              result2 hwf_mid hb_mid hP1 hL.right (by simpa [updateCtxFromResult] using hIH1) htc2'
        | vlet x e1 e2 =>
            have hstruct := typecheckVlet_structure ctx x e1 e2 fuel' res htc
            rcases hstruct with ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, htag, _, _hnextTag, _hregime', _, _⟩
            subst hctx'
            have hLs := hL.of_log_eq (typecheckVlet_tagLog htc htc1 htc2)
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            obtain ⟨tm1, hcanon1, hP1⟩ :=
              typecheck_canonical_sub P tm ctx e1 (fuel' - 1) result1 hwf hb hsub hLs.left htc1'
            have hIH1 := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              hLs.left hrec htc1'
            have hwf_mid : wfTagMeaningCtx tm1
                { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                           tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                           nextTag := result1.nextTag', regime := result1.regime',
                           declaredExternRefs := result1.declared' } := by
              have hwf_after : wfTagMeaningCtx tm1 (ctxAfter ctx result1) :=
                IsCanonicalExtension.wfCtx hcanon1
              simp only [wfTagMeaningCtx, ctxAfter] at hwf_after
              let ctxBase : TypeContext :=
                ⟨ctx.pc, result1.regime', result1.memEnv', ctx.varEnv, result1.tagEnv',
                 result1.nextLoc', result1.nextTag', ctx.pureCtx, ctx.externRegime,
                 ctx.externRefAllowed, result1.declared'⟩
              exact wfTagMeaningCtx_varEnv_ext tm1 ctxBase x result1.qualType
                (by simpa [wfTagMeaningCtx, ctxAfter, ctxBase] using hwf_after)
                (IsCanonicalExtension.respectsResult hcanon1)
            have hb_mid : TagMeaningBounded tm1
                ({ ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                            tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                            nextTag := result1.nextTag', regime := result1.regime',
                            declaredExternRefs := result1.declared' } : TypeContext).nextTag := by
              simpa using IsCanonicalExtension.bounded hcanon1
            have htc2' : typecheck
                { ctx with memEnv := result1.memEnv', varEnv := ctx.varEnv.update x result1.qualType,
                           tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                           nextTag := result1.nextTag', regime := result1.regime',
                           declaredExternRefs := result1.declared' } e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            have hIH2 := IH (fuel' - 1) (by omega) tm1 P _ e2 result2
              hwf_mid hb_mid hP1 hLs.right hIH1 htc2'
            rw [htag]
            exact hIH2
        | assign e1 e2 =>
            obtain ⟨result1, result2, ls, htc1, hRef, htc2, _, _, _, _, _, _, _⟩ :=
              typecheckAssign_structure ctx e1 e2 fuel' res htc
            have hLs := hL.of_log_eq (typecheckAssign_tagLog htc htc1 htc2)
            have htc1' : typecheck ctx e1 (fuel' - 1) = .ok result1 := by simpa using! htc1
            obtain ⟨tm1, hcanon1, hP1⟩ :=
              typecheck_canonical_sub P tm ctx e1 (fuel' - 1) result1 hwf hb hsub hLs.left htc1'
            have hIH1 := IH (fuel' - 1) (by omega) tm P ctx e1 result1 hwf hb hsub
              hLs.left hrec htc1'
            have hwf_mid : wfTagMeaningCtx tm1 (updateCtxFromResult ctx result1) := by
              simpa [wfTagMeaningCtx, ctxAfter, updateCtxFromResult] using
                IsCanonicalExtension.wfCtx hcanon1
            have hb_mid : TagMeaningBounded tm1 (updateCtxFromResult ctx result1).nextTag := by
              simpa [updateCtxFromResult] using IsCanonicalExtension.bounded hcanon1
            have htc2' :
                typecheck (updateCtxFromResult ctx result1) e2 (fuel' - 1) = .ok result2 := by
              simpa using! htc2
            have hIH2 := IH (fuel' - 1) (by omega) tm1 P (updateCtxFromResult ctx result1) e2
              result2 hwf_mid hb_mid hP1 hLs.right (by simpa [updateCtxFromResult] using hIH1) htc2'
            rw [assign_tagEnv htc htc1 hRef htc2]
            exact RecordsCover.invalidateTagDeps hIH2
        | ite e1 e2 e3 =>
            have hstruct := typecheckIf_structure ctx e1 e2 e3 fuel' res htc
            rcases hstruct with h1 | h2 | hstd
            · rcases h1 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, htag, _hnextLoc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
              let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                      nextTag := res1.nextTag',
                                                      declaredExternRefs := res1.declared' }
              have htc2' : typecheck ctxTrue e2 (fuel' - 1) = .ok res2 := by
                simpa [typecheck, ctxTrue] using htc2
              have hwf_true : wfTagMeaningCtx tm ctxTrue := by
                simpa [wfTagMeaningCtx, ctxTrue] using hwf
              have hb_true : TagMeaningBounded tm ctxTrue.nextTag := hb.mono hb1
              have hrec_true : RecordsCover P ctxTrue.tagEnv :=
                RecordsCover.matched (b := true) (wfTagMeaningCtx_mono hsub hwf) hrec
                  hmatch
              have hIH := IH (fuel' - 1) (by omega) tm P ctxTrue e2 res2 hwf_true hb_true hsub
                (hL.of_log_eq
                  (typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3)).left.right
                hrec_true htc2'
              rw [htag]
              exact hIH
            · rcases h2 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, htag, _hnextLoc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              have hb1 : ctx.nextTag ≤ res1.nextTag' :=
                typecheck_nextTag_mono { ctx with pureCtx := true } e1 (fuel' - 1) res1 htc1p
              let ctxTrue : TypeContext := { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                                                      nextTag := res1.nextTag',
                                                      declaredExternRefs := res1.declared' }
              let ctxFalse : TypeContext :=
                { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
                           nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                           declaredExternRefs := res2.declared' }
              have htc2' : typecheck ctxTrue e2 (fuel' - 1) = .ok res2 := by
                simpa [typecheck, ctxTrue] using htc2
              have hnextTag2 : ctx.nextTag ≤ res2.nextTag' :=
                Nat.le_trans hb1 (typecheck_nextTag_mono ctxTrue e2 (fuel' - 1) res2 htc2')
              have htc3' : typecheck ctxFalse e3 (fuel' - 1) = .ok res3 := by
                simpa [typecheck, ctxFalse] using htc3
              have hwf_false : wfTagMeaningCtx tm ctxFalse := by
                simpa [wfTagMeaningCtx, ctxFalse] using hwf
              have hb_false : TagMeaningBounded tm ctxFalse.nextTag := by
                simpa [ctxFalse] using hb.mono hnextTag2
              have hrec_false : RecordsCover P ctxFalse.tagEnv :=
                RecordsCover.matched (b := false) (wfTagMeaningCtx_mono hsub hwf) hrec
                  hmatch
              have hIH := IH (fuel' - 1) (by omega) tm P ctxFalse e3 res3 hwf_false hb_false hsub
                (hL.of_log_eq
                  (typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3)).right
                hrec_false htc3'
              rw [htag]
              exact hIH
            · obtain ⟨hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3_raw,
                _hmemEnv, htag, _hnextLoc, _hnextTag, _hregime, _hdecl, _hpoison,
                _hetyp_res, _hpred_res⟩ := hstd
              let ctx1 : TypeContext :=
                { ctx with memEnv := res1.memEnv', tagEnv := res1.tagEnv',
                           nextLoc := res1.nextLoc', nextTag := res1.nextTag', regime := res1.regime',
                           declaredExternRefs := res1.declared' }
              let pc' := joinPoison ctx.pc res1.qualType.poison
              let ctx'' := { ctx1 with pc := pc' }
              have htc1' : typecheck ctx e1 (fuel' - 1) = .ok res1 := by
                simpa [typecheck] using htc1
              have hLstd := hL.of_log_eq
                (typecheckIf_tagLog_std htc hstdCase htc1 htc2 htc3_raw)
              obtain ⟨tm1, hcanon1, hP1⟩ :=
                typecheck_canonical_sub P tm ctx e1 (fuel' - 1) res1 hwf hb hsub
                  hLstd.left.left htc1'
              have hIH1 := IH (fuel' - 1) (by omega) tm P ctx e1 res1 hwf hb hsub
                hLstd.left.left hrec htc1'
              have hwf_mid : wfTagMeaningCtx tm1 ctx'' := by
                simp only [wfTagMeaningCtx, ctx'', ctx1]
                simpa [wfTagMeaningCtx, ctxAfter] using
                  IsCanonicalExtension.wfCtx hcanon1
              have hb_mid : TagMeaningBounded tm1 ctx''.nextTag := by
                simpa [ctx'', ctx1] using IsCanonicalExtension.bounded hcanon1
              have htc2' : typecheck ctx'' e2 (fuel' - 1) = .ok res2 := by
                simpa [typecheck, ctx'', ctx1, pc'] using htc2
              have hIH2 := IH (fuel' - 1) (by omega) tm1 P ctx'' e2 res2 hwf_mid hb_mid
                hP1 hLstd.left.right (by simpa [ctx'', ctx1] using hIH1) htc2'
              rw [htag]
              exact RecordsCover.join_left hIH2
        | app e1 e2 =>
            simp at htc
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
                rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
                  ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, hcases⟩
                have hLapp : ∃ joined : TypeResult,
                    res.tagLog' = result2.tagLog' ++ (result1.tagLog' ++ joined.tagLog') := by
                  rcases hcases with
                    ⟨_, _, _, _, _, _, _, _, joined, _, _, _, _, _, _, _, _, hres⟩ |
                    ⟨_, _, _, _, _, _, _, _, joined, _, _, _, _, _, _, _, hres⟩
                  · exact ⟨joined, by rw [hres]⟩
                  · exact ⟨joined, by rw [hres]⟩
                obtain ⟨_joined, hLapp⟩ := hLapp
                have hL21 := hL.of_log_eq hLapp
                have htc2' : typecheck ctx e2 fuel'' = .ok result2 := by
                  simpa [typecheck] using htc2
                obtain ⟨tm2, hcanon2, h_laws2⟩ :=
                  typecheck_canonical_sub P tm ctx e2 fuel'' result2 hwf hb hsub hL21.left htc2'
                have hIH2 := IH fuel'' (by omega) tm P ctx e2 result2 hwf hb hsub hL21.left hrec htc2'
                have htc1' : typecheck (ctxAfter ctx result2) e1 fuel'' = .ok result1 := by
                  simpa [typecheck, ctxAfter] using htc1
                obtain ⟨tm1, hcanon1, h_laws1⟩ :=
                  typecheck_canonical_sub P tm2 (ctxAfter ctx result2) e1 fuel'' result1
                    hcanon2.2.2.1 hcanon2.2.1 h_laws2 hL21.right.left htc1'
                have hIH1 := IH fuel'' (by omega) tm2 P (ctxAfter ctx result2) e1 result1
                  hcanon2.2.2.1 hcanon2.2.1 h_laws2 hL21.right.left hIH2 htc1'
                have hext_tm2_tm1 : tm2 ⊑ tm1 := hcanon1.1
                have hctxTm1 : wfTagMeaningCtx tm1 (ctxAfter ctx result1) := hcanon1.2.2.1
                have hresTm1 : QTypRespectsTagMeaning tm1 result1.qualType := hcanon1.2.2.2
                have hargTm2 : QTypRespectsTagMeaning tm2 ⟨etyp2, p2, pred2⟩ := by
                  rw [← hqt2]
                  exact hcanon2.2.2.2
                have hargTm1 : QTypRespectsTagMeaning tm1 ⟨etyp2, p2, pred2⟩ :=
                  QTypRespectsTagMeaning_mono hext_tm2_tm1 hargTm2
                have hargTm1' : QTypRespectsTagMeaning tm1 ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ :=
                  QTypRespectsTagMeaning_transport_etyp_pred tm1 ⟨etyp2, p2, pred2⟩
                    ⟨etyp2, joinPoison ctx.pc p2, pred2⟩ hargTm1 rfl rfl
                have hbound1 : TagMeaningBounded tm1 result1.nextTag' := hcanon1.2.1
                have h_fn_closure :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List FnTClosure)
                      (results : List TypeResult),
                      result1.qualType.etyp = ETyp.arrow st1 st2 p tcls →
                      applyClosuresThreaded
                        (fun tcl cursor =>
                          applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel'')
                        tcls (result1.nextTag', result1.nextLoc') = .ok results →
                      (∀ r ∈ results, LogIn r.tagLog' P) →
                      ∀ r, r ∈ results → RecordsCover P r.tagEnv' := by
                  intro st1 st2 p p1 tcls results hetyp1 hthread hLall r hr
                  have hLr := hLall r hr
                  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
                      (applyOne := fun tcl cursor =>
                        applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel'')
                      (base := result1.nextTag')
                      (hmono := fun tcl cursor result hb happly =>
                        Nat.le_trans hb (applyFnTClosureAtCursor_nextTag_advance tcl ctx st1 st2 p p1
                          etyp2 p2 pred2 result1 result cursor fuel'' happly))
                      (hbase := Nat.le_refl _) (hthread := hthread) (hmem := hr) with
                    ⟨tcl, htcl_mem, cursor, hcursorTag, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                              cases hqt3 : result3.qualType with
                              | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    let bodyCtx : TypeContext := { ctx with
                                      pc := joinPoison p (joinPoison p1 ctx.pc),
                                      memEnv := result1.memEnv',
                                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                      tagEnv := result1.tagEnv', nextTag := cursor.1,
                                      nextLoc := cursor.2, regime := result1.regime',
                                      externRefAllowed := false,
                                      declaredExternRefs := result1.declared' }
                                    have hwf_body : wfTagMeaningCtx tm1 bodyCtx :=
                                      wfTagMeaningCtx_closure_body tm1 ctx result1 result1.qualType
                                        st1 st2 p tcls x body env x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                                        hctxTm1 hresTm1 hetyp1 htcl_mem hargTm1'
                                    have hb_body : TagMeaningBounded tm1 bodyCtx.nextTag :=
                                      hbound1.mono hcursorTag
                                    have htcBody' : typecheck bodyCtx body k = .ok result3 := by
                                      simpa [bodyCtx] using! htcBody
                                    exact IH k (by omega) tm1 P bodyCtx body result3
                                      hwf_body hb_body h_laws1 hLr hIH1 htcBody'
                  | extern id x retSpec effects capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
                      have happly_old :
                          applyFnTClosure
                            (.extern id x retSpec effects capturedEnv declaredArgQt captures)
                            st1 st2 p p1 etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyFnTClosure
                        unfold applyFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      exact records_applyFnExtern ctx st1 st2 p p1 etyp2 p2 pred2
                        rCursor r fuel'' id x retSpec effects capturedEnv declaredArgQt
                        happly_old hLr hIH1
                have h_pfn_closure :
                    ∀ (st1 st2 : Typ) (p p1 : Poison) (tcls : List PFnTClosure)
                      (results : List TypeResult),
                      result1.qualType.etyp = ETyp.parrow st1 st2 p tcls →
                      applyClosuresThreaded
                        (fun tcl cursor =>
                          applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel'')
                        tcls (result1.nextTag', result1.nextLoc') = .ok results →
                      (∀ r ∈ results, LogIn r.tagLog' P) →
                      ∀ r, r ∈ results → RecordsCover P r.tagEnv' := by
                  intro st1 st2 p p1 tcls results hetyp1 hthread hLall r hr
                  have hLr := hLall r hr
                  rcases applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound
                      (applyOne := fun tcl cursor =>
                        applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2 ctx result1 cursor fuel'')
                      (base := result1.nextTag')
                      (hmono := fun tcl cursor result hb happly =>
                        Nat.le_trans hb (applyPFnTClosureAtCursor_nextTag_advance tcl ctx st1 st2 p p1
                          etyp2 p2 pred2 result1 result cursor fuel'' happly))
                      (hbase := Nat.le_refl _) (hthread := hthread) (hmem := hr) with
                    ⟨tcl, htcl_mem, cursor, hcursorTag, happly⟩
                  cases tcl with
                  | regular x body env =>
                      cases fuel'' with
                      | zero => simp [applyPFnTClosureAtCursor] at happly
                      | succ k =>
                          simp only [applyPFnTClosureAtCursor, bind, Except.bind] at happly
                          split at happly
                          · exact absurd happly (Except.error_ne_ok _ _)
                          · next result3 htcBody =>
                            cases hqt3 : result3.qualType with
                            | mk etyp3 p3 pred3 =>
                                simp only [hqt3] at happly
                                split at happly
                                · simp at happly
                                · next _hsub =>
                                    simp only [pure, Except.pure] at happly
                                    cases happly
                                    let bodyCtx : TypeContext := { ctx with
                                      pc := joinPoison p (joinPoison ctx.pc p1),
                                      memEnv := result1.memEnv',
                                      varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured env) x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩,
                                      tagEnv := result1.tagEnv', nextTag := cursor.1,
                                      pureCtx := true,
                                      nextLoc := cursor.2, regime := result1.regime',
                                      externRefAllowed := false,
                                      declaredExternRefs := result1.declared' }
                                    have hwf_body : wfTagMeaningCtx tm1 bodyCtx :=
                                      wfTagMeaningCtx_pclosure_body tm1 ctx result1 result1.qualType
                                        st1 st2 p tcls x body env x
                                        ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
                                        hctxTm1 hresTm1 hetyp1 htcl_mem hargTm1'
                                    have hb_body : TagMeaningBounded tm1 bodyCtx.nextTag :=
                                      hbound1.mono hcursorTag
                                    have htcBody' :
                                        typecheck bodyCtx (PExpr.toExpr body) k = .ok result3 := by
                                      simpa [bodyCtx] using! htcBody
                                    exact IH k (by omega) tm1 P bodyCtx (PExpr.toExpr body) result3
                                      hwf_body hb_body h_laws1 hLr hIH1 htcBody'
                  | extern id x retSpec capturedEnv declaredArgQt captures =>
                      let rCursor : TypeResult :=
                        { result1 with nextTag' := cursor.1, nextLoc' := cursor.2 }
                      have happly_old :
                          applyPFnTClosure
                            (.extern id x retSpec capturedEnv declaredArgQt captures)
                            st1 st2 p p1 etyp2 p2 pred2 ctx rCursor fuel'' = .ok r := by
                        unfold applyPFnTClosure
                        unfold applyPFnTClosureAtCursor at happly
                        simpa [rCursor] using happly
                      exact records_applyPFnExtern ctx st1 st2 p p1 etyp2 p2 pred2
                        rCursor r fuel'' id x retSpec capturedEnv declaredArgQt
                        happly_old hLr hIH1
                rcases hcases with
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, hetyp1, _hp1, _hpure, _hne, _hsub, hmap, hresults, h_join, rfl⟩ |
                  ⟨st1, st2, p, p1, tcls, results, first, rest, res, hetyp1, _hp1, _hne, _hsub, hmap, hresults, h_join, rfl⟩
                · subst hresults
                  have hLall := hL.right.right.of_join h_join
                  exact joinTypeResults_records ctx first rest res h_join
                    (h_fn_closure st1 st2 p p1 tcls (first :: rest) hetyp1 hmap hLall
                      first (List.mem_cons_self ..))
                · subst hresults
                  have hLall := hL.right.right.of_join h_join
                  exact joinTypeResults_records ctx first rest res h_join
                    (h_pfn_closure st1 st2 p p1 tcls (first :: rest) hetyp1 hmap hLall
                      first (List.mem_cons_self ..))

/-! ### The records half of `TypingKeepsFootprintCtx` -/

theorem typingKeepsRecordsCover : TypingKeepsRecordsCover := by
  intro ctx e fuel res tm tm' htc hwfTm hb htb _hwf _hext hw hrec
  have htc' : typecheck ctx e fuel = .ok res := htc
  obtain ⟨hsubP, hlogP, hwithinP⟩ := typecheck_programTable tm ctx e fuel res hb htc'
  have hfresh := typecheck_tagLog_fresh ctx e fuel res htc'
  have hrecP : RecordsCover (programTable tm res.tagLog') ctx.tagEnv := by
    intro k tv d hk hd l hl
    have hlt : k < ctx.nextTag := htb.1 k (by rw [hk]; simp)
    rcases hwithinP k d hd with hold | ⟨a, ha, hak, _⟩
    · exact hrec k tv d hk hold l hl
    · have := (hfresh.1 a ha).1
      rw [hak] at this
      exact absurd hlt (Nat.not_lt.mpr this)
  have h := typecheck_preserves_recordsCover fuel tm (programTable tm res.tagLog') ctx e res
    hwfTm hb hsubP hlogP hrecP htc'
  exact RecordsCover.anti h (typecheck_table_sub_programTable hb htc' hw)
