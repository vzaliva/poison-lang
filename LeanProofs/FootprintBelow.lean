/-
  FootprintBelow.lean - The footprints of the guards a typing run allocates lie
  below the run's final `nextLoc`.

  The dependency extraction only returns reference locations of the
  environment it reads, at any closure depth (`extract_bounded`). Every guard a
  run allocates captures an environment bounded by the `nextLoc` of the run at
  that point: the context's variables at an extern declaration, or a closure's
  captured environment with the actual argument at an extern application. So
  the footprints of the run's allocations lie below its final `nextLoc'`
  (`typecheck_log_footprints_below`), and `FootprintBelow` passes from the
  starting table to every table that adds allocations of the run
  (`typingKeepsFootprintBelow`). With `typingKeepsRecordsCover` this gives
  `TypingKeepsFootprintCtx`.
-/
import LeanProofs.FootprintTyping

open List
open Std

/-! ### The bound of an environment -/

private def EnvBd (env : VarTypeEnv) (nl : Loc) : Prop :=
  (∀ x qt, env.lookup x = some qt → etypRefLocsBounded qt.etyp nl) ∧
  (∀ x qt, env.lookup x = some qt → etypClosuresCapturedRefLocsBounded qt.etyp nl)

private theorem EnvBd.mono {env : VarTypeEnv} {nl nl' : Loc} (h : EnvBd env nl) (hle : nl ≤ nl') :
    EnvBd env nl' :=
  ⟨fun x qt hx => etypRefLocsBounded_mono (h.1 x qt hx) hle,
   fun x qt hx => etypClosuresCapturedRefLocsBounded_mono (h.2 x qt hx) hle⟩

private theorem EnvBd.of_wf {ctx : TypeContext} (h : wfTypeContext ctx) :
    EnvBd ctx.varEnv ctx.nextLoc :=
  ⟨h.2.1, h.2.2⟩

private theorem EnvBd_ofCaptured {cap : CapturedVarEnv} {nl : Loc}
    (h : CapturedEnvRefLocsFullBounded cap nl) : EnvBd (VarTypeEnv.ofCaptured cap) nl :=
  ⟨varEnvRefLocsBounded_ofCaptured (capturedEnvRefLocsBounded_of_fullBounded_refLocs h),
   varEnvClosuresCapturedRefLocsBounded_ofCaptured h⟩

private theorem EnvBd_ofToCaptured {env : VarTypeEnv} {nl : Loc} (h : EnvBd env nl) :
    EnvBd (VarTypeEnv.ofCaptured (VarTypeEnv.toCaptured env)) nl := by
  have hl : ∀ x qt, (VarTypeEnv.ofCaptured (VarTypeEnv.toCaptured env)).lookup x = some qt →
      env.lookup x = some qt := fun x qt hx =>
    VarTypeEnv_lookup_of_toCaptured_lookup env x qt (list_lookup_of_ofCaptured_lookup _ x qt hx)
  exact ⟨fun x qt hx => h.1 x qt (hl x qt hx), fun x qt hx => h.2 x qt (hl x qt hx)⟩

/-! ### Sets of locations -/

private theorem contains_union {l : Loc} {s t : LocSet} :
    (LocSet.union s t).contains l = true ↔ s.contains l = true ∨ t.contains l = true := by
  simp only [ExtTreeSet.contains_iff_mem]
  simp [LocSet.union, ExtTreeSet.mem_union_iff]

private theorem foldlM_inv {α : Type} (l : List α) (F : LocSet → α → Except String LocSet)
    (P : Loc → Prop) (init r : LocSet)
    (hinit : ∀ x, init.contains x = true → P x)
    (hstep : ∀ acc a r, a ∈ l → (∀ x, acc.contains x = true → P x) → F acc a = .ok r →
      ∀ x, r.contains x = true → P x) :
    l.foldlM F init = .ok r → ∀ x, r.contains x = true → P x := by
  induction l generalizing init with
  | nil =>
      intro h
      simp [List.foldlM_nil, pure, Except.pure] at h
      subst h
      exact hinit
  | cons a rest ih =>
      intro h
      simp only [List.foldlM_cons] at h
      cases hF : F init a with
      | error e => simp [hF, bind, Except.bind] at h
      | ok r1 =>
          simp only [hF, bind, Except.bind] at h
          exact ih r1 (hstep init a r1 (List.mem_cons_self ..) hinit hF)
            (fun acc b r hb => hstep acc b r (List.mem_cons_of_mem _ hb)) h

private theorem bind_union_inv {X : Except String LocSet} {acc r : LocSet} {P : Loc → Prop}
    (hacc : ∀ x, acc.contains x = true → P x)
    (hX : ∀ d, X = .ok d → ∀ x, d.contains x = true → P x) :
    (do let d ← X; pure (LocSet.union acc d) : Except String LocSet) = .ok r →
      ∀ x, r.contains x = true → P x := by
  cases hXe : X with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok d =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      intro hr x hx
      subst hr
      rcases contains_union.mp hx with h | h
      · exact hacc x h
      · exact hX d hXe x h

private theorem bind2_union_inv {X Y : Except String LocSet} {r : LocSet} {P : Loc → Prop}
    (hX : ∀ d, X = .ok d → ∀ x, d.contains x = true → P x)
    (hY : ∀ d, Y = .ok d → ∀ x, d.contains x = true → P x) :
    (do let d1 ← X; let d2 ← Y; pure (LocSet.union d1 d2) : Except String LocSet) = .ok r →
      ∀ x, r.contains x = true → P x := by
  cases hXe : X with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok d1 =>
      cases hYe : Y with
      | error e => intro h; simp [bind, Except.bind] at h
      | ok d2 =>
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
          intro hr x hx
          subst hr
          rcases contains_union.mp hx with h | h
          · exact hX d1 hXe x h
          · exact hY d2 hYe x h

private theorem bind3_union_inv {X Y Z : Except String LocSet} {r : LocSet} {P : Loc → Prop}
    (hX : ∀ d, X = .ok d → ∀ x, d.contains x = true → P x)
    (hY : ∀ d, Y = .ok d → ∀ x, d.contains x = true → P x)
    (hZ : ∀ d, Z = .ok d → ∀ x, d.contains x = true → P x) :
    (do let d1 ← X; let d2 ← Y; let d3 ← Z;
        pure (LocSet.union (LocSet.union d1 d2) d3) : Except String LocSet) = .ok r →
      ∀ x, r.contains x = true → P x := by
  cases hXe : X with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok d1 =>
      cases hYe : Y with
      | error e => intro h; simp [bind, Except.bind] at h
      | ok d2 =>
          cases hZe : Z with
          | error e => intro h; simp [bind, Except.bind] at h
          | ok d3 =>
              simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
              intro hr x hx
              subst hr
              rcases contains_union.mp hx with h | h
              · rcases contains_union.mp h with h | h
                · exact hX d1 hXe x h
                · exact hY d2 hYe x h
              · exact hZ d3 hZe x h

/-! ### The bridge: an extraction only returns locations of the environment it reads -/

private theorem extract_bounded :
    ∀ (f : Nat) (pe : PExpr) (bound : List Name) (env : VarTypeEnv) (nl : Loc) (deps : Deps),
      EnvBd env nl →
      extractDepsFromPred.extractDepsFromPExpr pe bound env f = .ok deps →
      ∀ l, deps.contains l = true → l < nl := by
  intro f
  induction f with
  | zero =>
      intro pe bound env nl deps _ h
      simp [extractDepsFromPred.extractDepsFromPExpr, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
      intro pe bound env nl deps hE h
      cases pe with
      | var y =>
          revert h
          simp only [extractDepsFromPred.extractDepsFromPExpr]
          split
          · intro h
            simp [pure, Except.pure] at h
            subst h
            intro l hl
            simp [LocSet.empty] at hl
          · split
            · rename_i qt hget
              have hlk : env.lookup y = some qt := by simpa [VarTypeEnv.lookup] using hget
              split
              · rename_i ls hty
                intro h
                simp [pure, Except.pure] at h
                subst h
                intro l hl
                have hb := hE.1 y qt hlk
                rw [hty] at hb
                exact hb l hl
              · rename_i tcls hty
                intro h
                have hcl := hE.2 y qt hlk
                rw [hty] at hcl
                refine foldlM_inv tcls _ (fun l => l < nl) _ _ ?_ ?_ h
                · intro x hx
                  simp [LocSet.empty] at hx
                · intro acc tcl r hmem hacc hx
                  cases tcl with
                  | regular argName body varEnv' =>
                      have hcap := hcl _ hmem
                      revert hx
                      simp only
                      intro hx
                      exact bind_union_inv hacc
                        (fun d hd => ih _ _ _ _ _ (EnvBd_ofCaptured hcap) hd) hx
                  | extern _eid argName retSpec capEnv _argQt captures =>
                      have hcap := hcl _ hmem
                      revert hx
                      simp only
                      split
                      · intro hx
                        simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hx
                      · intro hx
                        refine bind_union_inv hacc (fun d hd => ?_) hx
                        refine foldlM_inv _ _ (fun l => l < nl) _ _ ?_ ?_ hd
                        · intro x hx
                          simp [LocSet.empty] at hx
                        · intro dacc x r _ hdacc hy
                          exact bind_union_inv hdacc
                            (fun d2 hd2 => ih _ _ _ _ _ (EnvBd_ofCaptured hcap) hd2) hy
              · intro h
                simp [throw, throwThe, MonadExceptOf.throw] at h
              · intro h
                simp [pure, Except.pure] at h
                subst h
                intro l hl
                simp [LocSet.empty] at hl
            · intro h
              simp [throw, throwThe, MonadExceptOf.throw] at h
      | deref p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact ih p bound env nl deps hE h
      | unaryop o p =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact ih p bound env nl deps hE h
      | op p o q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact bind2_union_inv (fun d hd => ih _ _ _ _ _ hE hd)
            (fun d hd => ih _ _ _ _ _ hE hd) h
      | app p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact bind2_union_inv (fun d hd => ih _ _ _ _ _ hE hd)
            (fun d hd => ih _ _ _ _ _ hE hd) h
      | vlet y p q =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact bind2_union_inv (fun d hd => ih _ _ _ _ _ hE hd)
            (fun d hd => ih _ _ _ _ _ hE hd) h
      | ite p q r =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          exact bind3_union_inv (fun d hd => ih _ _ _ _ _ hE hd)
            (fun d hd => ih _ _ _ _ _ hE hd) (fun d hd => ih _ _ _ _ _ hE hd) h
      | _ =>
          simp only [extractDepsFromPred.extractDepsFromPExpr] at h
          simp [pure, Except.pure] at h
          subst h
          intro l hl
          simp [LocSet.empty] at hl

/-! ### Allocation sites -/

/-- Every guard of the log has its footprint below `nl`. -/
private def LogFootBelow (log : List TagAlloc) (nl : Loc) : Prop :=
  ∀ a ∈ log, ∀ l, InFootprint a.tag a.desc l → l < nl

private theorem LogFootBelow.mono {log : List TagAlloc} {nl nl' : Loc} (h : LogFootBelow log nl)
    (hle : nl ≤ nl') : LogFootBelow log nl' :=
  fun a ha l hl => Nat.lt_of_lt_of_le (h a ha l hl) hle

private theorem LogFootBelow.nil (nl : Loc) : LogFootBelow [] nl := by
  intro a ha; cases ha

private theorem LogFootBelow.append {log₁ log₂ : List TagAlloc} {nl₁ nl₂ nl : Loc}
    (h₁ : LogFootBelow log₁ nl₁) (h₂ : LogFootBelow log₂ nl₂) (h₁₂ : nl₁ ≤ nl) (h₂₃ : nl₂ ≤ nl) :
    LogFootBelow (log₁ ++ log₂) nl := by
  intro a ha l hl
  rcases List.mem_append.mp ha with ha | ha
  · exact Nat.lt_of_lt_of_le (h₁ a ha l hl) h₁₂
  · exact Nat.lt_of_lt_of_le (h₂ a ha l hl) h₂₃

private theorem mem_externTagLog_capEnv {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {m : ExtTreeMap TagIndex Tag} {a : TagAlloc} (ha : a ∈ externTagLog preds env m) :
    a.capEnv = VarTypeEnv.toCaptured env := by
  simp only [externTagLog, List.mem_filterMap] at ha
  obtain ⟨pred, _hpred, hsome⟩ := ha
  cases pred with
  | guardClosure idx arg body =>
      simp only at hsome
      split at hsome
      · cases hsome; rfl
      · cases hsome
  | guardOnly _ => cases hsome
  | noPred => cases hsome

private theorem InFootprint_below_of_capEnv {k : Tag} {arg : Name} {body : PExpr}
    {cap : CapturedVarEnv} {nl : Loc} (hE : EnvBd (VarTypeEnv.ofCaptured cap) nl) :
    ∀ l, InFootprint k { argName := arg, body := body, capEnv := cap } l → l < nl := by
  intro l ⟨fuel, deps, hx, hl⟩
  have hx' : extractDepsFromPred.extractDepsFromPExpr body [arg] (VarTypeEnv.ofCaptured cap) fuel
      = .ok deps := by simpa [extractDepsFromPred] using hx
  exact extract_bounded fuel body [arg] _ nl deps hE hx' l hl

/-- Every footprint location of a descriptor whose captured environment is
    reference-bounded by `nl`, at every closure depth, is below `nl`. -/
theorem InFootprint_lt_of_capEnv_bounded {k : Tag} {d : GuardDesc} {nl : Loc}
    (h : CapturedEnvRefLocsFullBounded d.capEnv nl) : ∀ l, InFootprint k d l → l < nl := by
  rcases d with ⟨arg, body, cap⟩
  exact InFootprint_below_of_capEnv (EnvBd_ofCaptured h)

private theorem externTagLog_below (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (mapping : ExtTreeMap TagIndex Tag) (nl : Loc) (hE : EnvBd env nl) :
    LogFootBelow (externTagLog preds env mapping) nl := by
  intro a ha l hl
  have hcap := mem_externTagLog_capEnv ha
  have hE' : EnvBd (VarTypeEnv.ofCaptured a.capEnv) nl := by
    rw [hcap]; exact EnvBd_ofToCaptured hE
  exact InFootprint_below_of_capEnv (k := a.tag) (arg := a.argName) (body := a.body)
    (cap := a.capEnv) hE' l hl

/-! ### Closure applications -/

private theorem applyFnTClosureAtCursor_extern_log
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (effects : List Effect)
    (capturedEnv : CapturedVarEnv) (declaredArgQt : QTyp) (captures : List Capture)
    (st1 st2 : Typ) (p p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc) (k : Nat) (r : TypeResult)
    (h : applyFnTClosureAtCursor
      (FnTClosure.extern id x retSpec effects capturedEnv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor (k + 1) = .ok r) :
    ∃ preds mapping, r.tagLog' = externTagLog preds
      (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) mapping := by
  unfold applyFnTClosureAtCursor at h
  simp only [bind, Except.bind, pure, Except.pure, resolveArgCondQTyp] at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, reduceCtorEq] at h)
  all_goals (cases h)
  all_goals (try (exfalso; have hthrow := ‹throw _ = Except.ok _›; cases hthrow))
  all_goals (try (rename_i heqLast _ _ _; split at heqLast <;>
    (try simp only [Except.ok.injEq, reduceCtorEq] at heqLast); (try subst heqLast)))
  all_goals exact ⟨_, _, rfl⟩

private theorem applyPFnTClosureAtCursor_extern_log
    (id : ExternId) (x : Name) (retSpec : ExternReturn)
    (capturedEnv : CapturedVarEnv) (declaredArgQt : QTyp) (captures : List Capture)
    (st1 st2 : Typ) (p p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc) (k : Nat) (r : TypeResult)
    (h : applyPFnTClosureAtCursor
      (PFnTClosure.extern id x retSpec capturedEnv declaredArgQt captures)
      st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor (k + 1) = .ok r) :
    ∃ preds mapping, r.tagLog' = externTagLog preds
      (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
        ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) mapping := by
  unfold applyPFnTClosureAtCursor at h
  simp only [bind, Except.bind, pure, Except.pure, resolveArgCondQTyp] at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, reduceCtorEq] at h)
  all_goals (cases h)
  all_goals (try (exfalso; have hthrow := ‹throw _ = Except.ok _›; cases hthrow))
  all_goals (try (rename_i heqLast; split at heqLast <;>
    (try simp only [Except.ok.injEq, reduceCtorEq] at heqLast); (try subst heqLast)))
  all_goals first | exact ⟨_, _, rfl⟩ | exact ⟨[], {}, rfl⟩

private theorem applyFnTClosureAtCursor_below
    (tcl : FnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (r1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat) (r : TypeResult)
    (IH : ∀ m < fuel, ∀ (ctx' : TypeContext) (e : Expr) (res' : TypeResult),
      typecheckExpr ctx' e m = .ok res' → wfTypeContext ctx' →
        LogFootBelow res'.tagLog' res'.nextLoc')
    (hr1 : wfTypeResult r1) (hcursor : r1.nextLoc' ≤ cursor.2)
    (hcap : match tcl with
      | .regular _ _ env => CapturedEnvRefLocsFullBounded env r1.nextLoc'
      | .extern _ _ _ _ env _ _ => CapturedEnvRefLocsFullBounded env r1.nextLoc')
    (hargRL : etypRefLocsBounded argEtyp r1.nextLoc')
    (hargCL : etypClosuresCapturedRefLocsBounded argEtyp r1.nextLoc')
    (h : applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 cursor fuel
      = .ok r) :
    LogFootBelow r.tagLog' r.nextLoc' := by
  have hmono : r1.nextLoc' ≤ r.nextLoc' :=
    applyFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1 argEtyp argPoison argPred r1 r
      cursor fuel hcursor (fun m _ e c r htc => typecheck_nextLoc_mono c e m r htc) h
  cases fuel with
  | zero => simp [applyFnTClosureAtCursor, throw, throwThe, MonadExceptOf.throw] at h
  | succ k =>
    cases tcl with
    | regular x body env =>
        have hcap' : CapturedEnvRefLocsFullBounded env r1.nextLoc' := hcap
        unfold applyFnTClosureAtCursor at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i v hv
          have hlog := IH k (Nat.lt_succ_self k) _ _ _ hv
          have hlog' : LogFootBelow v.tagLog' v.nextLoc' := hlog
            ⟨fun l hl => Nat.lt_of_lt_of_le (hr1 l hl) hcursor,
             varEnvRefLocsBounded_update
               (varEnvRefLocsBounded_mono
                 (varEnvRefLocsBounded_ofCaptured
                   (capturedEnvRefLocsBounded_of_fullBounded_refLocs hcap')) hcursor)
               (etypRefLocsBounded_mono hargRL hcursor),
             varEnvClosuresCapturedRefLocsBounded_update
               (varEnvClosuresCapturedRefLocsBounded_mono
                 (varEnvClosuresCapturedRefLocsBounded_ofCaptured hcap') hcursor)
               (etypClosuresCapturedRefLocsBounded_mono hargCL hcursor)⟩
          repeat' split at h
          all_goals (try simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h)
          all_goals (subst h; exact hlog')
    | extern id x retSpec effects capturedEnv declaredArgQt captures =>
        have hcap' : CapturedEnvRefLocsFullBounded capturedEnv r1.nextLoc' := hcap
        obtain ⟨preds, mapping, hlog⟩ := applyFnTClosureAtCursor_extern_log id x retSpec effects
          capturedEnv declaredArgQt captures st1 st2 p p1 argEtyp argPoison argPred ctx r1
          cursor k r h
        have hE : EnvBd (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) r1.nextLoc' :=
          ⟨varEnvRefLocsBounded_update
             (varEnvRefLocsBounded_ofCaptured
               (capturedEnvRefLocsBounded_of_fullBounded_refLocs hcap')) hargRL,
           varEnvClosuresCapturedRefLocsBounded_update
             (varEnvClosuresCapturedRefLocsBounded_ofCaptured hcap') hargCL⟩
        rw [hlog]
        exact (externTagLog_below preds _ mapping _ hE).mono hmono

private theorem applyPFnTClosureAtCursor_below
    (tcl : PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (r1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat) (r : TypeResult)
    (IH : ∀ m < fuel, ∀ (ctx' : TypeContext) (e : Expr) (res' : TypeResult),
      typecheckExpr ctx' e m = .ok res' → wfTypeContext ctx' →
        LogFootBelow res'.tagLog' res'.nextLoc')
    (hr1 : wfTypeResult r1) (hcursor : r1.nextLoc' ≤ cursor.2)
    (hcap : match tcl with
      | .regular _ _ env => CapturedEnvRefLocsFullBounded env r1.nextLoc'
      | .extern _ _ _ env _ _ => CapturedEnvRefLocsFullBounded env r1.nextLoc')
    (hargRL : etypRefLocsBounded argEtyp r1.nextLoc')
    (hargCL : etypClosuresCapturedRefLocsBounded argEtyp r1.nextLoc')
    (h : applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 cursor fuel
      = .ok r) :
    LogFootBelow r.tagLog' r.nextLoc' := by
  have hmono : r1.nextLoc' ≤ r.nextLoc' :=
    applyPFnTClosureAtCursor_nextLoc_mono tcl ctx st1 st2 p p1 argEtyp argPoison argPred r1 r
      cursor fuel hcursor (fun m _ e c r htc => typecheck_nextLoc_mono c e m r htc) h
  cases fuel with
  | zero => simp [applyPFnTClosureAtCursor, throw, throwThe, MonadExceptOf.throw] at h
  | succ k =>
    cases tcl with
    | regular x body env =>
        have hcap' : CapturedEnvRefLocsFullBounded env r1.nextLoc' := hcap
        unfold applyPFnTClosureAtCursor at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i v hv
          have hlog := IH k (Nat.lt_succ_self k) _ _ _ hv
          have hlog' : LogFootBelow v.tagLog' v.nextLoc' := hlog
            ⟨fun l hl => Nat.lt_of_lt_of_le (hr1 l hl) hcursor,
             varEnvRefLocsBounded_update
               (varEnvRefLocsBounded_mono
                 (varEnvRefLocsBounded_ofCaptured
                   (capturedEnvRefLocsBounded_of_fullBounded_refLocs hcap')) hcursor)
               (etypRefLocsBounded_mono hargRL hcursor),
             varEnvClosuresCapturedRefLocsBounded_update
               (varEnvClosuresCapturedRefLocsBounded_mono
                 (varEnvClosuresCapturedRefLocsBounded_ofCaptured hcap') hcursor)
               (etypClosuresCapturedRefLocsBounded_mono hargCL hcursor)⟩
          repeat' split at h
          all_goals (try simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h)
          all_goals (subst h; exact hlog')
    | extern id x retSpec capturedEnv declaredArgQt captures =>
        have hcap' : CapturedEnvRefLocsFullBounded capturedEnv r1.nextLoc' := hcap
        obtain ⟨preds, mapping, hlog⟩ := applyPFnTClosureAtCursor_extern_log id x retSpec
          capturedEnv declaredArgQt captures st1 st2 p p1 argEtyp argPoison argPred ctx r1
          cursor k r h
        have hE : EnvBd (VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
            ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩) r1.nextLoc' :=
          ⟨varEnvRefLocsBounded_update
             (varEnvRefLocsBounded_ofCaptured
               (capturedEnvRefLocsBounded_of_fullBounded_refLocs hcap')) hargRL,
           varEnvClosuresCapturedRefLocsBounded_update
             (varEnvClosuresCapturedRefLocsBounded_ofCaptured hcap') hargCL⟩
        rw [hlog]
        exact (externTagLog_below preds _ mapping _ hE).mono hmono

/-- Every result of a threaded closure application has its log below its own counter, and
    its counter is at least the base. -/
private theorem threaded_below {α : Type}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult) (base : Loc)
    {xs : List α} {cursor : Tag × Loc} {results : List TypeResult}
    (hone : ∀ item, item ∈ xs → ∀ cursor' r, base ≤ cursor'.2 → applyOne item cursor' = .ok r →
      LogFootBelow r.tagLog' r.nextLoc')
    (hmono : ∀ item cursor' result, base ≤ cursor'.2 → applyOne item cursor' = .ok result →
      base ≤ result.nextLoc')
    (hbase : base ≤ cursor.2)
    (hthread : applyClosuresThreaded applyOne xs cursor = .ok results) :
    ∀ y ∈ results, LogFootBelow y.tagLog' y.nextLoc' ∧ base ≤ y.nextLoc' := by
  intro y hy
  obtain ⟨x, hx, cursor', hc', happ⟩ :=
    applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound applyOne base
      (fun item cursor' result hb happ => hmono item cursor' result hb happ) hbase hthread hy
  exact ⟨hone x hx cursor' y hc' happ, hmono x cursor' y hc' happ⟩

/-! ### Composition of sub-runs -/

private def LogBelowStmt (m : Nat) : Prop :=
  ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
    typecheckExpr ctx e m = .ok res → wfTypeContext ctx → LogFootBelow res.tagLog' res.nextLoc'

private theorem wf_of_parts {c1 c : TypeContext} (hwf : wfTypeContext c1)
    (hmem : ∀ l, c.memEnv.contains l → l < c.nextLoc) (hv : c.varEnv = c1.varEnv)
    (hle : c1.nextLoc ≤ c.nextLoc) : wfTypeContext c :=
  ⟨hmem, by rw [hv]; exact varEnvRefLocsBounded_mono hwf.2.1 hle,
    by rw [hv]; exact varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hle⟩

private theorem next_wf {m : Nat} {c1 c2 : TypeContext} {e1 : Expr} {r1 : TypeResult}
    (hwf : wfTypeContext c1) (h1 : typecheckExpr c1 e1 m = .ok r1)
    (hmem : c2.memEnv = r1.memEnv') (hnl : c2.nextLoc = r1.nextLoc')
    (hv : c2.varEnv = c1.varEnv) : wfTypeContext c2 := by
  have hr := typecheckExpr_preserves_wfTypeResult c1 e1 m r1 hwf h1
  have hmono := typecheck_nextLoc_mono c1 e1 m r1 h1
  refine wf_of_parts hwf ?_ hv (by rw [hnl]; exact hmono)
  rw [hmem, hnl]; exact hr

private theorem seq_below {m : Nat} (IH : LogBelowStmt m)
    {c1 c2 : TypeContext} {e1 e2 : Expr} {r1 r2 : TypeResult}
    (hwf : wfTypeContext c1) (h1 : typecheckExpr c1 e1 m = .ok r1)
    (h2 : typecheckExpr c2 e2 m = .ok r2)
    (hwf2 : wfTypeContext c2) (hnl : c2.nextLoc = r1.nextLoc') :
    LogFootBelow (r1.tagLog' ++ r2.tagLog') r2.nextLoc' := by
  have m2 := typecheck_nextLoc_mono c2 e2 m r2 h2
  rw [hnl] at m2
  exact LogFootBelow.append (IH _ _ _ h1 hwf) (IH _ _ _ h2 hwf2) m2 (Nat.le_refl _)

private theorem seq3_below {m : Nat} (IH : LogBelowStmt m)
    {c1 c2 c3 : TypeContext} {e1 e2 e3 : Expr} {r1 r2 r3 : TypeResult}
    (hwf : wfTypeContext c1) (h1 : typecheckExpr c1 e1 m = .ok r1)
    (h2 : typecheckExpr c2 e2 m = .ok r2) (h3 : typecheckExpr c3 e3 m = .ok r3)
    (hmem2 : c2.memEnv = r1.memEnv') (hnl2 : c2.nextLoc = r1.nextLoc')
    (hv2 : c2.varEnv = c1.varEnv)
    (hmem3 : c3.memEnv = r1.memEnv') (hnl3 : c3.nextLoc = r2.nextLoc')
    (hv3 : c3.varEnv = c1.varEnv) :
    LogFootBelow (r1.tagLog' ++ r2.tagLog' ++ r3.tagLog') (max r2.nextLoc' r3.nextLoc') := by
  have hwf2 := next_wf hwf h1 hmem2 hnl2 hv2
  have hr1 := typecheckExpr_preserves_wfTypeResult c1 e1 m r1 hwf h1
  have m1 := typecheck_nextLoc_mono c1 e1 m r1 h1
  have m2 := typecheck_nextLoc_mono c2 e2 m r2 h2
  rw [hnl2] at m2
  have hwf3 : wfTypeContext c3 :=
    wf_of_parts hwf
      (by rw [hmem3, hnl3]; intro l hl; exact Nat.lt_of_lt_of_le (hr1 l hl) m2) hv3
      (by rw [hnl3]; exact Nat.le_trans m1 m2)
  exact LogFootBelow.append
    (LogFootBelow.append (IH _ _ _ h1 hwf) (IH _ _ _ h2 hwf2) m2 (Nat.le_refl _))
    (IH _ _ _ h3 hwf3) (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem matched_below {m : Nat} (IH : LogBelowStmt m)
    {ctx c2 c3 : TypeContext} {e2 e3 : Expr} {r1 r2 r3 : TypeResult}
    (hwf : wfTypeContext ctx) (hpure : LogFootBelow r1.tagLog' ctx.nextLoc)
    (h2 : typecheckExpr c2 e2 m = .ok r2) (h3 : typecheckExpr c3 e3 m = .ok r3)
    (hmem2 : c2.memEnv = ctx.memEnv) (hnl2 : c2.nextLoc = ctx.nextLoc)
    (hv2 : c2.varEnv = ctx.varEnv)
    (hmem3 : c3.memEnv = ctx.memEnv) (hnl3 : c3.nextLoc = r2.nextLoc')
    (hv3 : c3.varEnv = ctx.varEnv) :
    LogFootBelow (r1.tagLog' ++ r2.tagLog' ++ r3.tagLog') (max r2.nextLoc' r3.nextLoc') := by
  have hwf2 : wfTypeContext c2 :=
    wf_of_parts hwf (by rw [hmem2, hnl2]; exact hwf.1) hv2 (Nat.le_of_eq hnl2.symm)
  have m2 := typecheck_nextLoc_mono c2 e2 m r2 h2
  rw [hnl2] at m2
  have hwf3 : wfTypeContext c3 :=
    wf_of_parts hwf
      (by rw [hmem3, hnl3]; intro l hl; exact Nat.lt_of_lt_of_le (hwf.1 l hl) m2) hv3
      (by rw [hnl3]; exact m2)
  exact LogFootBelow.append
    (LogFootBelow.append hpure (IH _ _ _ h2 hwf2) m2 (Nat.le_refl _))
    (IH _ _ _ h3 hwf3) (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem foldl_max_ge (l : List Loc) (n : Nat) :
    n ≤ l.foldl (fun acc x => max acc (x + 1)) n := by
  induction l generalizing n with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih (max n (x + 1)))

private theorem fold_ge (ls : LocSet) (n : Nat) :
    n ≤ LocSet.fold ls n (fun acc l => max acc (l + 1)) := by
  unfold LocSet.fold
  rw [ExtTreeSet.foldl_eq_foldl_toList]
  exact foldl_max_ge _ _

/-! ### Leaves without allocation -/

local macro "leaf_log" h:ident : tactic => `(tactic| (
  (try simp only [bind, Except.bind, pure, Except.pure] at $h:ident)
  repeat' split at $h:ident
  all_goals (try simp only [bind, Except.bind, pure, Except.pure, MonadExceptOf.throw, throwThe,
    Except.ok.injEq, reduceCtorEq] at $h:ident)
  all_goals (first | (subst $h:ident; rfl) | (cases $h:ident; rfl) | (cases $h:ident) | skip)))

private theorem typecheckVar_tagLog' (ctx : TypeContext) (x : Name) (res : TypeResult)
    (h : typecheckVar ctx x = .ok res) : res.tagLog' = [] := by
  unfold typecheckVar at h
  leaf_log h

private theorem typecheckExternFn_tagLog' (ctx : TypeContext) id arg argTyp argPoison argPred
    retSpec effects captures fuel (res : TypeResult)
    (h : typecheckExternFn ctx id arg argTyp argPoison argPred retSpec effects captures fuel
      = .ok res) : res.tagLog' = [] := by
  unfold typecheckExternFn at h
  leaf_log h

private theorem typecheckExternPfn_tagLog' (ctx : TypeContext) id arg argTyp argPoison argPred
    retSpec captures fuel (res : TypeResult)
    (h : typecheckExternPfn ctx id arg argTyp argPoison argPred retSpec captures fuel
      = .ok res) : res.tagLog' = [] := by
  unfold typecheckExternPfn at h
  leaf_log h

private theorem typecheckExternRef_tagLog' (ctx : TypeContext) id rp rpred cp cpred
    (res : TypeResult) (h : typecheckExternRef ctx id rp rpred cp cpred = .ok res) :
    res.tagLog' = [] := by
  unfold typecheckExternRef at h
  leaf_log h

private theorem typecheckFn_tagLog' (ctx : TypeContext) x st1 body st2 (res : TypeResult)
    (h : typecheckFn ctx x st1 body st2 = .ok res) : res.tagLog' = [] := by
  unfold typecheckFn at h
  leaf_log h

private theorem typecheckPfn_tagLog' (ctx : TypeContext) x st1 body st2 (res : TypeResult)
    (h : typecheckPfn ctx x st1 body st2 = .ok res) : res.tagLog' = [] := by
  unfold typecheckPfn at h
  leaf_log h

/-! ### The condition of a matched conditional is typed in a pure context -/

private abbrev PureE (e : Expr) : Prop := ∃ pe, Expr.toPExpr? e = some pe

private theorem PureE_unaryop {o : UnaryOp} {a : Expr} (h : PureE (.unaryop o a)) : PureE a := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 => exact ⟨p1, h1⟩

private theorem PureE_deref {a : Expr} (h : PureE (.deref a)) : PureE a := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 => exact ⟨p1, h1⟩

private theorem PureE_op {a b : Expr} {o : Op} (h : PureE (.op a o b)) : PureE a ∧ PureE b := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 =>
    cases h2 : Expr.toPExpr? b with
    | none => simp [h1, h2] at hpe
    | some p2 => exact ⟨⟨p1, h1⟩, ⟨p2, h2⟩⟩

private theorem PureE_vlet {x : Name} {a b : Expr} (h : PureE (.vlet x a b)) :
    PureE a ∧ PureE b := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 =>
    cases h2 : Expr.toPExpr? b with
    | none => simp [h1, h2] at hpe
    | some p2 => exact ⟨⟨p1, h1⟩, ⟨p2, h2⟩⟩

private theorem PureE_app {a b : Expr} (h : PureE (.app a b)) : PureE a ∧ PureE b := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 =>
    cases h2 : Expr.toPExpr? b with
    | none => simp [h1, h2] at hpe
    | some p2 => exact ⟨⟨p1, h1⟩, ⟨p2, h2⟩⟩

private theorem PureE_ite {a b c : Expr} (h : PureE (.ite a b c)) :
    PureE a ∧ PureE b ∧ PureE c := by
  obtain ⟨pe, hpe⟩ := h
  simp only [Expr.toPExpr?] at hpe
  cases h1 : Expr.toPExpr? a with
  | none => simp [h1] at hpe
  | some p1 =>
    cases h2 : Expr.toPExpr? b with
    | none => simp [h1, h2] at hpe
    | some p2 =>
      cases h3 : Expr.toPExpr? c with
      | none => simp [h1, h2, h3] at hpe
      | some p3 => exact ⟨⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩

private def PureNLStmt (m : Nat) : Prop :=
  ∀ (ctx : TypeContext) (e : Expr) (res : TypeResult),
    typecheckExpr ctx e m = .ok res → PureE e → ctx.pureCtx = true →
      res.nextLoc' ≤ ctx.nextLoc

private theorem threaded_le {α : Type}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult) (base : Loc) :
    ∀ (xs : List α) (cursor : Tag × Loc) (results : List TypeResult),
      (∀ item, item ∈ xs → ∀ c r, c.2 ≤ base → applyOne item c = .ok r → r.nextLoc' ≤ base) →
      cursor.2 ≤ base → applyClosuresThreaded applyOne xs cursor = .ok results →
      ∀ y ∈ results, y.nextLoc' ≤ base := by
  intro xs
  induction xs with
  | nil =>
      intro cursor results _ _ hthread y hy
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      subst hthread
      cases hy
  | cons item rest ih =>
      intro cursor results hone hbase hthread y hy
      simp only [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _ => simp [hfirst] at hthread
      | ok first =>
          simp only [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest (first.nextTag', first.nextLoc') with
          | error _ => simp [hrest] at hthread
          | ok restResults =>
              simp only [hrest, pure, Except.pure, Except.ok.injEq] at hthread
              subst hthread
              have hfb := hone item (List.mem_cons_self ..) cursor first hbase hfirst
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hfb
              · exact ih (first.nextTag', first.nextLoc') restResults
                  (fun it hit c r hc happ => hone it (List.mem_cons_of_mem _ hit) c r hc happ)
                  hfb hrest y hy

private theorem returnSpecToQTyp_nextLoc_eq (typ : Typ) (poison : Bool) (pred : Predicate)
    (nextLoc : Loc) (ret : QTyp × Loc)
    (h : returnSpecToQTyp typ poison pred nextLoc = .ok ret) : ret.2 = nextLoc := by
  unfold returnSpecToQTyp at h
  cases typ with
  | int | bool | unit | string =>
      simp [bind, Except.bind, pure, Except.pure] at h
      exact (congrArg Prod.snd h).symm
  | ref _ => simp [bind, Except.bind] at h
  | arrow _ _ => simp [bind, Except.bind] at h

private theorem applyPFnTClosureAtCursor_le (tcl : PFnTClosure) (st1 st2 : Typ)
    (p p1 : Poison) (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (r1 : TypeResult) (cursor : Tag × Loc) (fuel : Nat) (r : TypeResult)
    (IH : ∀ m < fuel, PureNLStmt m)
    (h : applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx r1 cursor fuel
      = .ok r) : r.nextLoc' ≤ cursor.2 := by
  unfold applyPFnTClosureAtCursor at h
  cases fuel <;> simp at h
  rename_i k
  cases tcl <;> simp at h
  · simp [bind, Except.bind] at h
    rcases htc : typecheckExpr _ _ _ with _ | ⟨v⟩
      <;> rw [htc] at h
      <;> simp at h
    rcases hqt : v.qualType with ⟨etyp, poison, pred⟩
    simp [hqt] at h
    rcases hsub : isErasureOf st2 _
      <;> rw [hsub] at h
      <;> simp at h
    · simp [Functor.map, Except.map] at h
    · simp [pure, Except.pure] at h
      subst r
      have hle := IH k (Nat.lt_succ_self k) _ _ _ htc ⟨_, toExpr_toPExpr? _⟩ rfl
      simpa using hle
  · simp [bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Functor.map, Except.map] at h
          split at h
          · simp at h
          · rename_i v hret
            split at h
            · exact nomatch h
            simp only [Except.ok.injEq] at h; rw [← h]
            have := returnSpecToQTyp_nextLoc_eq _ _ _ cursor.2 v hret; simp [this]
    · simp only [Functor.map, Except.map] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; rw [← h]
    · simp only [Functor.map, Except.map] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; rw [← h]

private theorem pure_nextLoc_le :
    ∀ (fuel : Nat), PureNLStmt fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res htc hpe hp
    cases fuel with
    | zero => unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact Nat.le_refl _
        | bool _b =>
            unfold typecheckBool at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact Nat.le_refl _
        | unit =>
            unfold typecheckUnit at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact Nat.le_refl _
        | str _s =>
            unfold typecheckString at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact Nat.le_refl _
        | var x => exact (typecheckVar_preserves_nextLoc _ _ _ htc).le
        | fn _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | pfn _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | externVal _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | externRef _ _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | externFn _ _ _ _ _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | externPfn _ _ _ _ _ _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | newRef _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | assign _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | seq _ _ =>
            exfalso; obtain ⟨pe, h⟩ := hpe; simp [Expr.toPExpr?] at h
        | unaryop op e1 =>
            rcases typecheckUnaryOp_structure ctx op e1 fuel' res htc with
              ⟨result1, _, htc1, _, _, _, hnloc, _, _, _, _, _⟩
            rw [hnloc]
            exact IH (fuel' - 1) (by omega) ctx e1 result1 htc1 (PureE_unaryop hpe) hp
        | deref e1 =>
            rcases typecheckDeref_structure ctx e1 fuel' res htc with
              ⟨result1, htc1, _, _, hnloc, _, _⟩
            rw [hnloc]
            exact IH (fuel' - 1) (by omega) ctx e1 result1 htc1 (PureE_deref hpe) hp
        | op e1 op e2 =>
            rcases typecheckOp_structure ctx e1 e2 op fuel' res htc with
              ⟨result1, result2, _, htc1, htc2, _, _, _, hnloc, _, _, _, _, _⟩
            obtain ⟨pe1, pe2⟩ := PureE_op hpe
            rw [hnloc]
            have h1 : result1.nextLoc' ≤ ctx.nextLoc :=
              IH (fuel' - 1) (by omega) ctx e1 result1 htc1 pe1 hp
            have h2 : result2.nextLoc' ≤ result1.nextLoc' :=
              IH (fuel' - 1) (by omega) _ e2 result2 htc2 pe2 hp
            exact Nat.le_trans h2 h1
        | vlet x e1 e2 =>
            rcases typecheckVlet_structure ctx x e1 e2 fuel' res htc with
              ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, _, hnloc, _, _, _, _⟩
            subst hctx'
            obtain ⟨pe1, pe2⟩ := PureE_vlet hpe
            rw [hnloc]
            have h1 : result1.nextLoc' ≤ ctx.nextLoc :=
              IH (fuel' - 1) (by omega) ctx e1 result1 htc1 pe1 hp
            have h2 : result2.nextLoc' ≤ result1.nextLoc' :=
              IH (fuel' - 1) (by omega) _ e2 result2 htc2 pe2 hp
            exact Nat.le_trans h2 h1
        | ite e1 e2 e3 =>
            obtain ⟨pe1, pe2, pe3⟩ := PureE_ite hpe
            rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htc with h1 | h2 | hstd
            · rcases h1 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, _htag, hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              rw [hnloc]
              have h2 := IH (fuel' - 1) (by omega) _ e2 res2 htc2 pe2 hp
              have h3 : res3.nextLoc' ≤ res2.nextLoc' :=
                IH (fuel' - 1) (by omega) _ e3 res3 htc3 pe3 hp
              exact max_le h2 (Nat.le_trans h3 h2)
            · rcases h2 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, _htag, hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              rw [hnloc]
              have h2 := IH (fuel' - 1) (by omega) _ e2 res2 htc2 pe2 hp
              have h3 : res3.nextLoc' ≤ res2.nextLoc' :=
                IH (fuel' - 1) (by omega) _ e3 res3 htc3 pe3 hp
              exact max_le h2 (Nat.le_trans h3 h2)
            · rcases hstd with
                ⟨hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3_raw, _hmemEnv, _htag,
                  hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res, _hpred_res⟩
              rw [hnloc]
              have h1 : res1.nextLoc' ≤ ctx.nextLoc :=
                IH (fuel' - 1) (by omega) ctx e1 res1 htc1 pe1 hp
              have h2 : res2.nextLoc' ≤ res1.nextLoc' :=
                IH (fuel' - 1) (by omega) _ e2 res2 htc2 pe2 hp
              have h3 : res3.nextLoc' ≤ res2.nextLoc' :=
                IH (fuel' - 1) (by omega) _ e3 res3 htc3_raw pe3 hp
              exact max_le (Nat.le_trans h2 h1) (Nat.le_trans h3 (Nat.le_trans h2 h1))
        | app e1 e2 =>
            simp at htc
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
                obtain ⟨pe1, pe2⟩ := PureE_app hpe
                rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
                  ⟨result2, result1, etyp2, p2, pred2, _hqt2, htc2, htc1, hcases⟩
                have IHm : PureNLStmt fuel'' := IH fuel'' (by omega)
                have h2 : result2.nextLoc' ≤ ctx.nextLoc := IHm _ _ _ htc2 pe2 hp
                have h1 : result1.nextLoc' ≤ result2.nextLoc' := IHm _ _ _ htc1 pe1 hp
                rcases hcases with
                  ⟨_, _, _, _, _, _, _, _, _, _, _, hnp, _⟩ |
                  ⟨st1, st2, p, p1, tcls, results, first, rest, joined, _hetyp1, _hp1, _hne,
                    _hsub, hmap, hresults, hjoin, rfl⟩
                · exact absurd hp hnp
                · subst hresults
                  have hone : ∀ item, item ∈ tcls → ∀ c r, c.2 ≤ result1.nextLoc' →
                      applyPFnTClosureAtCursor item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        c fuel'' = .ok r → r.nextLoc' ≤ result1.nextLoc' :=
                    fun item _ c r hc happ =>
                      Nat.le_trans (applyPFnTClosureAtCursor_le item st1 st2 p p1 etyp2 p2 pred2
                        ctx result1 c fuel'' r (fun m hm => IH m (by omega)) happ) hc
                  have hmemb := threaded_le
                    (fun tcl cursor => applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                      ctx result1 cursor fuel'') result1.nextLoc' tcls _ _ hone (Nat.le_refl _) hmap
                  have hall : ∀ b ∈ first.nextLoc' :: rest.map TypeResult.nextLoc',
                      b ≤ result1.nextLoc' := by
                    intro b hb
                    rcases List.mem_cons.mp hb with rfl | hb
                    · exact hmemb first (List.mem_cons_self ..)
                    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
                      exact hmemb y (List.mem_cons_of_mem _ hy)
                  have hjn : joined.nextLoc' ≤ result1.nextLoc' := by
                    rw [joinTypeResults_nextLoc_eq_max ctx first rest joined hjoin]
                    exact hall _ (List.max_mem _)
                  exact Nat.le_trans hjn (Nat.le_trans h1 h2)

private theorem pure_cond_below {m : Nat} (IH : LogBelowStmt m) {ctx : TypeContext}
    {e1 : Expr} {res1 : TypeResult}
    (hwf : wfTypeContext ctx) (hpe : PureE e1)
    (h1 : typecheckExpr { ctx with pureCtx := true } e1 m = .ok res1) :
    LogFootBelow res1.tagLog' ctx.nextLoc := by
  have hle := pure_nextLoc_le m _ _ _ h1 hpe rfl
  exact (IH _ _ _ h1 hwf).mono hle

/-! ### The induction -/

private theorem typecheck_log_footprints_below_aux :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    typecheckExpr ctx e fuel = .ok res → wfTypeContext ctx →
      LogFootBelow res.tagLog' res.nextLoc' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro ctx e res htc hwf
    have hnl : ctx.nextLoc ≤ res.nextLoc' := typecheck_nextLoc_mono ctx e fuel res htc
    cases fuel with
    | zero => unfold typecheckExpr at htc; simp at htc
    | succ fuel' =>
        unfold typecheckExpr at htc
        cases e with
        | num _n =>
            unfold typecheckInt at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact LogFootBelow.nil _
        | bool _b =>
            unfold typecheckBool at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact LogFootBelow.nil _
        | unit =>
            unfold typecheckUnit at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact LogFootBelow.nil _
        | str _s =>
            unfold typecheckString at htc
            simp [pure, Except.pure] at htc
            cases htc
            exact LogFootBelow.nil _
        | var x =>
            rw [typecheckVar_tagLog' _ _ _ htc]
            exact LogFootBelow.nil _
        | fn _ _ _ _ =>
            rw [typecheckFn_tagLog' _ _ _ _ _ _ htc]
            exact LogFootBelow.nil _
        | pfn _ _ _ _ =>
            rw [typecheckPfn_tagLog' _ _ _ _ _ _ htc]
            exact LogFootBelow.nil _
        | externVal id typ poison pred =>
            have htc' : typecheckExternVal ctx id typ poison pred fuel' = .ok res := htc
            obtain ⟨_, tagMapping, _, resolvedPred, _, _halloc, _hres, _, rfl⟩ :=
              typecheckExternVal_ok_shape htc'
            exact (externTagLog_below _ _ _ _ (EnvBd.of_wf hwf)).mono hnl
        | externRef _ _ _ _ _ =>
            rw [typecheckExternRef_tagLog' _ _ _ _ _ _ _ htc]
            exact LogFootBelow.nil _
        | externFn _ _ _ _ _ _ _ _ =>
            rw [typecheckExternFn_tagLog' _ _ _ _ _ _ _ _ _ _ _ htc]
            exact LogFootBelow.nil _
        | externPfn _ _ _ _ _ _ _ =>
            rw [typecheckExternPfn_tagLog' _ _ _ _ _ _ _ _ _ _ htc]
            exact LogFootBelow.nil _
        | unaryop op e1 =>
            rcases typecheckUnaryOp_structure ctx op e1 fuel' res htc with
              ⟨result1, _, htc1, _, _, _, hnloc, _, _, _, _, _⟩
            rw [typecheckUnaryOp_tagLog htc htc1, hnloc]
            exact IH (fuel' - 1) (by omega) ctx e1 result1 htc1 hwf
        | deref e1 =>
            rcases typecheckDeref_structure ctx e1 fuel' res htc with
              ⟨result1, htc1, _, _, hnloc, _, _⟩
            rw [typecheckDeref_tagLog htc htc1, hnloc]
            exact IH (fuel' - 1) (by omega) ctx e1 result1 htc1 hwf
        | newRef e1 =>
            rcases typecheckNewRef_structure ctx e1 fuel' res htc with
              ⟨result1, _, htc1, _, _, _, _, _, _, _, hnloc, _, _⟩
            rw [typecheckNewRef_tagLog htc htc1, hnloc]
            exact (IH (fuel' - 1) (by omega) ctx e1 result1 htc1 hwf).mono (Nat.le_succ _)
        | op e1 op e2 =>
            rcases typecheckOp_structure ctx e1 e2 op fuel' res htc with
              ⟨result1, result2, _, htc1, htc2, _, _, _, hnloc, _, _, _, _, _⟩
            rw [typecheckOp_tagLog htc htc1 htc2, hnloc]
            exact seq_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf htc1 htc2
              (next_wf hwf htc1 rfl rfl rfl) rfl
        | assign e1 e2 =>
            rcases typecheckAssign_structure ctx e1 e2 fuel' res htc with
              ⟨result1, result2, ls, htc1, _, htc2, _, hnloc, _, _, _, _, _⟩
            rw [typecheckAssign_tagLog htc htc1 htc2, hnloc]
            exact (seq_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf htc1 htc2
              (next_wf hwf htc1 rfl rfl rfl) rfl).mono (fold_ge _ _)
        | seq e1 e2 =>
            rcases typecheckSeq_structure ctx e1 e2 fuel' res htc with
              ⟨result1, ctx', result2, htc1, hctx', htc2, rfl⟩
            subst hctx'
            exact seq_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf htc1 htc2
              (next_wf hwf htc1 rfl rfl rfl) rfl
        | vlet x e1 e2 =>
            rcases typecheckVlet_structure ctx x e1 e2 fuel' res htc with
              ⟨result1, result2, ctx', htc1, hctx', htc2, _, _, _, hnloc, _, _, _, _⟩
            subst hctx'
            have hr1 := typecheckExpr_preserves_wfTypeResult ctx e1 (fuel' - 1) result1 hwf htc1
            have hm1 := typecheck_nextLoc_mono ctx e1 (fuel' - 1) result1 htc1
            have hrl := typecheckExpr_preserves_etypRefLocsBounded ctx e1 (fuel' - 1) result1
              hwf htc1
            have hcl := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctx e1
              (fuel' - 1) result1 hwf htc1
            have hwf2 : wfTypeContext
                { ctx with memEnv := result1.memEnv',
                           varEnv := ctx.varEnv.update x result1.qualType,
                           tagEnv := result1.tagEnv', nextLoc := result1.nextLoc',
                           nextTag := result1.nextTag', regime := result1.regime',
                           declaredExternRefs := result1.declared' } :=
              ⟨hr1,
               varEnvRefLocsBounded_update (varEnvRefLocsBounded_mono hwf.2.1 hm1) hrl,
               varEnvClosuresCapturedRefLocsBounded_update
                 (varEnvClosuresCapturedRefLocsBounded_mono hwf.2.2 hm1) hcl⟩
            rw [typecheckVlet_tagLog htc htc1 htc2, hnloc]
            exact seq_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf htc1 htc2 hwf2 rfl
        | ite e1 e2 e3 =>
            rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htc with h1 | h2 | hstd
            · rcases h1 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, _htag, hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              rw [typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3, hnloc]
              obtain ⟨pe, hpe⟩ := matchGuard_ok_toPExpr?_some ctx e1 k deps hmatch
              exact matched_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf
                (pure_cond_below (IH (fuel' - 1) (by omega)) hwf ⟨pe, hpe⟩ htc1p) htc2 htc3
                rfl rfl rfl rfl rfl rfl
            · rcases h2 with
                ⟨k, deps, hmatch, hRk, res1, htc1p, _hbool, res2, res3, htc2, htc3,
                  _hmemEnv, _htag, hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res⟩
              rw [typecheckIf_tagLog_matched htc hmatch hRk htc1p htc2 htc3, hnloc]
              obtain ⟨pe, hpe⟩ := matchGuard_ok_toPExpr?_some ctx e1 k deps hmatch
              exact matched_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf
                (pure_cond_below (IH (fuel' - 1) (by omega)) hwf ⟨pe, hpe⟩ htc1p) htc2 htc3
                rfl rfl rfl rfl rfl rfl
            · rcases hstd with
                ⟨hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3_raw, _hmemEnv, _htag,
                  hnloc, _hnextTag, _hregime, _hdecl, _hpoison, _hetyp_res, _hpred_res⟩
              rw [typecheckIf_tagLog_std htc hstdCase htc1 htc2 htc3_raw, hnloc]
              exact seq3_below (m := fuel' - 1) (IH (fuel' - 1) (by omega)) hwf htc1 htc2
                htc3_raw rfl rfl rfl rfl rfl rfl
        | app e1 e2 =>
            simp at htc
            cases fuel' with
            | zero => simp [typecheckApp] at htc
            | succ fuel'' =>
                rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel'' res htc with
                  ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, hcases⟩
                have IHm : LogBelowStmt fuel'' := IH fuel'' (by omega)
                have hr2 := typecheckExpr_preserves_wfTypeResult ctx e2 fuel'' result2 hwf htc2
                have hm2 := typecheck_nextLoc_mono ctx e2 fuel'' result2 htc2
                have hwf1 : wfTypeContext (ctxAfter ctx result2) :=
                  wfTypeContext_of_wfTypeResult ctx result2 hr2 hwf hm2
                have htc1' : typecheckExpr (ctxAfter ctx result2) e1 fuel'' = .ok result1 := htc1
                have hr1 := typecheckExpr_preserves_wfTypeResult (ctxAfter ctx result2) e1 fuel''
                  result1 hwf1 htc1'
                have hm1 : result2.nextLoc' ≤ result1.nextLoc' :=
                  typecheck_nextLoc_mono (ctxAfter ctx result2) e1 fuel'' result1 htc1'
                have hargRL : etypRefLocsBounded etyp2 result1.nextLoc' := by
                  have h := typecheckExpr_preserves_etypRefLocsBounded ctx e2 fuel'' result2
                    hwf htc2
                  rw [hqt2] at h
                  exact etypRefLocsBounded_mono h hm1
                have hargCL : etypClosuresCapturedRefLocsBounded etyp2 result1.nextLoc' := by
                  have h := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded ctx e2
                    fuel'' result2 hwf htc2
                  rw [hqt2] at h
                  exact etypClosuresCapturedRefLocsBounded_mono h hm1
                have hcl1 := typecheckExpr_preserves_etypClosuresCapturedRefLocsBounded
                  (ctxAfter ctx result2) e1 fuel'' result1 hwf1 htc1'
                have hlog2 := IHm _ _ _ htc2 hwf
                have hlog1 := IHm _ _ _ htc1' hwf1
                have IHc : ∀ m < fuel'', ∀ (ctx' : TypeContext) (e : Expr) (res' : TypeResult),
                    typecheckExpr ctx' e m = .ok res' → wfTypeContext ctx' →
                      LogFootBelow res'.tagLog' res'.nextLoc' := fun m hm => IH m (by omega)
                have hmonoAll : ∀ m < fuel'', ∀ (e : Expr) (ctx' : TypeContext) (res' : TypeResult),
                    typecheck ctx' e m = .ok res' → ctx'.nextLoc ≤ res'.nextLoc' :=
                  fun m _ e c' r' htc' => typecheck_nextLoc_mono c' e m r' htc'
                rcases hcases with
                  ⟨st1, st2, p, p1, tcls, results, first, rest, joined, hetyp1, _hp1, _hpure,
                    _hne, _hsub, hmap, hresults, hjoin, rfl⟩ |
                  ⟨st1, st2, p, p1, tcls, results, first, rest, joined, hetyp1, _hp1, _hne,
                    _hsub, hmap, hresults, hjoin, rfl⟩
                · subst hresults
                  have hcl : ∀ tcl ∈ tcls, match tcl with
                      | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
                      | .extern _ _ _ _ env _ _ =>
                          CapturedEnvRefLocsFullBounded env result1.nextLoc' := by
                    rw [hetyp1] at hcl1; exact hcl1
                  have hone : ∀ item, item ∈ tcls → ∀ cursor' r, result1.nextLoc' ≤ cursor'.2 →
                      applyFnTClosureAtCursor item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        cursor' fuel'' = .ok r → LogFootBelow r.tagLog' r.nextLoc' :=
                    fun item hitem c r hb happ =>
                      applyFnTClosureAtCursor_below item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        c fuel'' r IHc hr1 hb (hcl item hitem) hargRL hargCL happ
                  have hmono_one : ∀ item cursor' (r : TypeResult),
                      result1.nextLoc' ≤ cursor'.2 →
                      applyFnTClosureAtCursor item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        cursor' fuel'' = .ok r → result1.nextLoc' ≤ r.nextLoc' :=
                    fun item c r hb happ =>
                      applyFnTClosureAtCursor_nextLoc_mono item ctx st1 st2 p p1 etyp2 p2 pred2
                        result1 r c fuel'' hb hmonoAll happ
                  have hmemb := threaded_below
                    (fun tcl cursor => applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                      ctx result1 cursor fuel'') result1.nextLoc' hone hmono_one (Nat.le_refl _) hmap
                  have hjn := joinTypeResults_member_nextLoc_le ctx first rest joined hjoin
                  have hjl := joinTypeResults_tagLog ctx first rest joined hjoin
                  have hres1_le : result1.nextLoc' ≤ joined.nextLoc' :=
                    Nat.le_trans (hmemb first (List.mem_cons_self ..)).2
                      (hjn first (List.mem_cons_self ..))
                  refine LogFootBelow.append hlog2
                    (LogFootBelow.append hlog1 ?_ hres1_le (Nat.le_refl _))
                    (Nat.le_trans hm1 hres1_le) (Nat.le_refl _)
                  intro a ha l hl
                  rw [hjl, ← List.flatMap_cons] at ha
                  obtain ⟨r, hr, har⟩ := List.mem_flatMap.mp ha
                  exact Nat.lt_of_lt_of_le ((hmemb r hr).1 a har l hl) (hjn r hr)
                · subst hresults
                  have hcl : ∀ tcl ∈ tcls, match tcl with
                      | .regular _ _ env => CapturedEnvRefLocsFullBounded env result1.nextLoc'
                      | .extern _ _ _ env _ _ =>
                          CapturedEnvRefLocsFullBounded env result1.nextLoc' := by
                    rw [hetyp1] at hcl1; exact hcl1
                  have hone : ∀ item, item ∈ tcls → ∀ cursor' r, result1.nextLoc' ≤ cursor'.2 →
                      applyPFnTClosureAtCursor item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        cursor' fuel'' = .ok r → LogFootBelow r.tagLog' r.nextLoc' :=
                    fun item hitem c r hb happ =>
                      applyPFnTClosureAtCursor_below item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        c fuel'' r IHc hr1 hb (hcl item hitem) hargRL hargCL happ
                  have hmono_one : ∀ item cursor' (r : TypeResult),
                      result1.nextLoc' ≤ cursor'.2 →
                      applyPFnTClosureAtCursor item st1 st2 p p1 etyp2 p2 pred2 ctx result1
                        cursor' fuel'' = .ok r → result1.nextLoc' ≤ r.nextLoc' :=
                    fun item c r hb happ =>
                      applyPFnTClosureAtCursor_nextLoc_mono item ctx st1 st2 p p1 etyp2 p2 pred2
                        result1 r c fuel'' hb hmonoAll happ
                  have hmemb := threaded_below
                    (fun tcl cursor => applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                      ctx result1 cursor fuel'') result1.nextLoc' hone hmono_one (Nat.le_refl _) hmap
                  have hjn := joinTypeResults_member_nextLoc_le ctx first rest joined hjoin
                  have hjl := joinTypeResults_tagLog ctx first rest joined hjoin
                  have hres1_le : result1.nextLoc' ≤ joined.nextLoc' :=
                    Nat.le_trans (hmemb first (List.mem_cons_self ..)).2
                      (hjn first (List.mem_cons_self ..))
                  refine LogFootBelow.append hlog2
                    (LogFootBelow.append hlog1 ?_ hres1_le (Nat.le_refl _))
                    (Nat.le_trans hm1 hres1_le) (Nat.le_refl _)
                  intro a ha l hl
                  rw [hjl, ← List.flatMap_cons] at ha
                  obtain ⟨r, hr, har⟩ := List.mem_flatMap.mp ha
                  exact Nat.lt_of_lt_of_le ((hmemb r hr).1 a har l hl) (hjn r hr)

/-! ### The two theorems -/

theorem typecheck_log_footprints_below :
    ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    wfTypeContext ctx → typecheck ctx e fuel = .ok res →
    ∀ a ∈ res.tagLog', ∀ l, InFootprint a.tag a.desc l → l < res.nextLoc' := by
  intro fuel ctx e res hwf htc a ha l hl
  exact typecheck_log_footprints_below_aux fuel ctx e res htc hwf a ha l hl

theorem typingKeepsFootprintBelow : TypingKeepsFootprintBelow := by
  intro ctx e fuel res tm tm' htc _hwfTm _hb _htb hwf _hext hw hfp k d hk l hl
  have hlogb := typecheck_log_footprints_below fuel ctx e res hwf htc
  have hmono := typecheck_nextLoc_mono ctx e fuel res htc
  rcases hw k d hk with hold | ⟨a, ha, hak, had⟩
  · exact Nat.lt_of_lt_of_le (hfp k d hold l hl) hmono
  · subst hak
    subst had
    exact hlogb _ ha l hl

/-- A successful typing run from a well-formed context keeps the footprint
    invariant `FootprintCtx`. -/
theorem typingKeepsFootprintCtx : TypingKeepsFootprintCtx :=
  ⟨typingKeepsRecordsCover, typingKeepsFootprintBelow⟩

/-! ### The root step -/

open Classical in
/-- The table restricted to the guards of the context. -/
noncomputable def restrictTo (tm : TagMeaning) (ctx : TypeContext) : TagMeaning :=
  tm.filter fun k d => decide (GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d)

theorem restrictTo_lookup {tm : TagMeaning} {ctx : TypeContext} {k : Tag} {d : GuardDesc} :
    (restrictTo tm ctx).lookup k = some d ↔
      tm.lookup k = some d ∧ GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d := by
  classical
  unfold restrictTo TagMeaning.lookup
  rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_filter', ← ExtTreeMap.get?_eq_getElem?]
  cases h : tm.get? k with
  | none => simp
  | some d' =>
      simp only [Option.filter]
      by_cases hg : GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d'
      · simp [hg]
        rintro rfl; exact hg
      · simp [hg]
        rintro rfl; exact hg

/-- At a starting context with an empty tag environment that meets the start
    condition, the table restricted to the context's guards is part of the
    table, keeps `wfTagMeaningCtx`, and satisfies `FootprintCtx`. -/
theorem root_footprintCtx (tm : TagMeaning) (ctx : TypeContext)
    (htag : ctx.tagEnv = ∅) (hwf : wfTagMeaningCtx tm ctx) (hstart : GuardCapsBelow ctx) :
    restrictTo tm ctx ⊑ tm ∧ wfTagMeaningCtx (restrictTo tm ctx) ctx ∧
      FootprintCtx (restrictTo tm ctx) ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k d hd
    exact (restrictTo_lookup.mp hd).1
  · refine EnvRespectsTagMeaning.intro fun {k d} hg => ?_
    exact restrictTo_lookup.mpr ⟨hwf.1 hg, hg⟩
  · intro k tv d hk
    rw [htag] at hk
    simp at hk
  · intro k d hd l hl
    exact InFootprint_lt_of_capEnv_bounded (hstart k d (restrictTo_lookup.mp hd).2) l hl
