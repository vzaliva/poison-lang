import LeanProofs.TypeSafety

/-!
# Branch-join capture conjunction

This module discharges the **branch-join capture conjunction merge** obligation
for extern `captures:` read dependencies.

The design requirement is:

> Capture preconditions combine by **conjunction**, not by the return-side join
> that collapses distinct predicate shapes to `noPred`. If two branches require
> distinct non-`noPred` predicate shapes for the same target, there may be no
> single `target :> QTyp` meet; the implementation must reject that merge (or
> require compatible shapes) rather than collapse capture predicates to `noPred`,
> because that would drop a precondition the extern implementation may depend on.

The Poison typechecker satisfies this requirement **structurally**, by the way
branch joins already merge closure type-members:

* `joinETyps` on `parrow`s merges the two branches' closure-member lists with
  `mergePFnTClosures`, a set-union that *deduplicates by `beqPFnTClosure`*.
  Before deduplication, members of one group (`PFnTClosure.sameButEnv`: for
  extern members, the same extern, parameter and return specification) keep an
  entry of their captured environments where it is the same in all of them and
  have every binding number in it set to 0 otherwise; the `captures:` contract
  is not touched. `beqPFnTClosure` compares the whole member **including its captures**
  (`beqCaptureList` is one of its conjuncts), so two members that agree on
  everything except their `captures:` contract are **not** deduplicated — they are
  kept as *distinct* members of the merged `parrow`.
* Capture contracts never pass through `joinPredicates` (the agreement-only
  predicate join that is the source of `noPred` collapse). They ride verbatim on
  their distinct closure members, so a branch's capture predicate shape can never
  be silently weakened to `noPred` by a join.
* Applying a multi-member `parrow` (`applyClosuresThreaded`) runs **every**
  member's `applyPFnTClosureAtCursor`, and each extern member's
  `applyPFnTClosureAtCursor` gates on that member's own `capturesSatisfied`. A
  successful application therefore requires *every* member's capture contract to
  hold — i.e. the **conjunction** of both branches' captures.

The lemmas below make this explicit:

* `mem_mergePFnTClosures_extern_captures` — every extern member of either branch
  has a copy in the merged member list with its `captures:` contract verbatim and
  its captured environment kept or zeroed entry by entry (`CapEnvZeroedFrom`): no
  capture is dropped or weakened by the merge (the structural "conjunction not
  collapse" fact, anchored on `beqPFnTClosure ⊇ beqCaptureList`).
* `capturesSatisfied_update_ofCaptured_zeroedFrom` — the capture gate reads the
  surface type, the poison and the predicate of each captured variable, never a
  binding number, so it has the same value on the zeroed copy.
* `applyPFnTClosureAtCursor_extern_captures` — a successful extern-member
  application implies that member's `capturesSatisfied` gate held.
* `applyClosuresThreaded_ok_mem` — a successful threaded application of a member
  list implies every member was applied successfully.
* `mergedParrow_apply_captures_conjunction` — the operational conjunction:
  applying the **merged** `parrow` succeeds only if *both* branches' extern
  members' capture contracts are satisfied. This is the precise statement that
  capture preconditions combine by conjunction across branch joins.

Fault-robustness of the merged capture contract is then **inherited** from the
generic FR step theorem: the application case (`stepFR_app_with_expr_proof` in
`StepFRApp.lean`) reads the applied member's `captures` (its
`memberCap`) directly from membership in the function-position `parrow`'s
(merged) member list — `ExternCallBoundaryPfnStaticSource.externMember` carries
`PFnTClosure.extern … memberCap ∈ tcls`, which threads through
`Call.pfnExternMember` (`d.captures = captures`, driving `capturesSatisfied`)
into the registry entry's `callFR`. `TrustedRegistryAgreesWithReachable` covers
the matched member because `ExternDeclarationInProgram` descends into *both*
branches of an `ite` (`ite_then` / `ite_else`). No capture-specific transport
lemma is needed in `JoinMemberTransport` (that module transports the *result*
type of an application, not the function-position captures).

Two clarifications on scope.

* *Call-time, not join-time, rejection.* The merge does not reject incompatible
  capture shapes at join time. It keeps both members; the rejection happens at
  the call boundary, where applying the merged `parrow` fires every member's
  gate (`applyClosuresThreaded`) and a single actual cannot satisfy two
  incompatible non-`noPred` shapes. This is one of the design's permitted
  realisations of "reject the merge" from the `captures:` model: the precondition
  is never collapsed to `noPred`; it is enforced as a conjunction at the call.

* *Why there is no single-extern two-distinct-member program-FR artifact.* No
  program joins two members of one extern id with distinct captures: the
  typechecker rejects a second declaration of an id, also in the other arm of an
  `if`. Such a pair would in any case fall *outside* the top-level FR theorem's
  domain: `TrustedRegistryAgreesWithProgram` requires every reachable
  declaration to match its registry entry *exactly* (captures included), and two
  same-id reachable decls that disagree on captures cannot both equal one entry.
  A two-member join under *distinct* ids (with matching signatures) is
  FR-reachable and *is* covered by the generic theorem once each id has a trusted
  entry; we ship no trusted-spec pair for one only because it would require a
  second trusted extern whose sole purpose is the join, which is out of scope
  here. `examples/extern_captures_join_memread.poison` joins the built-in `@23`
  with a native `pfn` (it typechecks and runs end-to-end to `3`); the join keeps
  `@23`'s `!r` contract. Identical members (one declaration reaching both arms)
  deduplicate to a single member and exercise nothing multi-member.

The lemmas in this module are illustrative anchors that verify the structural and
operational conjunction facts in isolation; they are intentionally *not* on the
FR proof path (which uses the `applyClosuresThreaded_ok_mem_*` threaded-application
member lemmas of `TypecheckInduction.lean`, `StepFR.lean` and `StepFRApp.lean`, and
the membership machinery consumed by the application case). Together with the
generic FR theorem they are the soundness story for the merge itself.
-/

open Std

namespace CaptureJoinConjunction

/-- **Captures survive the merge.** Every extern closure member of either branch
    has a copy in the merged closure list `mergePFnTClosures tcls1 tcls2` with
    its `captures:` contract *verbatim* and its captured environment kept or
    zeroed entry by entry.

    This is the structural core of "capture preconditions combine by
    conjunction": the merge drops no member and (because `mergePFnTClosures`
    changes only captured environments and deduplicates via `beqPFnTClosure`,
    which compares `beqCaptureList`) never coalesces two members that differ in
    their captures. No branch's capture contract is
    dropped, and none is weakened to `noPred`. -/
private theorem mem_mergePFnTClosures_extern_captures
    (tcls1 tcls2 : List PFnTClosure)
    (id : ExternId) (x : Name) (retSpec : ExternReturn) (tenv : CapturedVarEnv)
    (declaredArgQt : QTyp) (captures : List Capture)
    (h : PFnTClosure.extern id x retSpec tenv declaredArgQt captures ∈ tcls1 ∨
         PFnTClosure.extern id x retSpec tenv declaredArgQt captures ∈ tcls2) :
    ∃ tenv', CapEnvZeroedFrom tenv tenv' ∧
      PFnTClosure.extern id x retSpec tenv' declaredArgQt captures
        ∈ mergePFnTClosures tcls1 tcls2 := by
  obtain ⟨tcl', hz, hmem⟩ := h.elim (mem_mergePFnTClosures_left _ _ _)
    (mem_mergePFnTClosures_right _ _ _)
  obtain ⟨tenv', he, rfl⟩ := hz.extern
  exact ⟨tenv', he, hmem⟩

private lemma ofCaptured_lookup_zeroedFrom {σ σ' : CapturedVarEnv}
    (hz : CapEnvZeroedFrom σ σ') (v : Name) :
    (VarTypeEnv.ofCaptured σ').lookup v = (VarTypeEnv.ofCaptured σ).lookup v ∨
      (VarTypeEnv.ofCaptured σ').lookup v = ((VarTypeEnv.ofCaptured σ).lookup v).map zeroQTyp := by
  unfold CapEnvZeroedFrom at hz
  induction hz with
  | nil => exact Or.inl rfl
  | @cons e e' l l' hr _ ih =>
      obtain ⟨x, q, n⟩ := e
      obtain ⟨x', q', n'⟩ := e'
      obtain ⟨rfl, hq⟩ := hr.qtyp
      have hfold : ∀ (y : Name) (qq : QTyp) (m : Nat) (t : CapturedVarEnv),
          VarTypeEnv.ofCaptured ((y, qq, m) :: t) = (VarTypeEnv.ofCaptured t).update y qq :=
        fun _ _ _ _ => rfl
      rw [hfold, hfold]
      by_cases hv : v = x'
      · subst hv
        rw [VarTypeEnv_lookup_update_eq, VarTypeEnv_lookup_update_eq]
        rcases hq with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rw [VarTypeEnv_lookup_update_ne _ _ _ _ hv, VarTypeEnv_lookup_update_ne _ _ _ _ hv]
        exact ih

private lemma captureSatisfied_zeroedEnv {c : Capture} {E E' : VarTypeEnv}
    {memEnv : MemoryTypeEnv} {R : Regime}
    (hE : ∀ v, E'.lookup v = E.lookup v ∨ E'.lookup v = (E.lookup v).map zeroQTyp) :
    captureSatisfied c E' memEnv R = captureSatisfied c E memEnv R := by
  unfold captureSatisfied
  cases c.target with
  | bareVar v =>
      dsimp only
      rcases hE v with h | h
      · rw [h]
      · rw [h]
        cases E.lookup v with
        | none => rfl
        | some qt => obtain ⟨e, p, pr⟩ := qt; cases e <;> rfl
  | memVar v =>
      dsimp only
      rcases hE v with h | h
      · rw [h]
      · rw [h]
        cases E.lookup v with
        | none => rfl
        | some qt => obtain ⟨e, p, pr⟩ := qt; cases e <;> rfl

/-- The capture gate of an extern member does not read binding numbers: it has
    the same value on a captured environment zeroed entry by entry. -/
private theorem capturesSatisfied_update_ofCaptured_zeroedFrom {caps : List Capture}
    {σ σ' : CapturedVarEnv} (hz : CapEnvZeroedFrom σ σ') {x : Name} {q : QTyp}
    {memEnv : MemoryTypeEnv} {R : Regime} :
    capturesSatisfied caps (VarTypeEnv.update (VarTypeEnv.ofCaptured σ') x q) memEnv R =
      capturesSatisfied caps (VarTypeEnv.update (VarTypeEnv.ofCaptured σ) x q) memEnv R := by
  have hE : ∀ v, (VarTypeEnv.update (VarTypeEnv.ofCaptured σ') x q).lookup v =
      (VarTypeEnv.update (VarTypeEnv.ofCaptured σ) x q).lookup v ∨
      (VarTypeEnv.update (VarTypeEnv.ofCaptured σ') x q).lookup v =
        ((VarTypeEnv.update (VarTypeEnv.ofCaptured σ) x q).lookup v).map zeroQTyp := by
    intro v
    by_cases hv : v = x
    · subst hv
      left
      rw [VarTypeEnv_lookup_update_eq, VarTypeEnv_lookup_update_eq]
    · rw [VarTypeEnv_lookup_update_ne _ _ _ _ hv, VarTypeEnv_lookup_update_ne _ _ _ _ hv]
      exact ofCaptured_lookup_zeroedFrom hz v
  unfold capturesSatisfied
  congr 1
  funext c
  exact captureSatisfied_zeroedEnv hE

/-- A successful extern-member application implies that member's `capturesSatisfied`
    call gate held. The argument condition and the `captures:` contract are fused
    into one guard inside `applyPFnTClosureAtCursor`; a non-`throw` (`.ok`) result
    forces the whole guard true, hence the capture conjunct. -/
private theorem applyPFnTClosureAtCursor_extern_captures
    {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison}
    {argPred : Predicate} {ctx : TypeContext} {result2 : TypeResult}
    {cursor : Tag × Loc} {bn : Nat} {fuel : Nat}
    {id : ExternId} {x : Name} {retSpec : ExternReturn} {tenv : CapturedVarEnv}
    {declaredArgQt : QTyp} {captures : List Capture} {res : TypeResult}
    (h : applyPFnTClosureAtCursor (PFnTClosure.extern id x retSpec tenv declaredArgQt captures)
          st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor bn fuel = Except.ok res) :
    capturesSatisfied captures
        (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
        result2.memEnv' result2.regime' = true := by
  cases fuel with
  | zero => simp [applyPFnTClosureAtCursor] at h
  | succ fuel =>
      simp only [applyPFnTClosureAtCursor, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · rename_i hgate
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hgate
        exact hgate.2

/-- A successful threaded application of a member list implies every member was
    applied successfully (at its threaded cursor and binding number). -/
private theorem applyClosuresThreaded_ok_mem {α : Type}
    {applyOne : α → Tag × Loc → Nat → TypecheckM TypeResult}
    {items : List α} {cursor : Tag × Loc} {bn : Nat} {results : List TypeResult}
    (h : applyClosuresThreaded applyOne items cursor bn = Except.ok results) :
    ∀ a ∈ items, ∃ c b r, applyOne a c b = Except.ok r := by
  induction items generalizing cursor bn results with
  | nil => intro a ha; cases ha
  | cons hd tl ih =>
      intro a ha
      rw [applyClosuresThreaded] at h
      cases hhd : applyOne hd cursor bn with
      | error e => rw [hhd] at h; simp [bind, Except.bind] at h
      | ok r =>
          rw [hhd] at h
          simp only [bind, Except.bind] at h
          cases htl : applyClosuresThreaded applyOne tl (r.nextTag', r.nextLoc') r.nextBind' with
          | error e => rw [htl] at h; simp at h
          | ok rs =>
              cases ha with
              | head => exact ⟨cursor, bn, r, hhd⟩
              | tail _ ha' => exact ih htl a ha'

/-- **Branch-join capture conjunction (operational).** When the merged `parrow`
    `mergePFnTClosures tcls1 tcls2` is applied successfully, every extern closure
    member of *either* branch has had its `captures:` contract satisfied. The
    branches' capture preconditions therefore combine by **conjunction**: applying
    the join requires both, never just one, and never a `noPred`-collapsed
    weakening. -/
theorem mergedParrow_apply_captures_conjunction
    {st1 st2 : Typ} {p p1 : Poison} {argEtyp : ETyp} {argPoison : Poison}
    {argPred : Predicate} {ctx : TypeContext} {result2 : TypeResult}
    {cursor : Tag × Loc} {bn : Nat} {fuel : Nat}
    {tcls1 tcls2 : List PFnTClosure} {results : List TypeResult}
    (happly : applyClosuresThreaded
        (fun tcl c b =>
          applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 c b fuel)
        (mergePFnTClosures tcls1 tcls2) cursor bn = Except.ok results)
    {id : ExternId} {x : Name} {retSpec : ExternReturn} {tenv : CapturedVarEnv}
    {declaredArgQt : QTyp} {captures : List Capture}
    (hmem : PFnTClosure.extern id x retSpec tenv declaredArgQt captures ∈ tcls1 ∨
            PFnTClosure.extern id x retSpec tenv declaredArgQt captures ∈ tcls2) :
    capturesSatisfied captures
        (VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
          ⟨argEtyp, joinPoison ctx.pc argPoison, argPred⟩)
        result2.memEnv' result2.regime' = true := by
  obtain ⟨tenv', hz, hmerge⟩ := mem_mergePFnTClosures_extern_captures tcls1 tcls2 id x
    retSpec tenv declaredArgQt captures hmem
  obtain ⟨_c, _b, _r, hone⟩ := applyClosuresThreaded_ok_mem happly _ hmerge
  rw [← capturesSatisfied_update_ofCaptured_zeroedFrom hz]
  exact applyPFnTClosureAtCursor_extern_captures hone

end CaptureJoinConjunction
