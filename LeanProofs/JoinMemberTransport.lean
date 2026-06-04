/-
  Shared join-member transport machinery: lemmas about how `joinTypeResults`
  transports per-member properties (consistentWithRegime, agreeOnClean,
  signatures, member-of-arrow/parrow, ref membership, internal-poison) to
  the joined result.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

lemma agreeValueUnder_clean_monotoneRegime
    {predSat : PredSat} {R R' : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap} {qt : QTyp} {v₀ v₁ : Value} :
    Regime.monotoneStep R R' →
      qtypCleanUnder R' qt →
        agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
          agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro h_mono hclean hagree
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      (fun qt hclean' => cleanUnder_of_monotone (R := R) (R' := R') h_mono hclean')
      (fun h => memberVarsRegimeEvidence_monotone h_mono h)
      (fun h => memberCvcrEvidence_monotone h_mono h)
      (fun h => memberVarsRegimeEvidence_monotone h_mono h)
      (fun h => memberCvcrEvidence_monotone h_mono h)
      hclean hagree

/-- Extended-regime (`monotoneStepExt`) variant of `agreeValueUnder_clean_monotoneRegime`.
    The fresh-tag freshness is discharged from the closure-tag bound on `qt`. -/
lemma agreeValueUnder_clean_monotoneRegime_ext
    {predSat : PredSat} {R R' : Regime} {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {qt : QTyp} {v₀ v₁ : Value} {newTags : Tag → Prop} {B : Tag}
    (h_mono : Regime.monotoneStepExt R R' newTags)
    (hnewB : ∀ k, newTags k → B ≤ k)
    (hbound : etypClosuresFullBounded qt.etyp B) :
    qtypCleanUnder R' qt →
      agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ →
        agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁ := by
  intro hclean hagree
  exact agreeValueUnder_clean_transport_by_cleanBack_ext h_mono hnewB hbound hclean hagree

private lemma qtypCleanUnder_lookup_true_back
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

private lemma agreeValueUnder_clean_transport_by_lookupTrueBack
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
    exact qtypCleanUnder_lookup_true_back hlookup_true_back hclean'
  exact
    agreeValueUnder_clean_transport_by_cleanBack
      h_clean_back
      hmemberVars₀_transport hmemberCvcr₀_transport
      hmemberVars₁_transport hmemberCvcr₁_transport
      hclean hagree

private lemma agreeCapturedEnv_transport_by_lookupTrueBack
    {predSat : PredSat} {R R' : Regime}
    {μ₀ μ₁ : Memory} {θ₀ θ₁ : RealizationMap}
    {σcap : CapturedVarEnv} {ρcap₀ ρcap₁ : VarEnv}
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
    agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ →
      agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁ := by
  intro hcap
  have h_clean_back : ∀ qt, qtypCleanUnder R' qt → qtypCleanUnder R qt := by
    intro qt hclean
    exact qtypCleanUnder_lookup_true_back hlookup_true_back hclean
  let motive₁ :
      (a : QTyp) → (a_1 a_2 : Value) → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun qt v₀ v₁ _ =>
      qtypCleanUnder R' qt → agreeValueUnder predSat R' μ₀ μ₁ θ₀ θ₁ qt v₀ v₁
  let motive₂ :
      (a : CapturedVarEnv) → (a_1 a_2 : VarEnv) → agreeCapturedEnv predSat R μ₀ μ₁ θ₀ θ₁ a a_1 a_2 → Prop :=
    fun σcap ρcap₀ ρcap₁ _ =>
      agreeCapturedEnv predSat R' μ₀ μ₁ θ₀ θ₁ σcap ρcap₀ ρcap₁
  have htransport : motive₂ σcap ρcap₀ ρcap₁ hcap :=
    agreeCapturedEnv.rec (predSat := predSat) (R := R) (μ₁ := μ₀) (μ₂ := μ₁) (θ₁ := θ₀) (θ₂ := θ₁)
      (motive_1 := motive₁) (motive_2 := motive₂)
      (clean_eq_nonref_nonarrow := by
        intro qt v₀ v₁ hpoison hnotfun hnotref heq hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_eq_nonref_nonarrow hpoison hnotfun hnotref heq))
      (clean_internal_arrow := by
        intro st1 st2 p tcls qt tcl x body σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ _ihcap
          hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_internal_arrow hclean_internal hetyp htcl hmatch hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁))
      (clean_internal_arrow_extern := by
        intro id x y argTyp _argPoison _argPred retSpec effects p tcls qt tcl σcap _argQTyp ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ _ihcap
          hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_internal_arrow_extern hclean_internal hetyp htcl hmatch hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁))
      (dirty_internal_arrow := by
        intro qt v₀ v₁ hdirty_internal hisArrow htyp1 htyp2 hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.dirty_internal_arrow hdirty_internal hisArrow htyp1 htyp2))
      (clean_internal_parrow := by
        intro st1 st2 p tcls qt tcl x body pbody σcap ρcap₀ ρcap₁ v₀ v₁ hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ _ihcap
          hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_internal_parrow hclean_internal hetyp htcl hmatch hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁))
      (clean_internal_parrow_extern := by
        intro id x y argTyp _argPoison _argPred retSpec p tcls qt tcl σcap _argQTyp ρcap₀ ρcap₁ v₀ v₁
          hclean_internal hetyp htcl hmatch hcap
          hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁ _ihcap
          hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_internal_parrow_extern hclean_internal hetyp htcl hmatch hcap
            hmemberVars₀ hmemberCvcr₀ hmemberVars₁ hmemberCvcr₁ htyping₀ htyping₁ hv₀ hv₁))
      (dirty_internal_parrow := by
        intro qt v₀ v₁ hdirty_internal hisParrow htyp1 htyp2 hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.dirty_internal_parrow hdirty_internal hisParrow htyp1 htyp2))
      (clean_ref := by
        intro ls l a₀ a₁ qt v₀ v₁ hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁ hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.clean_ref hpoison hetyp hlookup1 hin hv₀ hlookup2 hv₁))
      (withPred_true_eq := by
        intro k qt v₀ v₁ htag hreg hnotfun hnotref heq hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.withPred_true_eq k htag hreg hnotfun hnotref heq))
      (withPred_true_ref := by
        intro k ls l a₀ a₁ qt v₀ v₁ htag hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁ hclean
        exact agreeValueUnder_clean_transport_by_cleanBack h_clean_back
          hmemberVars₀_transport hmemberCvcr₀_transport
          hmemberVars₁_transport hmemberCvcr₁_transport hclean
          (agreeValueUnder.withPred_true_ref k htag hreg hetyp hlookup1 hin hv₀ hlookup2 hv₁))
      (nil := by
        intro ρcap₀ ρcap₁
        exact agreeCapturedEnv.nil)
      (cons_clean := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ _hcleanR hlookup1 hlookup2 htyp1 htyp2 hagree _htail ihagree ihtail
        by_cases hcleanR' : qtypCleanUnder R' qt
        · exact agreeCapturedEnv.cons_clean hcleanR' hlookup1 hlookup2 htyp1 htyp2 (ihagree hcleanR') ihtail
        · exact agreeCapturedEnv.cons_dirty hcleanR' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      (cons_dirty := by
        intro x qt σcap ρcap₀ ρcap₁ v₀ v₁ hdirty hlookup1 hlookup2 htyp1 htyp2 _htail ihtail
        have hdirty' : ¬ qtypCleanUnder R' qt := by
          intro hcleanR'
          exact hdirty (h_clean_back qt hcleanR')
        exact agreeCapturedEnv.cons_dirty hdirty' hlookup1 hlookup2 htyp1 htyp2 ihtail)
      hcap
  exact htransport

-- Member-oriented transport for closureCapturedVarsRegime across joinTypeResults.
private lemma joinTypeResults_closure_cvcr_transport_from_member
  (predSat : PredSat) (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult)
  (res : TypeResult) (R : Regime) (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (hcap_src : closureCapturedVarsRegime predSat R src.qualType μ θ v) :
  closureCapturedVarsRegime predSat R res.qualType μ θ v := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        closureCapturedVarsRegime predSat R ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' hcompat hfold hcap_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        simpa using hcap_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcap_acc1 :
                closureCapturedVarsRegime predSat R ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
              have hstep :=
                closureCapturedVarsRegime_joinETyps_step
                  predSat R μ θ v acc.1 resEtyp acc.2.2.1 resPoison acc.2.2.2.1 resPred
                  hcompat_x hcap_acc
              simpa [acc1] using hstep
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            exact ih (acc := acc1) hcompat_tail hfold_tail hcap_acc1
  have h_fold_member_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        closureCapturedVarsRegime predSat R src'.qualType μ θ v →
        closureCapturedVarsRegime predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hcap_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hcap_acc1 :
                  closureCapturedVarsRegime predSat R
                    ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
                have hstep :=
                  closureCapturedVarsRegime_joinETyps_step_right
                    predSat R μ θ v acc.1 resEtyp acc.2.2.1 resPoison acc.2.2.2.1 resPred
                    hcompat_x (by simpa [hqx] using hcap_src')
                simpa [acc1] using hstep
              exact h_fold_left_cvcr xs acc1 acc' hcompat_tail hfold_tail hcap_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src')
                hcompat_tail hfold_tail hsrc_tail hcap_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at _h_join
          contradiction
      | ok _ =>
          erw [hcheck] at _h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at _h_join
              contradiction
          | ok a =>
              erw [hfold] at _h_join
              have heq := Except.ok.inj _h_join
              have hetyp_res : (⟨a.1, a.2.2.1, a.2.2.2.1⟩ : QTyp).etyp = res.qualType.etyp := by
                exact congrArg (fun tr => tr.qualType.etyp) heq
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hcap_a :
                    closureCapturedVarsRegime predSat R ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_left_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a hcompat hfold (by simpa [hqt] using hcap_src)
                exact closureCapturedVarsRegime_transport_etyp hetyp_res hcap_a
              · have hcap_a :
                    closureCapturedVarsRegime predSat R ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_member_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv',
                      first.regime', first.nextLoc', first.nextTag')
                    a src hcompat hfold hsrc_tail hcap_src
                exact closureCapturedVarsRegime_transport_etyp hetyp_res hcap_a

-- If the joined result predicate is a guardClosure, every contributing member keeps that exact predicate.
private lemma joinTypeResults_pred_eq_guardClosure_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (h_join : joinTypeResults ctx first rest = .ok res)
  (hmem_src : src ∈ first :: rest)
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv}
  (hpred_res : res.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  src.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_pred :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
        acc.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' hfold hpred_out
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hpred_out
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
            have hpred_acc1 : acc1.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
              ih (acc := acc1) hfold_tail
            have hjoin :
                joinPredicates acc.2.2.2.1 resPred = Predicate.guardClosure k arg_name pred_body var_env := by
              simpa [acc1] using hpred_acc1
            exact (joinPredicates_eq_guardClosure (p := acc.2.2.2.1) (q := resPred) hjoin).1
  have h_fold_member_pred :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env →
        src'.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' src' hfold hmem_src' hpred_out
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
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
            have hpred_acc1 : acc1.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
              h_fold_left_pred xs acc1 acc' hfold_tail hpred_out
            have hjoin :
                joinPredicates acc.2.2.2.1 resPred = Predicate.guardClosure k arg_name pred_body var_env := by
              simpa [acc1] using hpred_acc1
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              simpa [hqx] using
                (joinPredicates_eq_guardClosure (p := acc.2.2.2.1) (q := resPred) hjoin).2
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail hpred_out
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at h_join
          contradiction
      | ok _ =>
          erw [hcheck] at h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at h_join
              contradiction
          | ok a =>
              erw [hfold] at h_join
              have heq := Except.ok.inj h_join
              have hpred_match :
                  (match a.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => a.2.2.2.1) =
                    Predicate.guardClosure k arg_name pred_body var_env := by
                calc
                  (match a.1 with
                  | ETyp.arrow _ _ _ _ => Predicate.noPred
                  | ETyp.parrow _ _ _ _ => Predicate.noPred
                  | _ => a.2.2.2.1)
                      = res.qualType.pred := by
                        exact congrArg (fun tr => tr.qualType.pred) heq
                  _ = Predicate.guardClosure k arg_name pred_body var_env := hpred_res
              have hpred_a : a.2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env := by
                cases ha1 : a.1 <;> simp [ha1] at hpred_match <;> exact hpred_match
              rcases (List.mem_cons.mp hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hpred_first :
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag').2.2.2.1 = Predicate.guardClosure k arg_name pred_body var_env :=
                  h_fold_left_pred
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold hpred_a
                simpa [hqt] using hpred_first
              · exact h_fold_member_pred
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a src hfold hsrc_tail hpred_a

-- Member-oriented companions for `joinTypeResults` lookup compatibility.
-- These are the target interface for `stepFR_app`; proofs are staged and can be
-- completed incrementally after wiring.
lemma joinTypeResults_transport_valueConsistentWithRegime_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : valueConsistentWithRegime predSat (ctxAfter ctx src).regime src.qualType μ θ v) :
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  have hcap_src :
      closureCapturedVarsRegime predSat (ctxAfter ctx src).regime src.qualType μ θ v :=
    valueConsistentWithRegime_closureCapturedVarsRegime h_src
  have hcap_src_resR :
      closureCapturedVarsRegime predSat (ctxAfter ctx res).regime src.qualType μ θ v :=
    closureCapturedVarsRegime_transport_lookup_back
      (predSat := predSat)
      (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
      (qt := src.qualType) (μ := μ) (θ := θ) (v := v)
      hlookup_back hcap_src
  have hcap_res :
      closureCapturedVarsRegime predSat (ctxAfter ctx res).regime res.qualType μ θ v :=
    joinTypeResults_closure_cvcr_transport_from_member
      (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (R := (ctxAfter ctx res).regime) (μ := μ) (θ := θ) (v := v)
      _h_join _hmem_src hcap_src_resR
  cases hpred_res : res.qualType.pred with
  | noPred =>
      exact valueConsistentWithRegime.noTag
        (show qtypGuardTag res.qualType = none by simp [qtypGuardTag, hpred_res])
        hcap_res
  | guardOnly k =>
      exact valueConsistentWithRegime.guardOnly_ok k hpred_res hcap_res
  | guardClosure k arg_name pred_body var_env =>
      have hpred_src :
          src.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env :=
        joinTypeResults_pred_eq_guardClosure_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src hpred_res
      have hpred_eq : src.qualType.pred = res.qualType.pred := by
        simpa [hpred_res] using hpred_src
      have htag_res : qtypGuardTag res.qualType = some k := by
        simp [qtypGuardTag, hpred_res]
      cases hlookupR : (ctxAfter ctx res).regime.lookup? k with
      | none =>
          exact valueConsistentWithRegime.notInRegime k htag_res hlookupR hcap_res
      | some b =>
          have hlookup_src :
              (ctxAfter ctx src).regime.lookup? k = some b := hlookup_back k b hlookupR
          have hcons_src :
              (b = true → qtypPredHolds predSat src.qualType μ v) ∧
              (b = false → ¬ qtypPredHolds predSat src.qualType μ v) :=
            valueConsistentWithRegime_guardClosure_consistency
              (predSat := predSat) (R := (ctxAfter ctx src).regime)
              (qt := src.qualType) (μ := μ) (v := v)
              (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
              (b := b) h_src hpred_src hlookup_src
          cases b with
          | false =>
              have hnot_src : ¬ qtypPredHolds predSat src.qualType μ v := hcons_src.2 rfl
              have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                qtypPredHolds_transport_pred_not
                  (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                  (μ := μ) (v := v) hpred_eq hnot_src
              exact valueConsistentWithRegime.inRegimeFalse k htag_res hlookupR hnot_res hcap_res
          | true =>
              have hholds_src : qtypPredHolds predSat src.qualType μ v := hcons_src.1 rfl
              have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                qtypPredHolds_transport_pred
                  (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                  (μ := μ) (v := v) hpred_eq hholds_src
              exact valueConsistentWithRegime.inRegimeTrue k htag_res hlookupR hholds_res hcap_res

private lemma etyp_isFunctionType_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isFunctionType = t2.isFunctionType := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hsig ⊢

private lemma etyp_isArrow_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isArrow = t2.isArrow := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isArrow] at hsig ⊢

private lemma etyp_isParrow_eq_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true) :
  t1.isParrow = t2.isParrow := by
  cases t1 <;> cases t2 <;> simp [beqETypSignature, ETyp.isParrow] at hsig ⊢

private lemma etyp_not_ref_left_of_beqSignature_true
  {t1 t2 : ETyp}
  (hsig : beqETypSignature t1 t2 = true)
  (hnotref_right : ¬ ∃ ls, t2 = ETyp.ref ls) :
  ¬ ∃ ls, t1 = ETyp.ref ls := by
  intro href_left
  rcases href_left with ⟨ls, ht1⟩
  subst ht1
  cases t2 <;> simp [beqETypSignature] at hsig
  case ref ls2 =>
    exact hnotref_right ⟨ls2, rfl⟩


private lemma joinTypeResults_qualType_etyp_signature_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest) :
  beqETypSignature res.qualType.etyp src.qualType.etyp = true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_sig_invariant :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        ∀ t, beqETypSignature acc.1 t = beqETypSignature acc'.1 t := by
    intro rs' acc acc' hcompat hfold
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        intro t
        rfl
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hinv_tail := ih (acc := acc1) hcompat_tail hfold_tail
            intro t
            calc
              beqETypSignature acc.1 t = beqETypSignature acc1.1 t := by
                simpa [acc1] using
                  (beqETypSignature_joinETyps_left
                    (t1 := acc.1) (t2 := resEtyp) (t3 := t)
                    (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x)
              _ = beqETypSignature acc'.1 t := hinv_tail t
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              have hinv :=
                h_fold_sig_invariant
                  rest
                  (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                    first.nextTag')
                  a hcompat hfold
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hself : beqETypSignature etyp etyp = true :=
                  beqETypSignature_refl etyp
                have : beqETypSignature a.1 etyp = true := by
                  have hinv' := hinv etyp
                  simpa [hself] using hinv'.symm
                simpa [ctxAfter, hqt] using this
              · have hsrc_compat : beqETypSignature etyp src.qualType.etyp = true := hcompat src hsrc_rest
                have : beqETypSignature a.1 src.qualType.etyp = true := by
                  have hinv' := hinv src.qualType.etyp
                  simpa [hsrc_compat] using hinv'.symm
                simpa [ctxAfter] using this

private lemma joinTypeResults_qualType_poison_imp_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest) :
  res.qualType.poison = false → src.qualType.poison = false := by
  intro hpoison_res
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_poison :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.2.1 = false →
        acc.2.2.1 = false := by
    intro rs' acc acc' hfold hpoison_out
    induction rs' generalizing acc acc' with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hpoison_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hpoison_acc1 : acc1.2.2.1 = false :=
              ih (acc := acc1) (acc' := acc') hfold_tail hpoison_out
            have : joinPoison acc.2.2.1 resPoison = false := by
              simpa [acc1] using hpoison_acc1
            exact (joinPoison_eq_false this).1
  have h_fold_member_poison :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.2.1 = false →
        src'.qualType.poison = false := by
    intro rs' acc acc' src' hfold hmem_src' hpoison_out
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hpoison_acc1 : acc1.2.2.1 = false :=
                h_fold_left_poison xs acc1 acc' hfold_tail hpoison_out
              have : joinPoison acc.2.2.1 resPoison = false := by
                simpa [acc1] using hpoison_acc1
              have hresPoison : resPoison = false := (joinPoison_eq_false this).2
              simpa [hqx] using hresPoison
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail hpoison_out
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hpoison_match :
                  joinPoison ctx.pc a.2.2.1 = false := by
                simpa using hpoison_res
              have hpoison_a : a.2.2.1 = false := (joinPoison_eq_false hpoison_match).2
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hfirst_poison : poison = false :=
                  h_fold_left_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold hpoison_a
                simpa [hqt] using hfirst_poison
              · exact
                  h_fold_member_poison
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hfold hsrc_rest hpoison_a

private lemma joinTypeResults_qualType_guardTag_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {k : Tag}
  (htag_res : qtypGuardTag res.qualType = some k) :
  qtypGuardTag src.qualType = some k := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_guardTag :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs' = .ok acc' →
        predGuardTag acc'.2.2.2.1 = some k →
        predGuardTag acc.2.2.2.1 = some k := by
    intro rs' acc acc' hfold htag_out
    induction rs' generalizing acc acc' with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact htag_out
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have htag_acc1 : predGuardTag acc1.2.2.2.1 = some k :=
              ih (acc := acc1) (acc' := acc') hfold_tail htag_out
            have hjoin : predGuardTag (joinPredicates acc.2.2.2.1 resPred) = some k := by
              simpa [acc1] using htag_acc1
            exact (predGuardTag_joinPredicates (p := acc.2.2.2.1) (q := resPred) (k := k) hjoin).1
  have h_fold_member_guardTag :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        predGuardTag acc'.2.2.2.1 = some k →
        qtypGuardTag src'.qualType = some k := by
    intro rs' acc acc' src' hfold hmem_src' htag_out
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have htag_acc1 : predGuardTag acc1.2.2.2.1 = some k :=
              h_fold_left_guardTag xs acc1 acc' hfold_tail htag_out
            have hjoin : predGuardTag (joinPredicates acc.2.2.2.1 resPred) = some k := by
              simpa [acc1] using htag_acc1
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have htag_resPred : predGuardTag resPred = some k :=
                (predGuardTag_joinPredicates (p := acc.2.2.2.1) (q := resPred) (k := k) hjoin).2
              simpa [hqx, qtypGuardTag, predGuardTag] using htag_resPred
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hfold_tail hsrc_tail htag_out
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have htag_match :
                  predGuardTag
                    (match a.1 with
                    | ETyp.arrow _ _ _ _ => Predicate.noPred
                    | ETyp.parrow _ _ _ _ => Predicate.noPred
                    | _ => a.2.2.2.1) = some k := by
                simpa [qtypGuardTag, predGuardTag] using htag_res
              have htag_a : predGuardTag a.2.2.2.1 = some k := by
                cases ha1 : a.1 <;> simp [ha1, predGuardTag] at htag_match <;> exact htag_match
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have htag_first :
                    predGuardTag pred = some k :=
                  h_fold_left_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hfold htag_a
                simpa [hqt, qtypGuardTag, predGuardTag] using htag_first
              · exact
                  h_fold_member_guardTag
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hfold hsrc_rest htag_a

private lemma joinTypeResults_qualType_clean_compat_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime res.qualType) :
  qtypCleanUnder (ctxAfter ctx src).regime src.qualType := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_qualType_poison_imp_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src hpoison)
  | guard k htag hreg hnotfun =>
      have htag_src :
          qtypGuardTag src.qualType = some k :=
        joinTypeResults_qualType_guardTag_compat_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src htag
      have hreg_src :
          (ctxAfter ctx src).regime.lookup? k = some true :=
        joinTypeResults_lookup_member_regime_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src k true hreg
      have hsig :
          beqETypSignature res.qualType.etyp src.qualType.etyp = true :=
        joinTypeResults_qualType_etyp_signature_compat_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src
      have hfunEq :
          res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType :=
        etyp_isFunctionType_eq_of_beqSignature_true hsig
      have hnotfun_src : src.qualType.etyp.isFunctionType = false := by
        calc
          src.qualType.etyp.isFunctionType = res.qualType.etyp.isFunctionType := by
            simpa using hfunEq.symm
          _ = false := hnotfun
      exact qtypCleanUnder.guard k htag_src hreg_src hnotfun_src


private lemma joinETyps_preserves_dirty_arrow_right
    {t1 : ETyp} {st1 st2 : Typ} {tcls2 : List FnTClosure}
    {p1 p1' p2' : Poison}
    (hcompat : beqETypSignature t1 (ETyp.arrow st1 st2 p1 tcls2) = true)
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps t1 (ETyp.arrow st1 st2 p1 tcls2) p1' p2') = some true := by
  subst hDirty
  cases t1 with
  | arrow st1' st2' pL tclsL =>
      simp only [beqETypSignature] at hcompat
      have hshape : (st1' == st1 && st2' == st2) = true := hcompat
      simp [joinETyps, hshape, getInternalPoison, joinPoison]
  | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
      simp [beqETypSignature] at hcompat

private lemma joinETyps_preserves_dirty_parrow_right
    {t1 : ETyp} {st1 st2 : Typ} {tcls2 : List PFnTClosure}
    {p1 p1' p2' : Poison}
    (hcompat : beqETypSignature t1 (ETyp.parrow st1 st2 p1 tcls2) = true)
    (hDirty : p1 = true) :
    getInternalPoison (joinETyps t1 (ETyp.parrow st1 st2 p1 tcls2) p1' p2') = some true := by
  subst hDirty
  cases t1 with
  | parrow st1' st2' pL tclsL =>
      simp only [beqETypSignature] at hcompat
      have hshape : (st1' == st1 && st2' == st2) = true := hcompat
      simp [joinETyps, hshape, getInternalPoison, joinPoison]
  | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
      simp [beqETypSignature] at hcompat


private lemma joinTypeResults_qualType_getInternalPoison_true_from_member_arrow
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {tcls : List FnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.arrow st1 st2 true tcls) :
  getInternalPoison res.qualType.etyp = some true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.1.isArrow = true →
        getInternalPoison acc.1 = some true →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' hcompat hfold hisArrow_acc hdirty_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hdirty_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hsig_acc1_acc : beqETypSignature acc1.1 acc.1 = true := by
              have htmp :
                  beqETypSignature acc.1 acc.1 =
                    beqETypSignature (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) acc.1 :=
                beqETypSignature_joinETyps_left
                  (t1 := acc.1) (t2 := resEtyp) (t3 := acc.1)
                  (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x
              have hself : beqETypSignature acc.1 acc.1 = true := beqETypSignature_refl acc.1
              simpa [acc1, hself] using htmp
            have hisArrow_acc1 : acc1.1.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hsig_acc1_acc
              calc
                acc1.1.isArrow = acc.1.isArrow := by simpa using hEq
                _ = true := hisArrow_acc
            have hdirty_acc1 : getInternalPoison acc1.1 = some true := by
              cases hacc : acc.1 with
              | arrow st1' st2' p' tcls' =>
                  have hptrue : p' = true := by
                    simpa [hacc, getInternalPoison] using hdirty_acc
                  have hdirty' :
                      getInternalPoison
                        (joinETyps (ETyp.arrow st1' st2' p' tcls') resEtyp acc.2.2.1 resPoison) = some true :=
                    joinETyps_preserves_dirty_arrow
                      (st1 := st1') (st2 := st2') (p1 := p') (tcls1 := tcls')
                      (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison) hptrue
                  simpa [acc1, hacc] using hdirty'
              | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                  simp [ETyp.isArrow, hacc] at hisArrow_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hisArrow_acc1 hdirty_acc1
  have h_fold_member_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.arrow st1 st2 true tcls →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hetyp_resEtyp : resEtyp = ETyp.arrow st1 st2 true tcls := by
                simpa [hqx] using hetyp_src'
              have hdirty_acc1 :
                  getInternalPoison acc1.1 = some true := by
                have hdirty' :
                    getInternalPoison (joinETyps acc.1 (ETyp.arrow st1 st2 true tcls) acc.2.2.1 resPoison) = some true :=
                  joinETyps_preserves_dirty_arrow_right
                    (t1 := acc.1) (st1 := st1) (st2 := st2) (tcls2 := tcls)
                    (p1 := true) (p1' := acc.2.2.1) (p2' := resPoison)
                    (by simpa [hetyp_resEtyp] using hcompat_x) rfl
                simpa [acc1, hqx, hetyp_resEtyp] using hdirty'
              exact h_fold_left_dirty xs acc1 acc' hcompat_tail hfold_tail
                (by
                  have hsig_acc1_src : beqETypSignature acc1.1 (ETyp.arrow st1 st2 true tcls) = true := by
                    have htmp :
                        beqETypSignature acc.1 (ETyp.arrow st1 st2 true tcls) =
                          beqETypSignature
                            (joinETyps acc.1 (ETyp.arrow st1 st2 true tcls) acc.2.2.1 resPoison)
                            (ETyp.arrow st1 st2 true tcls) :=
                      beqETypSignature_joinETyps_left
                        (t1 := acc.1) (t2 := ETyp.arrow st1 st2 true tcls)
                        (t3 := ETyp.arrow st1 st2 true tcls)
                        (p1 := acc.2.2.1) (p2 := resPoison)
                        (by simpa [hetyp_resEtyp] using hcompat_x)
                    have hlhs : beqETypSignature acc.1 (ETyp.arrow st1 st2 true tcls) = true := by
                      simpa [hetyp_resEtyp] using hcompat_x
                    simpa [hqx, hetyp_resEtyp, acc1, hlhs] using htmp
                  have hEq := etyp_isArrow_eq_of_beqSignature_true hsig_acc1_src
                  simpa [ETyp.isArrow] using hEq)
                hdirty_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hetyp_first : etyp = ETyp.arrow st1 st2 true tcls := by
                  simpa [hqt] using hetyp_src
                have hisArrow_first : etyp.isArrow = true := by
                  simp [hetyp_first, ETyp.isArrow]
                have hdirty_first : getInternalPoison etyp = some true := by
                  simp [hetyp_first, getInternalPoison]
                exact
                  h_fold_left_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold hisArrow_first hdirty_first
              · exact
                  h_fold_member_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    (by simpa [ctxAfter] using hetyp_src)

private lemma joinTypeResults_qualType_getInternalPoison_true_from_member_parrow
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {tcls : List PFnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.parrow st1 st2 true tcls) :
  getInternalPoison res.qualType.etyp = some true := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        acc.1.isParrow = true →
        getInternalPoison acc.1 = some true →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' hcompat hfold hisParrow_acc hdirty_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        simpa using hdirty_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hsig_acc1_acc : beqETypSignature acc1.1 acc.1 = true := by
              have htmp :
                  beqETypSignature acc.1 acc.1 =
                    beqETypSignature (joinETyps acc.1 resEtyp acc.2.2.1 resPoison) acc.1 :=
                beqETypSignature_joinETyps_left
                  (t1 := acc.1) (t2 := resEtyp) (t3 := acc.1)
                  (p1 := acc.2.2.1) (p2 := resPoison) hcompat_x
              have hself : beqETypSignature acc.1 acc.1 = true := beqETypSignature_refl acc.1
              simpa [acc1, hself] using htmp
            have hisParrow_acc1 : acc1.1.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hsig_acc1_acc
              calc
                acc1.1.isParrow = acc.1.isParrow := by simpa using hEq
                _ = true := hisParrow_acc
            have hdirty_acc1 : getInternalPoison acc1.1 = some true := by
              cases hacc : acc.1 with
              | parrow st1' st2' p' tcls' =>
                  have hptrue : p' = true := by
                    simpa [hacc, getInternalPoison] using hdirty_acc
                  have hdirty' :
                      getInternalPoison
                        (joinETyps (ETyp.parrow st1' st2' p' tcls') resEtyp acc.2.2.1 resPoison) = some true :=
                    joinETyps_preserves_dirty_parrow
                      (st1 := st1') (st2 := st2') (p1 := p') (tcls1 := tcls')
                      (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison) hptrue
                  simpa [acc1, hacc] using hdirty'
              | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                  simp [ETyp.isParrow, hacc] at hisParrow_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hisParrow_acc1 hdirty_acc1
  have h_fold_member_dirty :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.parrow st1 st2 true tcls →
        getInternalPoison acc'.1 = some true := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hetyp_resEtyp : resEtyp = ETyp.parrow st1 st2 true tcls := by
                simpa [hqx] using hetyp_src'
              have hdirty_acc1 :
                  getInternalPoison acc1.1 = some true := by
                have hdirty' :
                    getInternalPoison (joinETyps acc.1 (ETyp.parrow st1 st2 true tcls) acc.2.2.1 resPoison) = some true :=
                  joinETyps_preserves_dirty_parrow_right
                    (t1 := acc.1) (st1 := st1) (st2 := st2) (tcls2 := tcls)
                    (p1 := true) (p1' := acc.2.2.1) (p2' := resPoison)
                    (by simpa [hetyp_resEtyp] using hcompat_x) rfl
                simpa [acc1, hqx, hetyp_resEtyp] using hdirty'
              exact h_fold_left_dirty xs acc1 acc' hcompat_tail hfold_tail
                (by
                  have hsig_acc1_src : beqETypSignature acc1.1 (ETyp.parrow st1 st2 true tcls) = true := by
                    have htmp :
                        beqETypSignature acc.1 (ETyp.parrow st1 st2 true tcls) =
                          beqETypSignature
                            (joinETyps acc.1 (ETyp.parrow st1 st2 true tcls) acc.2.2.1 resPoison)
                            (ETyp.parrow st1 st2 true tcls) :=
                      beqETypSignature_joinETyps_left
                        (t1 := acc.1) (t2 := ETyp.parrow st1 st2 true tcls)
                        (t3 := ETyp.parrow st1 st2 true tcls)
                        (p1 := acc.2.2.1) (p2 := resPoison)
                        (by simpa [hetyp_resEtyp] using hcompat_x)
                    have hlhs : beqETypSignature acc.1 (ETyp.parrow st1 st2 true tcls) = true := by
                      simpa [hetyp_resEtyp] using hcompat_x
                    simpa [hqx, hetyp_resEtyp, acc1, hlhs] using htmp
                  have hEq := etyp_isParrow_eq_of_beqSignature_true hsig_acc1_src
                  simpa [ETyp.isParrow] using hEq)
                hdirty_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have hetyp_first : etyp = ETyp.parrow st1 st2 true tcls := by
                  simpa [hqt] using hetyp_src
                have hisParrow_first : etyp.isParrow = true := by
                  simp [hetyp_first, ETyp.isParrow]
                have hdirty_first : getInternalPoison etyp = some true := by
                  simp [hetyp_first, getInternalPoison]
                exact
                  h_fold_left_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold hisParrow_first hdirty_first
              · exact
                  h_fold_member_dirty
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    (by simpa [ctxAfter] using hetyp_src)

private lemma joinTypeResults_qualType_ref_membership_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) {ls_src : LocSet}
  (hetyp_src : src.qualType.etyp = ETyp.ref ls_src)
  (hin_src : l ∈ ls_src) :
  ∃ ls_res, res.qualType.etyp = ETyp.ref ls_res ∧ l ∈ ls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_ref :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ ls, acc.1 = ETyp.ref ls ∧ l ∈ ls) →
        ∃ ls, acc'.1 = ETyp.ref ls ∧ l ∈ ls := by
    intro rs' acc acc' hcompat hfold href_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact href_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases href_acc with ⟨ls_acc, hacc_ref, hin_acc⟩
            have href_acc1 : ∃ ls, acc1.1 = ETyp.ref ls ∧ l ∈ ls := by
              cases hres : resEtyp with
              | ref ls2 =>
                  refine ⟨LocSet.union ls_acc ls2, ?_, ?_⟩
                  · simp [acc1, hacc_ref, hres, joinETyps]
                  · simpa [LocSet.union] using (Or.inl hin_acc : l ∈ ls_acc ∨ l ∈ ls2)
              | int | bool | unit | string | arrow _ _ _ _ | parrow _ _ _ _ =>
                  exfalso
                  simp [hacc_ref, hres, beqETypSignature] at hcompat_x
            exact ih (acc := acc1) hcompat_tail hfold_tail href_acc1
  have h_fold_member_ref :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        (∃ ls, src'.qualType.etyp = ETyp.ref ls ∧ l ∈ ls) →
        ∃ ls, acc'.1 = ETyp.ref ls ∧ l ∈ ls := by
    intro rs' acc acc' src' hcompat hfold hmem_src' href_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              rcases href_src' with ⟨ls_x, hetyp_x, hin_x⟩
              have hetyp_resEtyp : resEtyp = ETyp.ref ls_x := by
                simpa [hqx] using hetyp_x
              have href_acc1 : ∃ ls, acc1.1 = ETyp.ref ls ∧ l ∈ ls := by
                cases hacc : acc.1 with
                | ref ls_acc =>
                    subst resEtyp
                    refine ⟨LocSet.union ls_acc ls_x, ?_, ?_⟩
                    · simp [acc1, hacc, joinETyps]
                    · simpa [LocSet.union] using (Or.inr hin_x : l ∈ ls_acc ∨ l ∈ ls_x)
                | int | bool | unit | string | arrow _ _ _ _ | parrow _ _ _ _ =>
                    exfalso
                    simp [hacc, hetyp_resEtyp, beqETypSignature] at hcompat_x
              exact h_fold_left_ref xs acc1 acc' hcompat_tail hfold_tail href_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail href_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc | hsrc_rest
              · subst src
                have href_first : ∃ ls, etyp = ETyp.ref ls ∧ l ∈ ls := by
                  refine ⟨ls_src, ?_, hin_src⟩
                  simpa [hqt] using hetyp_src
                rcases h_fold_left_ref
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold href_first with ⟨ls_res, hetyp_res, hin_res⟩
                exact ⟨ls_res, by simpa [ctxAfter] using hetyp_res, hin_res⟩
              · rcases h_fold_member_ref
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_rest
                    ⟨ls_src, by simpa [ctxAfter] using hetyp_src, hin_src⟩
                  with ⟨ls_res, hetyp_res, hin_res⟩
                exact ⟨ls_res, by simpa [ctxAfter] using hetyp_res, hin_res⟩

private lemma joinTypeResults_qualType_arrow_member_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {p_src : Poison} {tcls_src : List FnTClosure} {tcl : FnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.arrow st1 st2 p_src tcls_src)
  (htcl_src : tcl ∈ tcls_src) :
  ∃ p_res tcls_res, res.qualType.etyp = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_arrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ p_acc tcls_acc, acc.1 = ETyp.arrow st1 st2 p_acc tcls_acc ∧ tcl ∈ tcls_acc) →
        ∃ p_res tcls_res, acc'.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' hcompat hfold harrow_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact harrow_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases harrow_acc with ⟨p_acc, tcls_acc, hacc_arrow, htcl_acc⟩
            have hisArrow_x : resEtyp.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hcompat_x
              calc
                resEtyp.isArrow = acc.1.isArrow := by
                  symm
                  simpa using hEq
                _ = true := by simp [hacc_arrow, ETyp.isArrow]
            rcases
                (joinETyps_arrow_structure
                  (st1 := st1) (st2 := st2) (p1 := p_acc) (tcls1 := tcls_acc)
                  (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison)
                  (by simpa [hacc_arrow] using hisArrow_x)
                  (by simpa [hacc_arrow] using hcompat_x))
              with ⟨p_acc1, tcls_acc1, hjoin_acc1, hmem_pres_left⟩
            have harrow_acc1 :
                ∃ p_mid tcls_mid, acc1.1 = ETyp.arrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
              refine ⟨p_acc1, tcls_acc1, ?_, ?_⟩
              · simpa [acc1, hacc_arrow] using hjoin_acc1
              · exact hmem_pres_left tcl htcl_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail harrow_acc1
  have h_fold_member_arrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.arrow st1 st2 p_src tcls_src →
        ∃ p_res tcls_res, acc'.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hsrc_resEtyp : resEtyp = ETyp.arrow st1 st2 p_src tcls_src := by
                simpa [hqx] using hetyp_src'
              have hisArrow_acc : acc.1.isArrow = true := by
                have hEq := etyp_isArrow_eq_of_beqSignature_true hcompat_x
                calc
                  acc.1.isArrow = resEtyp.isArrow := by
                    simpa using hEq
                  _ = true := by simp [hsrc_resEtyp, ETyp.isArrow]
              have harrow_acc1 :
                  ∃ p_mid tcls_mid, acc1.1 = ETyp.arrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
                cases hacc : acc.1 with
                | arrow st1l st2l pl tclsl =>
                    have hshape : (st1l == st1 && st2l == st2) = true := by
                      simpa [hacc, hsrc_resEtyp, beqETypSignature] using hcompat_x
                    have hshape_eq : st1l = st1 ∧ st2l = st2 := by
                      simpa using hshape
                    rcases hshape_eq with ⟨rfl, rfl⟩
                    refine ⟨joinPoison pl p_src, mergeFnTClosures tclsl tcls_src, ?_, ?_⟩
                    · simp [acc1, hacc, hsrc_resEtyp, joinETyps]
                    · exact mem_mergeFnTClosures_right tclsl tcls_src tcl htcl_src
                | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                    simp [ETyp.isArrow, hacc] at hisArrow_acc
              exact h_fold_left_arrow xs acc1 acc' hcompat_tail hfold_tail harrow_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have harrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_left_arrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold
                    ⟨p_src, tcls_src, by simpa [hqt] using hetyp_src, htcl_src⟩
                rcases harrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩
              · have harrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.arrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_member_arrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_tail
                    (by simpa [ctxAfter] using hetyp_src)
                rcases harrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩

private lemma joinTypeResults_qualType_parrow_member_from_member
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  {st1 st2 : Typ} {p_src : Poison} {tcls_src : List PFnTClosure} {tcl : PFnTClosure}
  (hetyp_src : src.qualType.etyp = ETyp.parrow st1 st2 p_src tcls_src)
  (htcl_src : tcl ∈ tcls_src) :
  ∃ p_res tcls_res, res.qualType.etyp = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
  let joinStep : (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_parrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        (∃ p_acc tcls_acc, acc.1 = ETyp.parrow st1 st2 p_acc tcls_acc ∧ tcl ∈ tcls_acc) →
        ∃ p_res tcls_res, acc'.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' hcompat hfold hparrow_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact hparrow_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases hparrow_acc with ⟨p_acc, tcls_acc, hacc_parrow, htcl_acc⟩
            have hisParrow_x : resEtyp.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hcompat_x
              calc
                resEtyp.isParrow = acc.1.isParrow := by
                  symm
                  simpa using hEq
                _ = true := by simp [hacc_parrow, ETyp.isParrow]
            rcases
                (joinETyps_parrow_structure
                  (st1 := st1) (st2 := st2) (p1 := p_acc) (tcls1 := tcls_acc)
                  (t2 := resEtyp) (p1' := acc.2.2.1) (p2' := resPoison)
                  (by simpa [hacc_parrow] using hisParrow_x)
                  (by simpa [hacc_parrow] using hcompat_x))
              with ⟨p_acc1, tcls_acc1, hjoin_acc1, hmem_pres_left⟩
            have hparrow_acc1 :
                ∃ p_mid tcls_mid, acc1.1 = ETyp.parrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
              refine ⟨p_acc1, tcls_acc1, ?_, ?_⟩
              · simpa [acc1, hacc_parrow] using hjoin_acc1
              · exact hmem_pres_left tcl htcl_acc
            exact ih (acc := acc1) hcompat_tail hfold_tail hparrow_acc1
  have h_fold_member_parrow :
      ∀ (rs' : List TypeResult) (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        src'.qualType.etyp = ETyp.parrow st1 st2 p_src tcls_src →
        ∃ p_res tcls_res, acc'.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hetyp_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
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
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hsrc_resEtyp : resEtyp = ETyp.parrow st1 st2 p_src tcls_src := by
                simpa [hqx] using hetyp_src'
              have hisParrow_acc : acc.1.isParrow = true := by
                have hEq := etyp_isParrow_eq_of_beqSignature_true hcompat_x
                calc
                  acc.1.isParrow = resEtyp.isParrow := by
                    simpa using hEq
                  _ = true := by simp [hsrc_resEtyp, ETyp.isParrow]
              have hparrow_acc1 :
                  ∃ p_mid tcls_mid, acc1.1 = ETyp.parrow st1 st2 p_mid tcls_mid ∧ tcl ∈ tcls_mid := by
                cases hacc : acc.1 with
                | parrow st1l st2l pl tclsl =>
                    have hshape : (st1l == st1 && st2l == st2) = true := by
                      simpa [hacc, hsrc_resEtyp, beqETypSignature] using hcompat_x
                    have hshape_eq : st1l = st1 ∧ st2l = st2 := by
                      simpa using hshape
                    rcases hshape_eq with ⟨rfl, rfl⟩
                    refine ⟨joinPoison pl p_src, mergePFnTClosures tclsl tcls_src, ?_, ?_⟩
                    · simp [acc1, hacc, hsrc_resEtyp, joinETyps]
                    · exact mem_mergePFnTClosures_right tclsl tcls_src tcl htcl_src
                | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                    simp [ETyp.isParrow, hacc] at hisParrow_acc
              exact h_fold_left_parrow xs acc1 acc' hcompat_tail hfold_tail hparrow_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src') hcompat_tail hfold_tail hsrc_tail hetyp_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hcompat := joinTypeResults_compat_ok etyp rest hcheck
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hparrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_left_parrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a hcompat hfold
                    ⟨p_src, tcls_src, by simpa [hqt] using hetyp_src, htcl_src⟩
                rcases hparrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩
              · have hparrow_a :
                    ∃ p_res tcls_res, a.1 = ETyp.parrow st1 st2 p_res tcls_res ∧ tcl ∈ tcls_res :=
                  h_fold_member_parrow
                    rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                      first.nextTag')
                    a src hcompat hfold hsrc_tail
                    (by simpa [ctxAfter] using hetyp_src)
                rcases hparrow_a with ⟨p_res, tcls_res, hetyp_a, htcl_res⟩
                exact ⟨p_res, tcls_res, by simpa [ctxAfter] using hetyp_a, htcl_res⟩

lemma joinTypeResults_transport_resultAgreesIfClean_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ₀ μ₁ : Memory) (θ₀ θ₁ : RealizationMap) (o₀ o₁ : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src :
    resultAgreesIfClean predSat (ctxAfter ctx src).regime
      μ₀ μ₁ θ₀ θ₁ src.qualType o₀ o₁) :
  resultAgreesIfClean predSat (ctxAfter ctx res).regime
    μ₀ μ₁ θ₀ θ₁ res.qualType o₀ o₁ := by
  intro hclean_res
  have hclean_src :
      qtypCleanUnder (ctxAfter ctx src).regime src.qualType :=
    joinTypeResults_qualType_clean_compat_from_member
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      _h_join _hmem_src hclean_res
  have hagree_src :
      agreeValueUnder predSat (ctxAfter ctx src).regime μ₀ μ₁ θ₀ θ₁ src.qualType o₀ o₁ :=
    h_src hclean_src
  have _hagree_src_keep := hagree_src
  have hsig :
      beqETypSignature res.qualType.etyp src.qualType.etyp = true :=
    joinTypeResults_qualType_etyp_signature_compat_from_member
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      _h_join _hmem_src
  have hfunEq :
      res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType :=
    etyp_isFunctionType_eq_of_beqSignature_true hsig
  cases hagree_src with
  | clean_eq_nonref_nonarrow hpoison_src hnotfun_src hnotref_src hEq =>
      cases hclean_res with
      | clean hpoison_res =>
          have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = false := hnotfun_src
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref_res hEq
      | guard k htag hreg hnotfun_res =>
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun_res hnotref_res hEq
  | withPred_true_eq _ _ _ hnotfun_src hnotref_src hEq =>
      cases hclean_res with
      | clean hpoison_res =>
          have hnotfun_res : res.qualType.etyp.isFunctionType = false := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = false := hnotfun_src
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.clean_eq_nonref_nonarrow hpoison_res hnotfun_res hnotref_res hEq
      | guard k htag hreg hnotfun_res =>
          have hnotref_res : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
            exact etyp_not_ref_left_of_beqSignature_true hsig hnotref_src
          exact agreeValueUnder.withPred_true_eq k htag hreg hnotfun_res hnotref_res hEq
  | @clean_internal_arrow st1 st2 p tcls _qt tcl x body σcap ρcap₀ ρcap₁ _v₀ _v₁
      hclean_internal_src hetyp_src htcl hmatch hcap
      hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src
      htyping₀_src htyping₁_src hv₁ hv₂ =>
      cases hclean_res with
      | clean _hpoison_res =>
          have hlookup_back :
              ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                (ctxAfter ctx src).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src k b hk
          have hlookup_true_back :
              ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                (ctxAfter ctx src).regime.lookup? k = some true := by
            intro k hk
            exact hlookup_back k true hk
          have hcap_res :=
            agreeCapturedEnv_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              hlookup_true_back
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              hcap
          have hmemberVars₀_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberVars₀_src
          have hmemberCvcr₀_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberCvcr₀_src
          have hmemberVars₁_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberVars₁_src
          have hmemberCvcr₁_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberCvcr₁_src
          rcases
              joinTypeResults_qualType_arrow_member_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src hetyp_src htcl
            with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
          by_cases hclean_internal_res : internalPoisonClean res.qualType
          · exact agreeValueUnder.clean_internal_arrow hclean_internal_res hetyp_res htcl_res hmatch hcap_res
              hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res
              htyping₀_src htyping₁_src hv₁ hv₂
          · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
              have htyped_closure :
                  valueHasETyp θ₀ (Value.closure x body ρcap₀) (ETyp.arrow st1 st2 p tcls) := by
                have htcl_match : FnTClosure.regular x body σcap ∈ tcls := by
                  simpa [hmatch] using htcl
                refine valueHasETyp.closure (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₀.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₁] using htyped_closure
            have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
              have htyped_closure :
                  valueHasETyp θ₁ (Value.closure x body ρcap₁) (ETyp.arrow st1 st2 p tcls) := by
                have htcl_match : FnTClosure.regular x body σcap ∈ tcls := by
                  simpa [hmatch] using htcl
                refine valueHasETyp.closure (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₁.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₂] using htyped_closure
            have htyp1_res :
                valueHasETyp θ₀ o₀ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
            have htyp2_res :
                valueHasETyp θ₁ o₁ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
            have hisArrow_src : src.qualType.etyp.isArrow = true := by
              simp [hetyp_src, ETyp.isArrow]
            have hisArrow_res : res.qualType.etyp.isArrow = true := by
              have hEq := etyp_isArrow_eq_of_beqSignature_true hsig
              calc
                res.qualType.etyp.isArrow = src.qualType.etyp.isArrow := hEq
                _ = true := hisArrow_src
            exact agreeValueUnder.dirty_internal_arrow hclean_internal_res hisArrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
    | @clean_internal_arrow_extern id x y argTyp argPoison argPred retSpec effects p tcls _qt tcl σcap argQTyp ρcap₀ ρcap₁ _v₀ _v₁
        hclean_internal_src hetyp_src htcl hmatch hcap
        hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src
        htyping₀_src htyping₁_src hv₁ hv₂ =>
        cases hclean_res with
        | clean _hpoison_res =>
            have hlookup_back :
                ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                  (ctxAfter ctx src).regime.lookup? k = some b := by
              intro k b hk
              exact
                joinTypeResults_lookup_member_regime_compat
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  _h_join _hmem_src k b hk
            have hlookup_true_back :
                ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                  (ctxAfter ctx src).regime.lookup? k = some true := by
              intro k hk
              exact hlookup_back k true hk
            have hcap_res :=
              agreeCapturedEnv_transport_by_lookupTrueBack
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
                hlookup_true_back
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₀) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₀) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₁) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₁) hlookup_back h)
                hcap
            have hmemberVars₀_res :=
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₀) hlookup_back hmemberVars₀_src
            have hmemberCvcr₀_res :=
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₀) hlookup_back hmemberCvcr₀_src
            have hmemberVars₁_res :=
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₁) hlookup_back hmemberVars₁_src
            have hmemberCvcr₁_res :=
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₁) hlookup_back hmemberCvcr₁_src
            rcases
                joinTypeResults_qualType_arrow_member_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  _h_join _hmem_src hetyp_src htcl
              with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
            by_cases hclean_internal_res : internalPoisonClean res.qualType
            · exact agreeValueUnder.clean_internal_arrow_extern hclean_internal_res hetyp_res htcl_res hmatch hcap_res
                hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res
                htyping₀_src htyping₁_src hv₁ hv₂
            · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
                have htyped_closure :
                    valueHasETyp θ₀
                      (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec effects) ρcap₀)
                      (ETyp.arrow argTyp (parseReturnType retSpec) p tcls) := by
                  have htcl_match : FnTClosure.extern id x retSpec effects σcap argQTyp ∈ tcls := by
                    simpa [hmatch] using htcl
                  refine valueHasETyp.closure_extern (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                  · intro y' qt_y v_y hlookup_σ hlookup_ρ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v', hlookup_ρ', htyp'⟩
                    have hv_eq : v' = v_y := by
                      have : some v' = some v_y := by
                        calc
                          some v' = ρcap₀.lookup y' := by simpa using hlookup_ρ'.symm
                          _ = some v_y := by simpa using hlookup_ρ
                      exact Option.some.inj this
                    subst hv_eq
                    exact htyp'
                  · intro y' qt_y hlookup_σ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v, hlookup_ρ, _htyp⟩
                    exact ⟨v, hlookup_ρ⟩
                simpa [hetyp_src, hv₁] using htyped_closure
              have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
                have htyped_closure :
                    valueHasETyp θ₁
                      (Value.closure x (Expr.externFn id y argTyp argPoison argPred retSpec effects) ρcap₁)
                      (ETyp.arrow argTyp (parseReturnType retSpec) p tcls) := by
                  have htcl_match : FnTClosure.extern id x retSpec effects σcap argQTyp ∈ tcls := by
                    simpa [hmatch] using htcl
                  refine valueHasETyp.closure_extern (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                  · intro y' qt_y v_y hlookup_σ hlookup_ρ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v', hlookup_ρ', htyp'⟩
                    have hv_eq : v' = v_y := by
                      have : some v' = some v_y := by
                        calc
                          some v' = ρcap₁.lookup y' := by simpa using hlookup_ρ'.symm
                          _ = some v_y := by simpa using hlookup_ρ
                      exact Option.some.inj this
                    subst hv_eq
                    exact htyp'
                  · intro y' qt_y hlookup_σ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v, hlookup_ρ, _htyp⟩
                    exact ⟨v, hlookup_ρ⟩
                simpa [hetyp_src, hv₂] using htyped_closure
              have htyp1_res :
                  valueHasETyp θ₀ o₀ res.qualType.etyp :=
                joinTypeResults_transport_valueHasETyp_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
              have htyp2_res :
                  valueHasETyp θ₁ o₁ res.qualType.etyp :=
                joinTypeResults_transport_valueHasETyp_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
              have hisArrow_src : src.qualType.etyp.isArrow = true := by
                simp [hetyp_src, ETyp.isArrow]
              have hisArrow_res : res.qualType.etyp.isArrow = true := by
                have hEq := etyp_isArrow_eq_of_beqSignature_true hsig
                calc
                  res.qualType.etyp.isArrow = src.qualType.etyp.isArrow := hEq
                  _ = true := hisArrow_src
              exact agreeValueUnder.dirty_internal_arrow hclean_internal_res hisArrow_res htyp1_res htyp2_res
        | guard _k _htag _hreg hnotfun_res =>
            exfalso
            have hisFun_src : src.qualType.etyp.isFunctionType = true := by
              simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hisFun_res : res.qualType.etyp.isFunctionType = true := by
              calc
                res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
                _ = true := hisFun_src
            rw [hisFun_res] at hnotfun_res
            cases hnotfun_res
    | @clean_internal_parrow st1 st2 p tcls _qt tcl x body pbody σcap ρcap₀ ρcap₁ _v₀ _v₁
      hclean_internal_src hetyp_src htcl hmatch hcap
      hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src
      htyping₀_src htyping₁_src hv₁ hv₂ =>
      cases hclean_res with
      | clean _hpoison_res =>
          have hlookup_back :
              ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                (ctxAfter ctx src).regime.lookup? k = some b := by
            intro k b hk
            exact
              joinTypeResults_lookup_member_regime_compat
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src k b hk
          have hlookup_true_back :
              ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                (ctxAfter ctx src).regime.lookup? k = some true := by
            intro k hk
            exact hlookup_back k true hk
          have hcap_res :=
            agreeCapturedEnv_transport_by_lookupTrueBack
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
              hlookup_true_back
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₀) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberVarsRegimeEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              (fun {σcap} {ρcap} h =>
                memberCvcrEvidence_transport_lookup_back
                  (predSat := predSat)
                  (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                  (μ := μ₁) hlookup_back h)
              hcap
          have hmemberVars₀_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberVars₀_src
          have hmemberCvcr₀_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₀) hlookup_back hmemberCvcr₀_src
          have hmemberVars₁_res :=
            memberVarsRegimeEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberVars₁_src
          have hmemberCvcr₁_res :=
            memberCvcrEvidence_transport_lookup_back
              (predSat := predSat)
              (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
              (μ := μ₁) hlookup_back hmemberCvcr₁_src
          rcases
              joinTypeResults_qualType_parrow_member_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                _h_join _hmem_src hetyp_src htcl
            with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
          by_cases hclean_internal_res : internalPoisonClean res.qualType
          · exact agreeValueUnder.clean_internal_parrow hclean_internal_res hetyp_res htcl_res hmatch hcap_res
              hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res
              htyping₀_src htyping₁_src hv₁ hv₂
          · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
              have hpure : Expr.toPExpr? body = some pbody := hmatch.1
              have htyped_closure :
                  valueHasETyp θ₀ (Value.peClosure x body ρcap₀) (ETyp.parrow st1 st2 p tcls) := by
                have htcl_match : PFnTClosure.regular x pbody σcap ∈ tcls := by
                  simpa [hmatch.2] using htcl
                refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₀.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₁] using htyped_closure
            have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
              have hpure : Expr.toPExpr? body = some pbody := hmatch.1
              have htyped_closure :
                  valueHasETyp θ₁ (Value.peClosure x body ρcap₁) (ETyp.parrow st1 st2 p tcls) := by
                have htcl_match : PFnTClosure.regular x pbody σcap ∈ tcls := by
                  simpa [hmatch.2] using htcl
                refine valueHasETyp.peClosure (hpure := hpure) (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                · intro y qt_y v_y hlookup_σ hlookup_ρ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v', hlookup_ρ', htyp'⟩
                  have hv_eq : v' = v_y := by
                    have : some v' = some v_y := by
                      calc
                        some v' = ρcap₁.lookup y := by simpa using hlookup_ρ'.symm
                        _ = some v_y := by simpa using hlookup_ρ
                    exact Option.some.inj this
                  subst hv_eq
                  exact htyp'
                · intro y qt_y hlookup_σ
                  rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                      (hcap := hcap) y qt_y (ofCaptured_lookup_of_list_lookup σcap y qt_y hlookup_σ) with
                    ⟨v, hlookup_ρ, _htyp⟩
                  exact ⟨v, hlookup_ρ⟩
              simpa [hetyp_src, hv₂] using htyped_closure
            have htyp1_res :
                valueHasETyp θ₀ o₀ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
            have htyp2_res :
                valueHasETyp θ₁ o₁ res.qualType.etyp :=
              joinTypeResults_transport_valueHasETyp_from_member
                (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
            have hisParrow_src : src.qualType.etyp.isParrow = true := by
              simp [hetyp_src, ETyp.isParrow]
            have hisParrow_res : res.qualType.etyp.isParrow = true := by
              have hEq := etyp_isParrow_eq_of_beqSignature_true hsig
              calc
                res.qualType.etyp.isParrow = src.qualType.etyp.isParrow := hEq
                _ = true := hisParrow_src
            exact agreeValueUnder.dirty_internal_parrow hclean_internal_res hisParrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
    | @clean_internal_parrow_extern id x y argTyp argPoison argPred retSpec p tcls _qt tcl σcap argQTyp ρcap₀ ρcap₁ _v₀ _v₁
        hclean_internal_src hetyp_src htcl hmatch hcap
        hmemberVars₀_src hmemberCvcr₀_src hmemberVars₁_src hmemberCvcr₁_src
        htyping₀_src htyping₁_src hv₁ hv₂ =>
        cases hclean_res with
        | clean _hpoison_res =>
            have hlookup_back :
                ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
                  (ctxAfter ctx src).regime.lookup? k = some b := by
              intro k b hk
              exact
                joinTypeResults_lookup_member_regime_compat
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  _h_join _hmem_src k b hk
            have hlookup_true_back :
                ∀ k, (ctxAfter ctx res).regime.lookup? k = some true →
                  (ctxAfter ctx src).regime.lookup? k = some true := by
              intro k hk
              exact hlookup_back k true hk
            have hcap_res :=
              agreeCapturedEnv_transport_by_lookupTrueBack
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
                hlookup_true_back
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₀) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₀) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberVarsRegimeEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₁) hlookup_back h)
                (fun {σcap} {ρcap} h =>
                  memberCvcrEvidence_transport_lookup_back
                    (predSat := predSat)
                    (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                    (μ := μ₁) hlookup_back h)
                hcap
            have hmemberVars₀_res :=
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₀) hlookup_back hmemberVars₀_src
            have hmemberCvcr₀_res :=
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₀) hlookup_back hmemberCvcr₀_src
            have hmemberVars₁_res :=
              memberVarsRegimeEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₁) hlookup_back hmemberVars₁_src
            have hmemberCvcr₁_res :=
              memberCvcrEvidence_transport_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ₁) hlookup_back hmemberCvcr₁_src
            rcases
                joinTypeResults_qualType_parrow_member_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  _h_join _hmem_src hetyp_src htcl
              with ⟨p_res, tcls_res, hetyp_res, htcl_res⟩
            by_cases hclean_internal_res : internalPoisonClean res.qualType
            · exact agreeValueUnder.clean_internal_parrow_extern hclean_internal_res hetyp_res htcl_res hmatch hcap_res
                hmemberVars₀_res hmemberCvcr₀_res hmemberVars₁_res hmemberCvcr₁_res
                htyping₀_src htyping₁_src hv₁ hv₂
            · have htyp1_src : valueHasETyp θ₀ o₀ src.qualType.etyp := by
                have htyped_closure :
                    valueHasETyp θ₀
                      (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec) ρcap₀)
                      (ETyp.parrow argTyp (parseReturnType retSpec) p tcls) := by
                  have htcl_match : PFnTClosure.extern id x retSpec σcap argQTyp [] ∈ tcls := by
                    simpa [hmatch] using htcl
                  refine valueHasETyp.peClosure_extern (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                  · intro y' qt_y v_y hlookup_σ hlookup_ρ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v', hlookup_ρ', htyp'⟩
                    have hv_eq : v' = v_y := by
                      have : some v' = some v_y := by
                        calc
                          some v' = ρcap₀.lookup y' := by simpa using hlookup_ρ'.symm
                          _ = some v_y := by simpa using hlookup_ρ
                      exact Option.some.inj this
                    subst hv_eq
                    exact htyp'
                  · intro y' qt_y hlookup_σ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_left
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v, hlookup_ρ, _htyp⟩
                    exact ⟨v, hlookup_ρ⟩
                simpa [hetyp_src, hv₁] using htyped_closure
              have htyp2_src : valueHasETyp θ₁ o₁ src.qualType.etyp := by
                have htyped_closure :
                    valueHasETyp θ₁
                      (Value.peClosure x (Expr.externPfn id y argTyp argPoison argPred retSpec) ρcap₁)
                      (ETyp.parrow argTyp (parseReturnType retSpec) p tcls) := by
                  have htcl_match : PFnTClosure.extern id x retSpec σcap argQTyp [] ∈ tcls := by
                    simpa [hmatch] using htcl
                  refine valueHasETyp.peClosure_extern (htcl := htcl_match) (henv := ?_) (hcover := ?_)
                  · intro y' qt_y v_y hlookup_σ hlookup_ρ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v', hlookup_ρ', htyp'⟩
                    have hv_eq : v' = v_y := by
                      have : some v' = some v_y := by
                        calc
                          some v' = ρcap₁.lookup y' := by simpa using hlookup_ρ'.symm
                          _ = some v_y := by simpa using hlookup_ρ
                      exact Option.some.inj this
                    subst hv_eq
                    exact htyp'
                  · intro y' qt_y hlookup_σ
                    rcases agreeCapturedEnv_ofCaptured_lookup_typed_right
                        (hcap := hcap) y' qt_y (ofCaptured_lookup_of_list_lookup σcap y' qt_y hlookup_σ) with
                      ⟨v, hlookup_ρ, _htyp⟩
                    exact ⟨v, hlookup_ρ⟩
                simpa [hetyp_src, hv₂] using htyped_closure
              have htyp1_res :
                  valueHasETyp θ₀ o₀ res.qualType.etyp :=
                joinTypeResults_transport_valueHasETyp_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
              have htyp2_res :
                  valueHasETyp θ₁ o₁ res.qualType.etyp :=
                joinTypeResults_transport_valueHasETyp_from_member
                  (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                  (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
              have hisParrow_src : src.qualType.etyp.isParrow = true := by
                simp [hetyp_src, ETyp.isParrow]
              have hisParrow_res : res.qualType.etyp.isParrow = true := by
                have hEq := etyp_isParrow_eq_of_beqSignature_true hsig
                calc
                  res.qualType.etyp.isParrow = src.qualType.etyp.isParrow := hEq
                  _ = true := hisParrow_src
              exact agreeValueUnder.dirty_internal_parrow hclean_internal_res hisParrow_res htyp1_res htyp2_res
        | guard _k _htag _hreg hnotfun_res =>
            exfalso
            have hisFun_src : src.qualType.etyp.isFunctionType = true := by
              simp [hetyp_src, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
            have hisFun_res : res.qualType.etyp.isFunctionType = true := by
              calc
                res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
                _ = true := hisFun_src
            rw [hisFun_res] at hnotfun_res
            cases hnotfun_res
    | dirty_internal_arrow hdirty_src hisArrow_src htyp1_src htyp2_src =>
      cases hclean_res with
      | clean _hpoison_res =>
          have htyp1_res :
              valueHasETyp θ₀ o₀ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
          have htyp2_res :
              valueHasETyp θ₁ o₁ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
          have hisArrow_res : res.qualType.etyp.isArrow = true := by
            have hEq := etyp_isArrow_eq_of_beqSignature_true hsig
            calc
              res.qualType.etyp.isArrow = src.qualType.etyp.isArrow := hEq
              _ = true := hisArrow_src
          have hdirty_res : ¬ internalPoisonClean res.qualType := by
            -- Extract the explicit `p = true` witness from the source dirty-arrow case.
            cases hs_etyp : src.qualType.etyp with
            | arrow st1 st2 p tcls =>
                have hptrue : p = true := by
                  have : ¬ p = false := by simpa [hs_etyp, internalPoisonClean, getInternalPoison] using hdirty_src
                  cases p <;> simp at this
                  rfl
                have hdirty_join :
                    getInternalPoison res.qualType.etyp = some true :=
                  joinTypeResults_qualType_getInternalPoison_true_from_member_arrow
                    (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                    _h_join _hmem_src (by simpa [hptrue] using hs_etyp)
                simp [internalPoisonClean, hdirty_join]
            | int | bool | unit | string | ref _ | parrow _ _ _ _ =>
                simp [ETyp.isArrow, hs_etyp] at hisArrow_src
          exact agreeValueUnder.dirty_internal_arrow hdirty_res hisArrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp only [ETyp.isFunctionType, Bool.or_eq_true]
            left
            exact hisArrow_src
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | dirty_internal_parrow hdirty_src hisParrow_src htyp1_src htyp2_src =>
      cases hclean_res with
      | clean _hpoison_res =>
          have htyp1_res :
              valueHasETyp θ₀ o₀ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₀) (v := o₀) _h_join _hmem_src htyp1_src
          have htyp2_res :
              valueHasETyp θ₁ o₁ res.qualType.etyp :=
            joinTypeResults_transport_valueHasETyp_from_member
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              (θ := θ₁) (v := o₁) _h_join _hmem_src htyp2_src
          have hisParrow_res : res.qualType.etyp.isParrow = true := by
            have hEq := etyp_isParrow_eq_of_beqSignature_true hsig
            calc
              res.qualType.etyp.isParrow = src.qualType.etyp.isParrow := hEq
              _ = true := hisParrow_src
          have hdirty_res : ¬ internalPoisonClean res.qualType := by
            cases hs_etyp : src.qualType.etyp with
            | parrow st1 st2 p tcls =>
                have hptrue : p = true := by
                  have : ¬ p = false := by simpa [hs_etyp, internalPoisonClean, getInternalPoison] using hdirty_src
                  cases p <;> simp at this
                  rfl
                have hdirty_join :
                    getInternalPoison res.qualType.etyp = some true :=
                  joinTypeResults_qualType_getInternalPoison_true_from_member_parrow
                    (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
                    _h_join _hmem_src (by simpa [hptrue] using hs_etyp)
                simp [internalPoisonClean, hdirty_join]
            | int | bool | unit | string | ref _ | arrow _ _ _ _ =>
                simp [ETyp.isParrow, hs_etyp] at hisParrow_src
          exact agreeValueUnder.dirty_internal_parrow hdirty_res hisParrow_res htyp1_res htyp2_res
      | guard _k _htag _hreg hnotfun_res =>
          exfalso
          have hisFun_src : src.qualType.etyp.isFunctionType = true := by
            simp only [ETyp.isFunctionType, Bool.or_eq_true]
            right
            exact hisParrow_src
          have hisFun_res : res.qualType.etyp.isFunctionType = true := by
            calc
              res.qualType.etyp.isFunctionType = src.qualType.etyp.isFunctionType := hfunEq
              _ = true := hisFun_src
          rw [hisFun_res] at hnotfun_res
          cases hnotfun_res
  | clean_ref hpoison_src hetyp_src hlookup1 hin hv1 hlookup2 hv2 =>
      obtain ⟨ls_res, hetyp_res, hin_res⟩ :=
        joinTypeResults_qualType_ref_membership_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src _ hetyp_src hin
      cases hclean_res with
      | clean hpoison_res =>
          exact agreeValueUnder.clean_ref hpoison_res hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
      | guard k htag hreg _hnotfun =>
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
  | withPred_true_ref _ _ _ hetyp_src hlookup1 hin hv1 hlookup2 hv2 =>
      obtain ⟨ls_res, hetyp_res, hin_res⟩ :=
        joinTypeResults_qualType_ref_membership_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src _ hetyp_src hin
      cases hclean_res with
      | clean hpoison_res =>
          exact agreeValueUnder.clean_ref hpoison_res hetyp_res hlookup1 hin_res hv1 hlookup2 hv2
      | guard k htag hreg _hnotfun =>
          exact agreeValueUnder.withPred_true_ref k htag hreg hetyp_res hlookup1 hin_res hv1 hlookup2 hv2

private lemma closureCapturedVarsRegimeMasked_weaken_fnTClosures'
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ : Memory}
  {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List FnTClosure}
  {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegimeMasked masked predSat R
    ⟨ETyp.arrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R
    ⟨ETyp.arrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | nonClosure hv hpe =>
      exact .nonClosure hv hpe
  | closure xp body ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hmem_src hP hrec =>
      have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
      subst heq_tcls
      exact .closure xp body ρcap σcap st1 st2 p' tcls' hval rfl (hmem _ hmem_src) hP hrec
  | closure_extern id xp y argTyp retSpec effects ρcap σcap _p tcls_src hval hetyp_eq hmem_src hP hrec =>
      have heq_arg : argTyp = st1 := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.1).symm
      have heq_ret : parseReturnType retSpec = st2 := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.1).symm
      have heq_tcls : tcls_src = tcls := ((ETyp.arrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
      subst heq_tcls
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p' tcls'
        hval (by simp [heq_arg, heq_ret]) (hmem _ hmem_src) hP hrec
  | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_eq_parr _ _ =>
      exfalso
      simp at hetyp_eq_parr
  | peClosure_extern _id _xp _y _argTyp _retSpec _ρcap _σcap _p _tcls _hval hetyp_eq_parr _hmem _hP _hrec =>
      exfalso
      simp at hetyp_eq_parr

private lemma closureCapturedVarsRegimeMasked_weaken_pFnTClosures'
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime} {μ : Memory}
  {θ : RealizationMap} {v : Value}
  {st1 st2 : Typ} {p p' : Poison} {tcls tcls' : List PFnTClosure}
  {poison : Poison} {pred : Predicate}
  (hmem : ∀ tcl, tcl ∈ tcls → tcl ∈ tcls')
  (h : closureCapturedVarsRegimeMasked masked predSat R
    ⟨ETyp.parrow st1 st2 p tcls, poison, pred⟩ μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R
    ⟨ETyp.parrow st1 st2 p' tcls', poison, pred⟩ μ θ v := by
  cases h with
  | nonClosure hv hpe =>
      exact .nonClosure hv hpe
  | closure _ _ _ _ _ _ _ _ _ hetyp_eq_arr _ _ =>
      exfalso
      simp at hetyp_eq_arr
  | closure_extern _id _xp _y _argTyp _retSpec _effects _ρcap _σcap _p _tcls _hval hetyp_eq_arr _hmem _hP _hrec =>
      exfalso
      simp at hetyp_eq_arr
  | peClosure xp body pbody ρcap σcap _st1 _st2 _p tcls_src hval hetyp_eq hpure hmem_src hP hrec =>
      have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
      subst heq_tcls
      exact .peClosure xp body pbody ρcap σcap st1 st2 p' tcls' hval rfl hpure (hmem _ hmem_src) hP hrec
  | peClosure_extern id xp y argTyp retSpec ρcap σcap _p tcls_src hval hetyp_eq hmem_src hP hrec =>
      have heq_arg : argTyp = st1 := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.1).symm
      have heq_ret : parseReturnType retSpec = st2 := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.1).symm
      have heq_tcls : tcls_src = tcls := ((ETyp.parrow.injEq ..).mp hetyp_eq |>.2.2.2).symm
      subst heq_tcls
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p' tcls'
        hval (by simp [heq_arg, heq_ret]) (hmem _ hmem_src) hP hrec

theorem closureCapturedVarsRegimeMasked_joinETyps_step
  (masked : Tag → Prop) (predSat : PredSat) (R : Regime)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegimeMasked masked predSat R ⟨etyp1, p1, pr1⟩ μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R
    ⟨joinETyps etyp1 resEtyp p1 resPoison,
      joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases etyp1 with
  | int | bool | unit | string =>
      simp [joinETyps]
      exact closureCapturedVarsRegimeMasked_transport_etyp (by simp) hcap
  | ref ls =>
      cases resEtyp with
      | ref ls2 =>
          simp only [beqETypSignature] at hcompat
          cases hcap with
          | nonClosure hv hpe => exact .nonClosure hv hpe
          | closure _ _ _ _ _ _ _ _ _ hetyp_arr _ _ => exfalso; exact ETyp.noConfusion hetyp_arr
          | closure_extern _ _ _ _ _ _ _ _ _ _ _ hetyp_arr _ _ _ => exfalso; exact ETyp.noConfusion hetyp_arr
          | peClosure _ _ _ _ _ _ _ _ _ _ hetyp_parr _ _ => exfalso; exact ETyp.noConfusion hetyp_parr
          | peClosure_extern _ _ _ _ _ _ _ _ _ _ hetyp_parr _ _ _ => exfalso; exact ETyp.noConfusion hetyp_parr
      | _ => simp [beqETypSignature] at hcompat
  | arrow st1 st2 p tcls =>
      have hisArrow : resEtyp.isArrow := by
        cases resEtyp with
        | arrow => rfl
        | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_arrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisArrow hcompat
      have hcap' :=
        closureCapturedVarsRegimeMasked_weaken_fnTClosures'
          (masked := masked) (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegimeMasked_transport_etyp heq.symm hcap'
  | parrow st1 st2 p tcls =>
      have hisParrow : resEtyp.isParrow := by
        cases resEtyp with
        | parrow => rfl
        | _ => simp [beqETypSignature] at hcompat
      obtain ⟨p', tcls', heq, hmem⟩ :=
        joinETyps_parrow_structure
          (st1 := st1) (st2 := st2) (p1 := p) (tcls1 := tcls)
          (t2 := resEtyp) (p1' := p1) (p2' := resPoison)
          hisParrow hcompat
      have hcap' :=
        closureCapturedVarsRegimeMasked_weaken_pFnTClosures'
          (masked := masked) (p' := p') (tcls' := tcls') hmem hcap
      exact closureCapturedVarsRegimeMasked_transport_etyp heq.symm hcap'

theorem closureCapturedVarsRegimeMasked_joinETyps_step_right
  (masked : Tag → Prop) (predSat : PredSat) (R : Regime)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (etyp1 resEtyp : ETyp) (p1 resPoison : Poison) (pr1 resPred : Predicate)
  (hcompat : beqETypSignature etyp1 resEtyp = true)
  (hcap : closureCapturedVarsRegimeMasked masked predSat R ⟨resEtyp, resPoison, resPred⟩ μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R
    ⟨joinETyps etyp1 resEtyp p1 resPoison,
      joinPoison p1 resPoison, joinPredicates pr1 resPred⟩ μ θ v := by
  cases hcap with
  | nonClosure hv hpe =>
      exact .nonClosure hv hpe
  | closure x body ρcap σcap st1r st2r pr tclr hval hetyp_r htcl hP hrec =>
      have hetyp_r' : resEtyp = ETyp.arrow st1r st2r pr tclr := by
        simpa using hetyp_r
      subst resEtyp
      cases etyp1 with
      | int => exfalso; simp [beqETypSignature] at hcompat
      | bool => exfalso; simp [beqETypSignature] at hcompat
      | unit => exfalso; simp [beqETypSignature] at hcompat
      | string => exfalso; simp [beqETypSignature] at hcompat
      | ref ls => exfalso; simp [beqETypSignature] at hcompat
      | arrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hcompat
          obtain ⟨rfl, rfl⟩ := hcompat
          have hcap_src :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
            simpa using (.closure x body ρcap σcap st1l st2l pr tclr hval rfl htcl hP hrec :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v)
          have hcap_join :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l st2l (joinPoison pl pr) (mergeFnTClosures tclsl tclr),
                  resPoison, resPred⟩ μ θ v :=
            closureCapturedVarsRegimeMasked_weaken_fnTClosures'
              (masked := masked) (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
              (st1 := st1l) (st2 := st2l) (p := pr)
              (p' := joinPoison pl pr) (tcls := tclr)
              (tcls' := mergeFnTClosures tclsl tclr)
              (poison := resPoison) (pred := resPred)
              (fun tcl hmem => mem_mergeFnTClosures_right tclsl tclr tcl hmem)
              hcap_src
          exact closureCapturedVarsRegimeMasked_transport_etyp (qt := _)
            (qt' := ⟨joinETyps (ETyp.arrow st1l st2l pl tclsl) (ETyp.arrow st1l st2l pr tclr)
                p1 resPoison,
                joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
            (by simp [joinETyps]) hcap_join
      | parrow st1l st2l pl tclsl =>
          exfalso
          simp [beqETypSignature] at hcompat
  | closure_extern id x y argTyp retSpec effects ρcap σcap pr tclr hval hetyp_r htcl hP hrec =>
      have hetyp_r' : resEtyp = ETyp.arrow argTyp (parseReturnType retSpec) pr tclr := by
        simpa using hetyp_r
      subst resEtyp
      cases etyp1 with
      | int => exfalso; simp [beqETypSignature] at hcompat
      | bool => exfalso; simp [beqETypSignature] at hcompat
      | unit => exfalso; simp [beqETypSignature] at hcompat
      | string => exfalso; simp [beqETypSignature] at hcompat
      | ref ls => exfalso; simp [beqETypSignature] at hcompat
      | arrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hcompat
          obtain ⟨rfl, rfl⟩ := hcompat
          have hcap_src :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l (parseReturnType retSpec) pr tclr,
                  resPoison, resPred⟩ μ θ v := by
            simpa using (.closure_extern id x y st1l retSpec effects ρcap σcap pr tclr
              hval rfl htcl hP hrec :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l (parseReturnType retSpec) pr tclr,
                  resPoison, resPred⟩ μ θ v)
          have hcap_join :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.arrow st1l (parseReturnType retSpec) (joinPoison pl pr)
                  (mergeFnTClosures tclsl tclr), resPoison, resPred⟩ μ θ v :=
            closureCapturedVarsRegimeMasked_weaken_fnTClosures'
              (masked := masked) (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
              (st1 := st1l) (st2 := parseReturnType retSpec) (p := pr)
              (p' := joinPoison pl pr) (tcls := tclr)
              (tcls' := mergeFnTClosures tclsl tclr)
              (poison := resPoison) (pred := resPred)
              (fun tcl hmem => mem_mergeFnTClosures_right tclsl tclr tcl hmem)
              hcap_src
          exact closureCapturedVarsRegimeMasked_transport_etyp (qt := _)
            (qt' := ⟨joinETyps (ETyp.arrow st1l (parseReturnType retSpec) pl tclsl)
                (ETyp.arrow st1l (parseReturnType retSpec) pr tclr) p1 resPoison,
                joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
            (by simp [joinETyps]) hcap_join
      | parrow st1l st2l pl tclsl =>
          exfalso
          simp [beqETypSignature] at hcompat
  | peClosure x body pbody ρcap σcap st1r st2r pr tclr hval hetyp_r hpure htcl hP hrec =>
      have hetyp_r' : resEtyp = ETyp.parrow st1r st2r pr tclr := by
        simpa using hetyp_r
      subst resEtyp
      cases etyp1 with
      | int => exfalso; simp [beqETypSignature] at hcompat
      | bool => exfalso; simp [beqETypSignature] at hcompat
      | unit => exfalso; simp [beqETypSignature] at hcompat
      | string => exfalso; simp [beqETypSignature] at hcompat
      | ref ls => exfalso; simp [beqETypSignature] at hcompat
      | arrow st1l st2l pl tclsl =>
          exfalso
          simp [beqETypSignature] at hcompat
      | parrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hcompat
          obtain ⟨rfl, rfl⟩ := hcompat
          have hcap_src :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v := by
            simpa using (.peClosure x body pbody ρcap σcap st1l st2l pr tclr hval rfl hpure htcl hP hrec :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l st2l pr tclr, resPoison, resPred⟩ μ θ v)
          have hcap_join :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l st2l (joinPoison pl pr) (mergePFnTClosures tclsl tclr),
                  resPoison, resPred⟩ μ θ v :=
            closureCapturedVarsRegimeMasked_weaken_pFnTClosures'
              (masked := masked) (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
              (st1 := st1l) (st2 := st2l) (p := pr)
              (p' := joinPoison pl pr) (tcls := tclr)
              (tcls' := mergePFnTClosures tclsl tclr)
              (poison := resPoison) (pred := resPred)
              (fun tcl hmem => mem_mergePFnTClosures_right tclsl tclr tcl hmem)
              hcap_src
          exact closureCapturedVarsRegimeMasked_transport_etyp (qt := _)
            (qt' := ⟨joinETyps (ETyp.parrow st1l st2l pl tclsl) (ETyp.parrow st1l st2l pr tclr)
                p1 resPoison,
                joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
            (by simp [joinETyps]) hcap_join
  | peClosure_extern id x y argTyp retSpec ρcap σcap pr tclr hval hetyp_r htcl hP hrec =>
      have hetyp_r' : resEtyp = ETyp.parrow argTyp (parseReturnType retSpec) pr tclr := by
        simpa using hetyp_r
      subst resEtyp
      cases etyp1 with
      | int => exfalso; simp [beqETypSignature] at hcompat
      | bool => exfalso; simp [beqETypSignature] at hcompat
      | unit => exfalso; simp [beqETypSignature] at hcompat
      | string => exfalso; simp [beqETypSignature] at hcompat
      | ref ls => exfalso; simp [beqETypSignature] at hcompat
      | arrow st1l st2l pl tclsl =>
          exfalso
          simp [beqETypSignature] at hcompat
      | parrow st1l st2l pl tclsl =>
          simp [beqETypSignature] at hcompat
          obtain ⟨rfl, rfl⟩ := hcompat
          have hcap_src :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l (parseReturnType retSpec) pr tclr,
                  resPoison, resPred⟩ μ θ v := by
            simpa using (.peClosure_extern id x y st1l retSpec ρcap σcap pr tclr
              hval rfl htcl hP hrec :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l (parseReturnType retSpec) pr tclr,
                  resPoison, resPred⟩ μ θ v)
          have hcap_join :
              closureCapturedVarsRegimeMasked masked predSat R
                ⟨ETyp.parrow st1l (parseReturnType retSpec) (joinPoison pl pr)
                  (mergePFnTClosures tclsl tclr), resPoison, resPred⟩ μ θ v :=
            closureCapturedVarsRegimeMasked_weaken_pFnTClosures'
              (masked := masked) (predSat := predSat) (R := R) (μ := μ) (θ := θ) (v := v)
              (st1 := st1l) (st2 := parseReturnType retSpec) (p := pr)
              (p' := joinPoison pl pr) (tcls := tclr)
              (tcls' := mergePFnTClosures tclsl tclr)
              (poison := resPoison) (pred := resPred)
              (fun tcl hmem => mem_mergePFnTClosures_right tclsl tclr tcl hmem)
              hcap_src
          exact closureCapturedVarsRegimeMasked_transport_etyp (qt := _)
            (qt' := ⟨joinETyps (ETyp.parrow st1l (parseReturnType retSpec) pl tclsl)
                (ETyp.parrow st1l (parseReturnType retSpec) pr tclr) p1 resPoison,
                joinPoison p1 resPoison, joinPredicates pr1 resPred⟩)
            (by simp [joinETyps]) hcap_join

private lemma joinTypeResults_closure_cvcr_masked_transport_from_member
  (masked : Tag → Prop) (predSat : PredSat) (ctx : TypeContext) (first src : TypeResult)
  (rest : List TypeResult) (res : TypeResult) (R : Regime) (μ : Memory)
  (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (hcap_src : closureCapturedVarsRegimeMasked masked predSat R src.qualType μ θ v) :
  closureCapturedVarsRegimeMasked masked predSat R res.qualType μ θ v := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
      TypeResult → Except String (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
            joinMemEnvsStrong acc.2.1 result.memEnv', joinPoison acc.2.2.1 resPoison,
            joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
            joinRegimes acc.2.2.2.2.2.1 result.regime',
            max acc.2.2.2.2.2.2.1 result.nextLoc', max acc.2.2.2.2.2.2.2 result.nextTag')
  have h_fold_left_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        closureCapturedVarsRegimeMasked masked predSat R ⟨acc.1, acc.2.2.1, acc.2.2.2.1⟩ μ θ v →
        closureCapturedVarsRegimeMasked masked predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' hcompat hfold hcap_acc
    induction rs' generalizing acc with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        simpa using hcap_acc
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcap_acc1 :
                closureCapturedVarsRegimeMasked masked predSat R
                  ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
              have hstep :=
                closureCapturedVarsRegimeMasked_joinETyps_step
                  masked predSat R μ θ v acc.1 resEtyp
                  acc.2.2.1 resPoison acc.2.2.2.1 resPred hcompat_x hcap_acc
              simpa [acc1] using hstep
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            exact ih (acc := acc1) hcompat_tail hfold_tail hcap_acc1
  have h_fold_member_cvcr :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult),
        (∀ r ∈ rs', beqETypSignature acc.1 r.qualType.etyp = true) →
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        closureCapturedVarsRegimeMasked masked predSat R src'.qualType μ θ v →
        closureCapturedVarsRegimeMasked masked predSat R ⟨acc'.1, acc'.2.2.1, acc'.2.2.2.1⟩ μ θ v := by
    intro rs' acc acc' src' hcompat hfold hmem_src' hcap_src'
    induction rs' generalizing acc acc' src' with
    | nil =>
        cases hmem_src'
    | cons x xs ih =>
        cases hqx : x.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqx, bind, Except.bind] at hfold
            have hcompat_x : beqETypSignature acc.1 resEtyp = true := by
              have hx := hcompat x (by simp)
              simpa [hqx] using hx
            let acc1 :
                ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag :=
              (joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
                joinMemEnvsStrong acc.2.1 x.memEnv', joinPoison acc.2.2.1 resPoison,
                joinPredicates acc.2.2.2.1 resPred, joinTagEnvs acc.2.2.2.2.1 x.tagEnv',
                joinRegimes acc.2.2.2.2.2.1 x.regime',
                max acc.2.2.2.2.2.2.1 x.nextLoc', max acc.2.2.2.2.2.2.2 x.nextTag')
            have hcompat_tail : ∀ r ∈ xs, beqETypSignature acc1.1 r.qualType.etyp = true := by
              intro r hr
              have hcomp := hcompat r (List.Mem.tail _ hr)
              rw [show acc1.1 = joinETyps acc.1 resEtyp acc.2.2.1 resPoison by rfl]
              rw [← beqETypSignature_joinETyps_left hcompat_x]
              exact hcomp
            have hfold_tail : List.foldlM joinStep acc1 xs = .ok acc' := by
              simpa [acc1] using hfold
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              have hcap_acc1 :
                  closureCapturedVarsRegimeMasked masked predSat R
                    ⟨acc1.1, acc1.2.2.1, acc1.2.2.2.1⟩ μ θ v := by
                have hstep :=
                  closureCapturedVarsRegimeMasked_joinETyps_step_right
                    masked predSat R μ θ v acc.1 resEtyp acc.2.2.1 resPoison acc.2.2.2.1 resPred
                    hcompat_x (by simpa [hqx] using hcap_src')
                simpa [acc1] using hstep
              exact h_fold_left_cvcr xs acc1 acc' hcompat_tail hfold_tail hcap_acc1
            · exact ih (acc := acc1) (acc' := acc') (src' := src')
                hcompat_tail hfold_tail hsrc_tail hcap_src'
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
      cases hcheck : (List.foldlM (fun _ result =>
        match result.qualType with
        | { etyp := resEtyp, poison := _, pred := _ } =>
            if beqETypSignature etyp resEtyp = false then
              Except.error (toString "Closure alternatives produced incompatible result types: " ++
                toString (repr etyp) ++ toString " vs " ++ toString (repr resEtyp))
            else Except.ok ()) () rest : Except String Unit) with
      | error _ =>
          erw [hcheck] at _h_join
          contradiction
      | ok _ =>
          erw [hcheck] at _h_join
          cases hfold : List.foldlM joinStep (etyp, first.memEnv', poison, pred, first.tagEnv',
            first.regime', first.nextLoc', first.nextTag') rest with
          | error _ =>
              erw [hfold] at _h_join
              contradiction
          | ok a =>
              erw [hfold] at _h_join
              have heq := Except.ok.inj _h_join
              have hetyp_res : (⟨a.1, a.2.2.1, a.2.2.2.1⟩ : QTyp).etyp = res.qualType.etyp := by
                exact congrArg (fun tr => tr.qualType.etyp) heq
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                have hcap_a :
                    closureCapturedVarsRegimeMasked masked predSat R
                      ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_left_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    a
                    (joinTypeResults_compat_ok etyp rest hcheck)
                    hfold
                    (hqt ▸ hcap_src)
                exact closureCapturedVarsRegimeMasked_transport_etyp hetyp_res hcap_a
              · have hcap_a :
                    closureCapturedVarsRegimeMasked masked predSat R
                      ⟨a.1, a.2.2.1, a.2.2.2.1⟩ μ θ v :=
                  h_fold_member_cvcr rest
                    (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime',
                      first.nextLoc', first.nextTag')
                    a src
                    (joinTypeResults_compat_ok etyp rest hcheck)
                    hfold hsrc_tail hcap_src
                exact closureCapturedVarsRegimeMasked_transport_etyp hetyp_res hcap_a

private lemma valueConsistentWithRegimeMasked_guardClosure_consistency
  {masked : Tag → Prop} {predSat : PredSat} {R : Regime}
  {qt : QTyp} {μ : Memory} {θ : RealizationMap} {v : Value}
  {k : Tag} {arg_name : Name} {pred_body : PExpr} {var_env : CapturedVarEnv} {b : Bool}
  (hnotmasked : ¬ masked k)
  (hvalc : valueConsistentWithRegimeMasked masked predSat R qt μ θ v)
  (hpred : qt.pred = Predicate.guardClosure k arg_name pred_body var_env)
  (hlookup : R.lookup? k = some b) :
  (b = true → qtypPredHolds predSat qt μ v) ∧
  (b = false → ¬ qtypPredHolds predSat qt μ v) := by
  cases hvalc with
  | noTag htag _ =>
      simp [qtypGuardTag, hpred] at htag
  | guardOnly_ok _ hgo _ =>
      simp [hpred] at hgo
  | maskedTag k' htag hmasked _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      exact False.elim (hnotmasked (by simpa [hk_eq] using hmasked))
  | notInRegime k' htag hnone _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have : R.lookup? k = none := by simpa [hk_eq] using hnone
      rw [hlookup] at this
      cases this
  | inRegimeTrue k' htag hktrue hholds _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hb_true : b = true := by
        have : some b = some true := by
          calc
            some b = R.lookup? k := by symm; exact hlookup
            _ = R.lookup? k' := by simp [hk_eq]
            _ = some true := hktrue
        exact Option.some.inj this
      subst hb_true
      exact ⟨fun _ => hholds, fun hbfalse _ => by cases hbfalse⟩
  | inRegimeFalse k' htag hkfalse hnot _ =>
      have hk_eq : k' = k := by
        have : some k' = some k := by
          calc
            some k' = qtypGuardTag qt := by simp [htag]
            _ = some k := by simp [qtypGuardTag, hpred]
        exact Option.some.inj this
      have hb_false : b = false := by
        have : some b = some false := by
          calc
            some b = R.lookup? k := by symm; exact hlookup
            _ = R.lookup? k' := by simp [hk_eq]
            _ = some false := hkfalse
        exact Option.some.inj this
      subst hb_false
      constructor
      · intro hbtrue
        cases hbtrue
      · intro _
        exact hnot


lemma join_transport_agreeOnClean_from_member
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
            agreeValueUnder_clean_transport_by_lookupTrueBack
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
          agreeValueUnder_clean_transport_by_lookupTrueBack
            (predSat := predSat)
            (R := src.regime') (R' := res.regime')
            (μ₀ := μ₀) (μ₁ := μ₁) (θ₀ := θ₀) (θ₁ := θ₁)
            (qt := qt) (v₀ := v₀) (v₁ := v₁)
            hlookup_true_back
            hmemberVars₀_transport hmemberCvcr₀_transport
            hmemberVars₁_transport hmemberCvcr₁_transport
            hclean hagree
        exact agreeVarUnder.agree_values x qt v₀ v₁ hlookup₀ hlookup₁ hagree'


lemma joinTypeResults_transport_valueConsistentWithRegimeMasked_from_member
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (θ : RealizationMap) (v : Value)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx src).regime src.qualType μ θ v) :
  valueConsistentWithRegimeMasked masked predSat (ctxAfter ctx res).regime res.qualType μ θ v := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  have hcap_src :
      closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx src).regime src.qualType μ θ v :=
    valueConsistentWithRegimeMasked_closureCapturedVarsRegime h_src
  have hcap_src_resR :
      closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx res).regime src.qualType μ θ v :=
    closureCapturedVarsRegimeMasked_transport_lookup_back
      (masked := masked) (predSat := predSat)
      (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
      (qt := src.qualType) (μ := μ) (θ := θ) (v := v)
      hlookup_back hcap_src
  have hcap_res :
      closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx res).regime res.qualType μ θ v :=
    joinTypeResults_closure_cvcr_masked_transport_from_member
      (masked := masked) (predSat := predSat)
      (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
      (R := (ctxAfter ctx res).regime) (μ := μ) (θ := θ) (v := v)
      _h_join _hmem_src hcap_src_resR
  cases hpred_res : res.qualType.pred with
  | noPred =>
      exact valueConsistentWithRegimeMasked.noTag
        (show qtypGuardTag res.qualType = none by simp [qtypGuardTag, hpred_res])
        hcap_res
  | guardOnly k =>
      exact valueConsistentWithRegimeMasked.guardOnly_ok k hpred_res hcap_res
  | guardClosure k arg_name pred_body var_env =>
      have hpred_src :
          src.qualType.pred = Predicate.guardClosure k arg_name pred_body var_env :=
        joinTypeResults_pred_eq_guardClosure_from_member
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src hpred_res
      have hpred_eq : src.qualType.pred = res.qualType.pred := by
        simpa [hpred_res] using hpred_src
      have htag_res : qtypGuardTag res.qualType = some k := by
        simp [qtypGuardTag, hpred_res]
      by_cases hmasked : masked k
      · exact valueConsistentWithRegimeMasked.maskedTag k htag_res hmasked hcap_res
      · cases hlookupR : (ctxAfter ctx res).regime.lookup? k with
        | none =>
            exact valueConsistentWithRegimeMasked.notInRegime k htag_res hlookupR hcap_res
        | some b =>
            have hlookup_src :
                (ctxAfter ctx src).regime.lookup? k = some b := hlookup_back k b hlookupR
            have hcons_src :
                (b = true → qtypPredHolds predSat src.qualType μ v) ∧
                (b = false → ¬ qtypPredHolds predSat src.qualType μ v) :=
              valueConsistentWithRegimeMasked_guardClosure_consistency
                (masked := masked) (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (qt := src.qualType)
                (μ := μ) (θ := θ) (v := v)
                (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                hmasked h_src hpred_src hlookup_src
            cases b with
            | false =>
                have hnot_src : ¬ qtypPredHolds predSat src.qualType μ v := hcons_src.2 rfl
                have hnot_res : ¬ qtypPredHolds predSat res.qualType μ v :=
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                    (μ := μ) (v := v) hpred_eq hnot_src
                exact valueConsistentWithRegimeMasked.inRegimeFalse k htag_res hlookupR hnot_res hcap_res
            | true =>
                have hholds_src : qtypPredHolds predSat src.qualType μ v := hcons_src.1 rfl
                have hholds_res : qtypPredHolds predSat res.qualType μ v :=
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := src.qualType) (qt' := res.qualType)
                    (μ := μ) (v := v) hpred_eq hholds_src
                exact valueConsistentWithRegimeMasked.inRegimeTrue k htag_res hlookupR hholds_res hcap_res


private lemma joinMemEnvs_lookup_guardClosure_left
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt1 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup1 : env1.lookup l = some qt1)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt1.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup2_none : env2.lookup l = none
  · have hcontains1 : env1.contains l := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
    have hlookup2_none_get : env2[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup2_none
    have hjoin_eq_left := joinMemEnvs_lookup_eq_left_of_right_none env1 env2 l hcontains1 hlookup2_none_get
    have hqt_eq : qt1 = qt := by
      have hqeq_opt : some qt = some qt1 := by
        calc
          some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env1.lookup l := hjoin_eq_left
          _ = some qt1 := hlookup1
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using hpred_join
  · have hlookup2_some : env2.lookup l ≠ none := hlookup2_none
    rcases Option.ne_none_iff_exists'.1 hlookup2_some with ⟨qt2, hlookup2⟩
    have he1 : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
      |> (Std.ExtTreeMap.contains_iff_mem).mp
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
      memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
    have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by
      have hjoin_go : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = f l (env1.get? l) (env2.get? l) := by
        cases hopt : f l (env1.get? l) (env2.get? l) with
        | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
        | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
      rw [← h_go_eq_f]; exact hjoin_go
    have hqt_pred : qt.pred = joinPredicates qt1.pred qt2.pred := by
      erw [he1, he2] at hmatch
      have heq := (Option.some.inj hmatch).symm
      exact congr_arg MemEntry.pred heq
    have hsplit := joinPredicates_eq_guardClosure
      (p := qt1.pred) (q := qt2.pred) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env)
      (by simpa [hqt_pred] using hpred_join)
    exact hsplit.1

private lemma joinMemEnvs_lookup_guardClosure_right
  (env1 env2 : MemoryTypeEnv) (l : Loc) (qt qt2 : QTyp)
  (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_join : (joinMemEnvs env1 env2).lookup l = some qt)
  (hlookup2 : env2.lookup l = some qt2)
  (hpred_join : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  qt2.pred = Predicate.guardClosure k arg_name pred_body var_env := by
  by_cases hlookup1_none : env1.lookup l = none
  · have hcontains2 : env2.contains l := memEnv_contains_of_lookup_some env2 l qt2 hlookup2
    have hlookup1_none_get : env1[l]? = none := by
      simpa [MemoryTypeEnv.lookup, Std.ExtTreeMap.get?_eq_getElem?] using hlookup1_none
    have hjoin_eq_right := joinMemEnvs_lookup_eq_right_of_left_none env1 env2 l hlookup1_none_get hcontains2
    have hqt_eq : qt2 = qt := by
      have hqeq_opt : some qt = some qt2 := by
        calc
          some qt = (joinMemEnvs env1 env2).lookup l := hlookup_join.symm
          _ = env2.lookup l := hjoin_eq_right
          _ = some qt2 := hlookup2
      exact (Option.some.inj hqeq_opt).symm
    simpa [hqt_eq] using hpred_join
  · have hlookup1_some : env1.lookup l ≠ none := hlookup1_none
    rcases Option.ne_none_iff_exists'.1 hlookup1_some with ⟨qt1, hlookup1⟩
    have he1 : env1.get? l = some ⟨qt1.poison, qt1.pred⟩ := memEnv_get_eq_of_lookup env1 l qt1 hlookup1
    have he2 : env2.get? l = some ⟨qt2.poison, qt2.pred⟩ := memEnv_get_eq_of_lookup env2 l qt2 hlookup2
    have hmem1 : l ∈ env1 := memEnv_contains_of_lookup_some env1 l qt1 hlookup1
      |> (Std.ExtTreeMap.contains_iff_mem).mp
    have h_in : l ∈ (env1.keys ++ env2.keys).eraseDups := by
      have hkeys1 : l ∈ env1.keys := by rw [Std.ExtTreeMap.mem_keys]; exact hmem1
      exact List.mem_eraseDups_of_mem (List.mem_append_left _ hkeys1)
    let f : Loc → Option MemEntry → Option MemEntry → Option MemEntry := fun _ oe1 oe2 =>
      match oe1, oe2 with
      | some e1, none => some e1
      | none, some e2 => some e2
      | some e1, some e2 =>
        some ⟨joinPoison e1.poison e2.poison, joinPredicates e1.pred e2.pred⟩
      | none, none => none
    have hgo := combineExtTreeMaps_go_get_mem env1 env2 f (env1.keys ++ env2.keys).eraseDups
      ({} : MemoryTypeEnv) l h_in
    have hjoin_get : (joinMemEnvs env1 env2).get? l = some ⟨qt.poison, qt.pred⟩ :=
      memEnv_get_eq_of_lookup (joinMemEnvs env1 env2) l qt hlookup_join
    have hmatch : f l (env1.get? l) (env2.get? l) = some ⟨qt.poison, qt.pred⟩ := by
      have hjoin_go : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = some ⟨qt.poison, qt.pred⟩ := by
        simpa [joinMemEnvs, combineExtTreeMaps, Std.ExtTreeMap.get?_eq_getElem?] using hjoin_get
      have h_go_eq_f : (combineExtTreeMaps.go env1 env2 f (env1.keys ++ env2.keys).eraseDups
        ({} : MemoryTypeEnv))[l]? = f l (env1.get? l) (env2.get? l) := by
        cases hopt : f l (env1.get? l) (env2.get? l) with
        | none => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
        | some v => have hgo' := hgo; rw [hopt] at hgo'; exact hgo'
      rw [← h_go_eq_f]; exact hjoin_go
    have hqt_pred : qt.pred = joinPredicates qt1.pred qt2.pred := by
      erw [he1, he2] at hmatch
      have heq := (Option.some.inj hmatch).symm
      exact congr_arg MemEntry.pred heq
    have hsplit := joinPredicates_eq_guardClosure
      (p := qt1.pred) (q := qt2.pred) (k := k) (arg_name := arg_name)
      (pred_body := pred_body) (var_env := var_env)
      (by simpa [hqt_pred] using hpred_join)
    exact hsplit.2

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

lemma joinMemEnvsStrong_lookup_guardClosure_implies_left
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

lemma joinMemEnvsStrong_lookup_guardClosure_implies_right
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

private lemma joinTypeResults_lookup_member_guardClosure_lookup_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt : QTyp) (k : Tag) (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hpred_res : qt.pred = Predicate.guardClosure k arg_name pred_body var_env) :
  ∃ qt_src,
    (ctxAfter ctx src).memEnv.lookup l = some qt_src ∧
    qt_src.pred = Predicate.guardClosure k arg_name pred_body var_env := by
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
  have h_fold_left_guardClosure :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (qt_out : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        acc'.2.1.lookup l = some qt_out →
        qt_out.pred = Predicate.guardClosure k arg_name pred_body var_env →
        ∃ qt_acc, acc.2.1.lookup l = some qt_acc ∧
          qt_acc.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' qt_out hfold hlookup_out hpred_out
    induction rs' generalizing acc acc' qt_out with
    | nil =>
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        subst acc'
        exact ⟨qt_out, hlookup_out, hpred_out⟩
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
            rcases ih (acc := acc1) (acc' := acc') (qt_out := qt_out)
                hfold_tail hlookup_out hpred_out with
              ⟨qt_acc1, hlookup_acc1, hpred_acc1⟩
            rcases
                joinMemEnvsStrong_lookup_guardClosure_implies_left
                  (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                  (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                  (hlookup_join := by simpa [acc1] using hlookup_acc1)
                  (hpred_join := hpred_acc1)
              with ⟨qt_acc, hlookup_acc, hpred_acc⟩
            exact ⟨qt_acc, hlookup_acc, hpred_acc⟩
  have h_fold_member_guardClosure :
      ∀ (rs' : List TypeResult)
        (acc acc' : ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag)
        (src' : TypeResult) (qt_out : QTyp),
        List.foldlM joinStep acc rs' = .ok acc' →
        src' ∈ rs' →
        acc'.2.1.lookup l = some qt_out →
        qt_out.pred = Predicate.guardClosure k arg_name pred_body var_env →
        ∃ qt_src', src'.memEnv'.lookup l = some qt_src' ∧
          qt_src'.pred = Predicate.guardClosure k arg_name pred_body var_env := by
    intro rs' acc acc' src' qt_out hfold hmem_src' hlookup_out hpred_out
    induction rs' generalizing acc acc' src' qt_out with
    | nil =>
        cases hmem_src'
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
            rcases (List.mem_cons.mp hmem_src') with hsrc_eq | hsrc_tail
            · subst src'
              rcases h_fold_left_guardClosure
                  (rs' := xs) (acc := acc1) (acc' := acc') (qt_out := qt_out)
                  hfold_tail hlookup_out hpred_out with
                ⟨qt_acc1, hlookup_acc1, hpred_acc1⟩
              rcases
                  joinMemEnvsStrong_lookup_guardClosure_implies_right
                    (env1 := acc.2.1) (env2 := x.memEnv') (l := l) (qt := qt_acc1)
                    (k := k) (arg_name := arg_name) (pred_body := pred_body) (var_env := var_env)
                    (hlookup_join := by simpa [acc1] using hlookup_acc1)
                    (hpred_join := hpred_acc1)
                with ⟨qt_x, hlookup_x, hpred_x⟩
              exact ⟨qt_x, hlookup_x, hpred_x⟩
            · exact
                ih (acc := acc1) (acc' := acc') (src' := src') (qt_out := qt_out)
                  hfold_tail hsrc_tail hlookup_out hpred_out
  cases hqt : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqt, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, TypecheckM] at _h_join
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
          erw [hcheck] at _h_join
          simp at _h_join
      | ok _ =>
          erw [hcheck] at _h_join
          simp at _h_join
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                  first.nextTag') rest with
          | error err =>
              erw [hfold] at _h_join
              simp at _h_join
          | ok a =>
              erw [hfold] at _h_join
              simp at _h_join
              subst res
              have hlookup_res' : a.2.1.lookup l = some qt := by
                simpa [ctxAfter] using hlookup_res
              rcases (List.mem_cons.mp _hmem_src) with hsrc_head | hsrc_tail
              · subst src
                rcases
                    h_fold_left_guardClosure
                      rest
                      (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                        first.nextTag')
                      a qt hfold hlookup_res' hpred_res
                  with ⟨qt_first, hlookup_first, hpred_first⟩
                exact ⟨qt_first, by simpa [ctxAfter] using hlookup_first, hpred_first⟩
              · rcases
                    h_fold_member_guardClosure
                      rest
                      (etyp, first.memEnv', poison, pred, first.tagEnv', first.regime', first.nextLoc',
                        first.nextTag')
                      a src qt hfold hsrc_tail hlookup_res' hpred_res
                  with ⟨qt_src, hlookup_src, hpred_src⟩
                exact ⟨qt_src, by simpa [ctxAfter] using hlookup_src, hpred_src⟩
lemma joinTypeResults_transport_consistentWithRegime_from_member
  (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : consistentWithRegime predSat (ctxAfter ctx src).regime (ctxAfter ctx src) μ ρ θ) :
  consistentWithRegime predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  unfold consistentWithRegime at h_src ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred_res : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred_res] at hguard
    | guardOnly k' =>
        exact locsRegime.guardOnly_ok (l, qt) k' hpred_res
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred_res]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinTypeResults_lookup_member_guardClosure_lookup_compat
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              _h_join _hmem_src l qt k' arg_name pred_body var_env hlookup hpred_res
          with ⟨qt_src, hlookup_src, hpred_src⟩
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [hk_eq] using hkres)
          | some b =>
              have hk_src : (ctxAfter ctx src).regime.lookup? k' = some b := hlookup_back k' b hkres
              rw [hk_src] at hnone
              contradiction
        have hguard_src : qtypGuardTag qt_src = some k' := by
          simp [qtypGuardTag, hpred_src]
        have hloc_src := h_src.1 l qt_src k' hlookup_src hguard_src hRdef_src
        cases hloc_src with
        | noPred_ok hnp =>
            simp [qtypGuardTag, hpred_src] at hnp
        | guardOnly_ok _ hgo =>
            simp [hpred_src] at hgo
        | withPred_ok k_src arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
            have hclos0 : qt_src.pred = Predicate.guardClosure k_src arg_name' pred_body' var_env' := by
              simpa using hclos
            have hk_src_eq : qtypGuardTag qt_src = some k_src := by
              simp [qtypGuardTag, hclos0]
            have hk_tag_eq : k_src = k' := by
              have : some k_src = some k' := by
                calc
                  some k_src = qtypGuardTag qt_src := by symm; exact hk_src_eq
                  _ = some k' := hguard_src
              exact Option.some.inj this
            have hclos' : qt_src.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
              simpa [hk_tag_eq] using hclos0
            have hreg' : (ctxAfter ctx src).regime.lookup? k' = some b := by
              simpa [hk_tag_eq] using hreg
            have hpred_ctor_eq :
                Predicate.guardClosure k' arg_name' pred_body' var_env' =
                  Predicate.guardClosure k' arg_name pred_body var_env := by
              calc
                Predicate.guardClosure k' arg_name' pred_body' var_env' = qt_src.pred := by
                  simpa using hclos'.symm
                _ = Predicate.guardClosure k' arg_name pred_body var_env := hpred_src
            cases hpred_ctor_eq
            have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
              cases hkres : (ctxAfter ctx res).regime.lookup? k' with
              | none =>
                  exact False.elim (hRdef (by simpa [hk_eq] using hkres))
              | some b' =>
                  have hk_src' : (ctxAfter ctx src).regime.lookup? k' = some b' := hlookup_back k' b' hkres
                  have hb_eq : b = b' := by
                    have : some b = some b' := by
                      calc
                        some b = (ctxAfter ctx src).regime.lookup? k' := by symm; exact hreg'
                        _ = some b' := hk_src'
                    exact Option.some.inj this
                  simp [hb_eq]
            have hpred_eq : qt_src.pred = qt.pred := by
              simp [hpred_src, hpred_res]
            have hcons_res :
                (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
              refine ⟨?_, ?_⟩
              · intro hb
                exact
                  qtypPredHolds_transport_pred
                    (predSat := predSat) (qt := qt_src) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
              · intro hb
                exact
                  qtypPredHolds_transport_pred_not
                    (predSat := predSat) (qt := qt_src) (qt' := qt)
                    (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
            exact
              locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                hpred_res hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k ≠ none := by
          intro hnone
          have hk_src := hlookup_back k b hkres
          rw [hk_src] at hnone
          contradiction
        have hvar_src :=
          h_src.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_src
        exact
          varsRegime_transport_active_lookup_back
            (predSat := predSat)
            (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
            (μ := μ) (ρ := ρ) (entry := (x, qt))
            hlookup_back hguard hkres hvar_src
  · intro x qt v hlookup hlookup_v
    have hcap_src :
        closureCapturedVarsRegime predSat (ctxAfter ctx src).regime qt μ θ v :=
      h_src.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegime_transport_lookup_back
        (predSat := predSat)
        (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_src

lemma joinTypeResults_transport_consistentWithRegimeMasked_from_member
  (masked : Tag → Prop) (predSat : PredSat)
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (h_src : consistentWithRegimeMasked masked predSat (ctxAfter ctx src).regime (ctxAfter ctx src) μ ρ θ) :
  consistentWithRegimeMasked masked predSat (ctxAfter ctx res).regime (ctxAfter ctx res) μ ρ θ := by
  have hlookup_back :
      ∀ k b, (ctxAfter ctx res).regime.lookup? k = some b →
        (ctxAfter ctx src).regime.lookup? k = some b := by
    intro k b hk
    exact
      joinTypeResults_lookup_member_regime_compat
        (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
        _h_join _hmem_src k b hk
  unfold consistentWithRegimeMasked at h_src ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hRdef
    cases hpred_res : qt.pred with
    | noPred =>
        simp [qtypGuardTag, hpred_res] at hguard
    | guardOnly k' =>
        exact Or.inr (locsRegime.guardOnly_ok (l, qt) k' hpred_res)
    | guardClosure k' arg_name pred_body var_env =>
        have hk_eq : k' = k := by
          have : some k' = some k := by
            calc
              some k' = qtypGuardTag qt := by simp [qtypGuardTag, hpred_res]
              _ = some k := hguard
          exact Option.some.inj this
        rcases
            joinTypeResults_lookup_member_guardClosure_lookup_compat
              (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
              _h_join _hmem_src l qt k' arg_name pred_body var_env hlookup hpred_res
          with ⟨qt_src, hlookup_src, hpred_src⟩
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k' ≠ none := by
          intro hnone
          cases hkres : (ctxAfter ctx res).regime.lookup? k' with
          | none =>
              exact hRdef (by simpa [hk_eq] using hkres)
          | some b =>
              have hk_src : (ctxAfter ctx src).regime.lookup? k' = some b := hlookup_back k' b hkres
              rw [hk_src] at hnone
              contradiction
        have hguard_src : qtypGuardTag qt_src = some k' := by
          simp [qtypGuardTag, hpred_src]
        have hloc_src := h_src.1 l qt_src k' hlookup_src hguard_src hRdef_src
        cases hloc_src with
        | inl hmasked =>
            exact Or.inl (by simpa [hk_eq] using hmasked)
        | inr hloc_src =>
            cases hloc_src with
            | noPred_ok hnp =>
                simp [qtypGuardTag, hpred_src] at hnp
            | guardOnly_ok _ hgo =>
                simp [hpred_src] at hgo
            | withPred_ok k_src arg_name' pred_body' var_env' a n b hclos hreg hreal hmem hcons =>
                have hclos0 : qt_src.pred = Predicate.guardClosure k_src arg_name' pred_body' var_env' := by
                  simpa using hclos
                have hk_src_eq : qtypGuardTag qt_src = some k_src := by
                  simp [qtypGuardTag, hclos0]
                have hk_tag_eq : k_src = k' := by
                  have : some k_src = some k' := by
                    calc
                      some k_src = qtypGuardTag qt_src := by symm; exact hk_src_eq
                      _ = some k' := hguard_src
                  exact Option.some.inj this
                have hclos' : qt_src.pred = Predicate.guardClosure k' arg_name' pred_body' var_env' := by
                  simpa [hk_tag_eq] using hclos0
                have hreg' : (ctxAfter ctx src).regime.lookup? k' = some b := by
                  simpa [hk_tag_eq] using hreg
                have hpred_ctor_eq :
                    Predicate.guardClosure k' arg_name' pred_body' var_env' =
                      Predicate.guardClosure k' arg_name pred_body var_env := by
                  calc
                    Predicate.guardClosure k' arg_name' pred_body' var_env' = qt_src.pred := by
                      simpa using hclos'.symm
                    _ = Predicate.guardClosure k' arg_name pred_body var_env := hpred_src
                cases hpred_ctor_eq
                have hreg_res : (ctxAfter ctx res).regime.lookup? k' = some b := by
                  cases hkres : (ctxAfter ctx res).regime.lookup? k' with
                  | none =>
                      exact False.elim (hRdef (by simpa [hk_eq] using hkres))
                  | some b' =>
                      have hk_src' : (ctxAfter ctx src).regime.lookup? k' = some b' := hlookup_back k' b' hkres
                      have hb_eq : b = b' := by
                        have : some b = some b' := by
                          calc
                            some b = (ctxAfter ctx src).regime.lookup? k' := by symm; exact hreg'
                            _ = some b' := hk_src'
                        exact Option.some.inj this
                      simp [hb_eq]
                have hpred_eq : qt_src.pred = qt.pred := by
                  simp [hpred_src, hpred_res]
                have hcons_res :
                    (b = true → qtypPredHolds predSat qt μ (Value.num n)) ∧
                    (b = false → ¬ qtypPredHolds predSat qt μ (Value.num n)) := by
                  refine ⟨?_, ?_⟩
                  · intro hb
                    exact
                      qtypPredHolds_transport_pred
                        (predSat := predSat) (qt := qt_src) (qt' := qt)
                        (μ := μ) (v := Value.num n) hpred_eq (hcons.1 hb)
                  · intro hb
                    exact
                      qtypPredHolds_transport_pred_not
                        (predSat := predSat) (qt := qt_src) (qt' := qt)
                        (μ := μ) (v := Value.num n) hpred_eq (hcons.2 hb)
                exact Or.inr <|
                  locsRegime.withPred_ok (l, qt) k' arg_name pred_body var_env a n b
                    hpred_res hreg_res hreal hmem hcons_res
  · intro x qt k hlookup hguard hRdef
    cases hkres : (ctxAfter ctx res).regime.lookup? k with
    | none =>
        exact False.elim (hRdef hkres)
    | some b =>
        have hRdef_src : (ctxAfter ctx src).regime.lookup? k ≠ none := by
          intro hnone
          have hk_src := hlookup_back k b hkres
          rw [hk_src] at hnone
          contradiction
        have hvar_src :=
          h_src.2.1 x qt k
            (by simpa [ctxAfter] using hlookup)
            hguard
            hRdef_src
        cases hvar_src with
        | inl hmasked =>
            exact Or.inl hmasked
        | inr hvar_src =>
            exact Or.inr <|
              varsRegime_transport_active_lookup_back
                (predSat := predSat)
                (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
                (μ := μ) (ρ := ρ) (entry := (x, qt))
                hlookup_back hguard hkres hvar_src
  · intro x qt v hlookup hlookup_v
    have hcap_src :
        closureCapturedVarsRegimeMasked masked predSat (ctxAfter ctx src).regime qt μ θ v :=
      h_src.2.2 x qt v
        (by simpa [ctxAfter] using hlookup)
        hlookup_v
    exact
      closureCapturedVarsRegimeMasked_transport_lookup_back
        (masked := masked) (predSat := predSat)
        (R := (ctxAfter ctx src).regime) (R' := (ctxAfter ctx res).regime)
        (qt := qt) (μ := μ) (θ := θ) (v := v)
        hlookup_back hcap_src


lemma joinTypeResults_lookup_member_clean_compat
  (ctx : TypeContext) (first src : TypeResult) (rest : List TypeResult) (res : TypeResult)
  (_h_join : joinTypeResults ctx first rest = .ok res)
  (_hmem_src : src ∈ first :: rest)
  (l : Loc) (qt qt_src : QTyp)
  (hlookup_res : (ctxAfter ctx res).memEnv.lookup l = some qt)
  (hclean_res : qtypCleanUnder (ctxAfter ctx res).regime qt)
  (hlookup_src : (ctxAfter ctx src).memEnv.lookup l = some qt_src) :
  qtypCleanUnder (ctxAfter ctx src).regime qt_src := by
  cases hclean_res with
  | clean hpoison =>
      exact qtypCleanUnder.clean
        (joinTypeResults_lookup_member_poison_imp
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src hpoison)
  | guard k htag hreg hnotfun =>
      have htag_src : qtypGuardTag qt_src = some k :=
        joinTypeResults_lookup_member_guardTag_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src k hlookup_res hlookup_src htag
      have hreg_src : (ctxAfter ctx src).regime.lookup? k = some true :=
        joinTypeResults_lookup_member_regime_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src k true hreg
      have hetyp_eq : qt.etyp = qt_src.etyp :=
        joinTypeResults_lookup_member_etyp_compat
          (ctx := ctx) (first := first) (src := src) (rest := rest) (res := res)
          _h_join _hmem_src l qt qt_src hlookup_res hlookup_src
      have hnotfun_src : qt_src.etyp.isFunctionType = false := by
        simpa [hetyp_eq.symm] using hnotfun
      exact qtypCleanUnder.guard k htag_src hreg_src hnotfun_src
