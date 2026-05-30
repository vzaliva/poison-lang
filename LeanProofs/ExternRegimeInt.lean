/-
  ExternRegimeInt.lean - Phase-D foundation (predicate-bearing "open" extern).

  Bottom-up, riskiest-first construction of a predicate-bearing ("open") extern
  trusted-registry instantiation that de-poisons under a true regime policy.
  Lemma order follows doc/extern-regime-impl-plan.md "PHASE D — remaining".

  STATUS (session 5): the two genuinely-uncertain STRUCTURAL divergence points
  vs. the clean noPred spec are VERIFIED here (both build, 0 sorry / 0 axiom):
    (a) `collectAndAllocExternTags_pred` — the allocator yields one fresh tag.
    (b) `applyExternRegimePolicy_singleton` — the regime gains `freshTag ↦ b`,
        so the result regime genuinely changes (ctxAfter ≠ ctx for predicates).
  The cross-run discriminator is resolved in the plan doc: the obligation is
  `agreeValueUnder` via `withPred_true_eq` (output equality), dischargeable by
  the `clean_agree` determinism shape — NOT predicate-satisfaction.

  REMAINING: the full `ExternBoundarySpec` (declFR/callFR/declSingle/callSingle/
  operational) + `TrustedExternEntry` + `TrustedRegistry` + `InputSpec` + the
  top-level `TypeSystemEnforcesFaultRobustness` instantiation.  NOTE: there is NO
  template anywhere — even `PureUnaryCleanIntSpec` (the clean analogue) is never
  assembled into a registry; this would be the first complete FR instantiation.
  The assembly needs the "p"rivate` helpers in ExternBoundaryConstructors
  (`stepFRPost_of_parts`, `externBoundarySinglePost_of_parts`, …): either
  un-"p"rivate` them (justified — another file now needs them) or build the spec
  inside ExternBoundaryConstructors and expose only the final record.
-/
import LeanProofs.ExternBoundaryProofs

open Std
open LeanPoison

namespace ExternRegimeInt

/-- Divergence point (a): the allocator on a single `guardClosure` predicate
    allocates exactly one fresh tag `nextTag` for index `idx`, advancing to
    `nextTag + 1`.  Contrast `collectAndAllocExternTags_noPred` (rfl, empty map). -/
theorem collectAndAllocExternTags_pred (idx : TagIndex) (nm : Name) (body : Expr) (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.guardClosure idx nm body] nextTag
      = .ok (({} : ExtTreeMap TagIndex Tag).insert idx nextTag, nextTag + 1) := by
  rfl

/-- A singleton `ExtTreeMap` lists to a single pair (one node, no ordering
    sensitivity). -/
theorem extTreeMap_toList_singleton (idx : TagIndex) (t : Tag) :
    (({} : ExtTreeMap TagIndex Tag).insert idx t).toList = [(idx, t)] := by
  rfl

/-- Divergence point (b): on the singleton tag mapping, the regime policy
    inserts exactly `freshTag ↦ b` when the policy says `some b` and `freshTag`
    is not already governed.  Contrast the noPred case where the empty mapping
    leaves the regime unchanged (identity). -/
theorem applyExternRegimePolicy_singleton
    (R : Regime) (id : ExternId) (policy : ExternId → Tag → Option Bool)
    (idx : TagIndex) (freshTag : Tag) (b : Bool)
    (hpolicy : policy id freshTag = some b)
    (hnone : R.lookup? freshTag = none) :
    applyExternRegimePolicy R id policy (({} : ExtTreeMap TagIndex Tag).insert idx freshTag)
      = R.insert freshTag b := by
  unfold applyExternRegimePolicy
  rw [extTreeMap_toList_singleton]
  simp only [List.foldl_cons, List.foldl_nil, hpolicy, hnone]

/-- Value-consistency for a predicate-bearing int output that the regime
    de-poisons (`R(k) = some true`).  Mirror of `valueConsistentWithRegime_int_noPred`
    but landing in the `inRegimeTrue` constructor; the predicate-satisfaction
    obligation "q"typPredHolds` is supplied (it is one of the two Phase-D trust
    fields). -/
theorem valueConsistentWithRegime_int_inRegimeTrue
    {predSat : PredSat} {R : Regime} {qt : QTyp} {k : Tag}
    {μ : Memory} {θ : RealizationMap} {n : Int}
    (hetyp : qt.etyp = ETyp.int)
    (htag : qtypGuardTag qt = some k)
    (hRk : R.lookup? k = some true)
    (hpred : qtypPredHolds predSat qt μ (Value.num n)) :
    valueConsistentWithRegime predSat R qt μ θ (Value.num n) :=
  valueConsistentWithRegime.inRegimeTrue k htag hRk hpred
    (closureCapturedVarsRegime_nonClosure_of_nonFunctionType
      (by simpa [hetyp] using (valueHasETyp.num (θ := θ) n))
      (by rw [hetyp]; rfl))

/-! ## The non-empty-registry instantiation obstruction

    `TypeSystemEnforcesFaultRobustness` takes a `hagrees` premise
    `∀ {ctx}, ctxMatchesInputSpec s ctx → TrustedRegistryAgreesWithReachable e ctx tr`.
    With `tr = []` it is vacuous (lookup never succeeds), but then the runtime
    registry is empty, the extern never runs, and the de-poisoned value never
    materialises — the de-poisoning is not dynamically exercised.

    For a non-empty registry (so the extern runs and de-poisoning is active),
    `hagrees` is UNPROVABLE: `ctxMatchesInputSpec` constrains `ctx.varEnv` only
    one-way (`s.vars ⊆ ctx.varEnv`), so an adversarial `ctx` may bind a rogue
    variable to an arrow type whose closure list contains an extern member for
    the registered id but with a different declaration.  The `var →
    arrow_extern_member` reachability path then reaches that id with a decl `≠`
    the registry's, falsifying `TrustedRegistryAgreesWithReachable`.

    The theorem below proves this concretely: it exhibits such a context and
    derives a contradiction from the agreement premise.  Hence the meaningful
    (non-empty-registry, de-poisoning-active) Phase-D instantiation is blocked by
    the FR theorem's universal `ctx` quantification, not by any missing lemma. -/

/-- Registered declaration: a `fn` extern @238 returning a clean int. -/
def regDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.int, argName := some "p",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [], preds := [] }

/-- A rogue arrow QTyp whose closure list holds an extern member for @238 but
    over argument type `bool` — so the reachable decl differs from "r"egDecl`
    (which is over `int`).  `noPred` ⇒ no guard tag; empty captured env. -/
def rogueQTyp : QTyp :=
  { etyp := ETyp.arrow Typ.bool Typ.int false
      [FnTClosure.extern 238 "q" (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [] []],
    poison := false, pred := Predicate.noPred }

/-- The decl the `arrow_extern_member` path reconstructs from "r"ogueQTyp` (typ =
    the arrow source `bool`). -/
def rogueDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.bool, argName := some "q",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [],
    preds := collectExternPreds (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [] }

/-- Adversarial typing context: everything empty except one rogue var. -/
def rogueCtx : TypeContext :=
  { pc := false, regime := {}, memEnv := {},
    varEnv := (({} : VarTypeEnv).insert "r" rogueQTyp),
    tagEnv := {}, nextLoc := 0, nextTag := 0, pureCtx := false }

/-- Empty input spec (selects nothing). -/
def emptyInputSpec : InputSpec := { locs := {}, vars := {}, regimeExterns := [] }

theorem nonempty_registry_hagrees_unprovable
    (impl : ExternImpl) (spec : ExternBoundarySpec regDecl impl) (e : Expr) :
    ¬ (∀ {ctx : TypeContext}, ctxMatchesInputSpec emptyInputSpec ctx →
        TrustedRegistryAgreesWithReachable e ctx [⟨regDecl, impl, spec⟩]) := by
  intro hagrees
  -- `rogueCtx.varEnv` lookup characterisation: every successful lookup yields the
  -- single rogue entry.
  have hlookupChar : ∀ {x qt}, VarTypeEnv.lookup rogueCtx.varEnv x = some qt → qt = rogueQTyp := by
    intro x qt hlk
    simp only [rogueCtx, VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?,
      ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_empty] at hlk
    split at hlk
    · exact (Option.some.inj hlk).symm
    · exact absurd hlk (by simp)
  -- rogueCtx satisfies ctxMatchesInputSpec emptyInputSpec.
  have hmatch : ctxMatchesInputSpec emptyInputSpec rogueCtx := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l qt h; simp [emptyInputSpec, MemoryTypeEnv.lookup] at h
    · intro x qt h; simp [emptyInputSpec, VarTypeEnv.lookup] at h
    · intro l qt k h _; simp [rogueCtx, MemoryTypeEnv.lookup] at h
    · refine deepVarEnvProperty.intro _ _ ?_ ?_
      · intro x qt k hlk hguard _
        obtain rfl := hlookupChar hlk
        simp [rogueQTyp, qtypGuardTag] at hguard
      · intro x qt hlk
        obtain rfl := hlookupChar hlk
        refine deepQTypProperty.arrow _ _ ⟨Typ.bool, Typ.int, false, _, by rfl, ?_⟩
        intro tcl htcl
        simp only [List.mem_singleton] at htcl
        subst htcl
        intro x' qt' k' hlk' _ _
        simp [VarTypeEnv.ofCaptured, VarTypeEnv.lookup] at hlk'
  -- Reachability: the rogue var reaches @238 with `rogueDecl ≠ regDecl`.
  have hreach : ExternDeclarationReachableFromContext e rogueCtx 238 rogueDecl := by
    refine ExternDeclarationReachableFromContext.var (x := "r") (qt := rogueQTyp) ?_ ?_
    · simp [rogueCtx, VarTypeEnv.lookup]
    · exact ExternDeclarationReachableFromQTyp.arrow_extern_member
        (st1 := Typ.bool) (st2 := Typ.int) (p := false) (qpoison := false)
        (qpred := Predicate.noPred) (x := "q")
        (retSpec := ExternReturn.simple Typ.int false SyntaxPredicate.noPred)
        (effects := []) (σcap := []) (by simp [rogueQTyp])
  have hlookup : TrustedRegistry.lookup? [⟨regDecl, impl, spec⟩] 238
      = some ⟨regDecl, impl, spec⟩ := by
    simp [TrustedRegistry.lookup?, regDecl]
  have hdeclEq : (⟨regDecl, impl, spec⟩ : TrustedExternEntry).decl = rogueDecl :=
    hagrees hmatch hreach hlookup
  simp [regDecl, rogueDecl] at hdeclEq

end ExternRegimeInt
