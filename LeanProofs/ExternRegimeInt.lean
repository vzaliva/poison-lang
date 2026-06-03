/-
  ExternRegimeInt.lean

  Lemmas about the extern-regime typechecking primitives for predicate-bearing
  ("open"-style) externs, plus a theorem characterising when the trusted-registry
  fault-robustness theorem can be instantiated for a program that names an extern.

  - `collectAndAllocExternTags_pred` / `applyExternRegimePolicy_singleton`: a
    single output predicate allocates exactly one fresh tag, and the regime policy
    inserts `freshTag ↦ b` for it — so a predicate-bearing extern result changes
    the regime, unlike the empty-mapping `noPred` case.
  - `valueConsistentWithRegime_int_inRegimeTrue`: value-consistency for an int
    output that the regime de-poisons (`R(k) = some true`).
  - `nonempty_registry_hagrees_unprovable`: the OLD all-context
    `TrustedRegistryAgreesWithReachable` premise (now retained only via
    `TypeSystemEnforcesFaultRobustness_allCtx`) is falsifiable for any non-empty
    registry — so the all-context theorem instantiates non-trivially only via the
    empty registry.
  - `open_empty_context_hagrees_provable`: the positive dual.  After the
    per-context reshape (`TypeSystemEnforcesFaultRobustness` /
    `TypeSystemEnforcesFaultRobustness_at`), the per-context premise IS provable
    for a NON-EMPTY registry at the canonical empty initial context, where
    reachability collapses to the program AST.  This demonstrates the obstruction
    is removed (theorem-shape only; the §4.6 dynamic materialisation of the
    de-poisoned value is separate, larger work).
  - `open_empty_context_FR_instantiable`: the capstone — composing the witness
    with `TypeSystemEnforcesFaultRobustness_at` yields the FR conclusion itself
    (`FaultRobustnessSpecForCtx`) for a NON-EMPTY registry at the empty context,
    so the reshaped theorem is *instantiable* (still parameterised over
    `impl`/`spec`; no concrete extern boundary spec is constructed).
-/
import LeanProofs.FaultRobustnessProofs

open Std
open LeanPoison

namespace ExternRegimeInt

/-- The allocator on a single `guardClosure` predicate allocates exactly one fresh
    tag `nextTag` for index `idx`, advancing to `nextTag + 1`.  Contrast
    `collectAndAllocExternTags_noPred`, which yields the empty map. -/
theorem collectAndAllocExternTags_pred (idx : TagIndex) (nm : Name) (body : Expr) (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.guardClosure idx nm body] nextTag
      = .ok (({} : ExtTreeMap TagIndex Tag).insert idx nextTag, nextTag + 1) := by
  rfl

/-- A singleton `ExtTreeMap` lists to a single pair (one node, no ordering
    sensitivity). -/
theorem extTreeMap_toList_singleton (idx : TagIndex) (t : Tag) :
    (({} : ExtTreeMap TagIndex Tag).insert idx t).toList = [(idx, t)] := by
  rfl

/-- On a singleton tag mapping, the regime policy inserts exactly `freshTag ↦ b`
    when the policy says `some b` and `freshTag` is not already governed.  Contrast
    the `noPred` case, where the empty mapping leaves the regime unchanged. -/
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
    obligation `qtypPredHolds` is supplied as a hypothesis. -/
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

/-! ## The non-empty-registry instantiation obstruction (old all-context premise)

    The OLD all-context FR premise — now retained only as
    `TypeSystemEnforcesFaultRobustness_allCtx` — took a `hagrees` premise
    `∀ {ctx}, ctxMatchesInputSpec s ctx → TrustedRegistryAgreesWithReachable e ctx tr`.
    With `tr = []` it is vacuous (lookup never succeeds), but then the runtime
    registry is empty and the extern never runs.

    For a non-empty registry, that all-context `hagrees` is UNPROVABLE:
    `ctxMatchesInputSpec` constrains `ctx.varEnv` only one-way
    (`s.vars ⊆ ctx.varEnv`), so an adversarial `ctx` may bind a rogue variable to
    an arrow type whose closure list contains an extern member for the registered
    id but with a different declaration.  The `var → arrow_extern_member`
    reachability path then reaches that id with a decl `≠` the registry's,
    falsifying `TrustedRegistryAgreesWithReachable`.

    The theorem below proves this concretely.  The per-context reshape removed the
    obstruction: the public `TypeSystemEnforcesFaultRobustness` now takes the
    trust premise per initial context, which is provable for a non-empty registry
    — see `open_empty_context_hagrees_provable` / `open_empty_context_FR_instantiable`
    further down. -/

/-- Registered declaration: a `fn` extern @238 returning a clean int. -/
def regDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.int, argName := some "p",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [], preds := [], argPoison := false }

/-- A rogue arrow QTyp whose closure list holds an extern member for @238 but
    over argument type `bool` — so the reachable decl differs from `regDecl`
    (which is over `int`).  `noPred` ⇒ no guard tag; empty captured env. -/
def rogueQTyp : QTyp :=
  { etyp := ETyp.arrow Typ.bool Typ.int false
      [FnTClosure.extern 238 "q" (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) []
        [] ⟨ETyp.bool, false, Predicate.noPred⟩],
    poison := false, pred := Predicate.noPred }

/-- The decl the `arrow_extern_member` path reconstructs from `rogueQTyp` (typ =
    the arrow source `bool`). -/
def rogueDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.bool, argName := some "q",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [],
    preds := collectExternPreds (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [],
    argPoison := false }

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
        (effects := []) (σcap := []) (argQt := ⟨ETyp.bool, false, Predicate.noPred⟩) (by simp)
  have hlookup : TrustedRegistry.lookup? [⟨regDecl, impl, spec⟩] 238
      = some ⟨regDecl, impl, spec⟩ := by
    simp [TrustedRegistry.lookup?, regDecl]
  have hdeclEq : (⟨regDecl, impl, spec⟩ : TrustedExternEntry).decl = rogueDecl :=
    hagrees hmatch hreach hlookup
  simp [regDecl, rogueDecl] at hdeclEq

/-! ## Provability witness: the per-context premise IS provable at the empty context

    The positive dual to `nonempty_registry_hagrees_unprovable`.  The reshaped FR
    theorem (`TypeSystemEnforcesFaultRobustness`) requires registry agreement only
    for the *actual* initial context (`InitialContextTrusted`/per-context
    `TrustedRegistryAgreesWithReachable`).  At the canonical empty initial context
    (`varEnv = {}`) reachability collapses to the program AST (the `var` branch
    cannot fire), so the premise is provable for a NON-EMPTY registry — exactly
    what the old all-context premise made impossible.  This demonstrates the
    obstruction is removed (theorem-shape only; the §4.6 *dynamic* materialisation
    of the de-poisoned value is separate, larger work). -/

/-- A minimal program declaring extern `@238` (a `fn` over `int`). -/
def openProg : Expr :=
  Expr.externFn 238 "p" Typ.int false SyntaxPredicate.noPred (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) []

/-- The declaration the `externFn` AST node exposes — matches the
    `ExternDeclarationInProgram.externFn` shape exactly. -/
def openDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.int, argName := some "p",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [],
    preds := collectExternPreds (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [],
    argPoison := false }

/-- Canonical empty initial typing context (no bound variables). -/
def openEmptyCtx : TypeContext :=
  { pc := false, regime := {}, memEnv := {}, varEnv := {},
    tagEnv := {}, nextLoc := 0, nextTag := 0, pureCtx := false }

/-- The single-extern program's only declaration is `openDecl`: invert
    `ExternDeclarationInProgram` on the `externFn` node.  The `externFn_return`
    branch is vacuous because `ExternReturn.simple` carries no nested extern. -/
theorem openProg_agreesWithProgram (impl : ExternImpl)
    (spec : ExternBoundarySpec openDecl impl) :
    TrustedRegistryAgreesWithProgram openProg [⟨openDecl, impl, spec⟩] := by
  intro id d entry hprog hlookup
  unfold openProg at hprog
  cases hprog with
  | externFn =>
      have hl : TrustedRegistry.lookup? ([⟨openDecl, impl, spec⟩] : TrustedRegistry) 238
          = some ⟨openDecl, impl, spec⟩ := by simp [TrustedRegistry.lookup?, openDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externFn_return hret => cases hret

/-- Provability witness: for a NON-EMPTY registry containing `@238`, the
    per-context trust premise `TrustedRegistryAgreesWithReachable` holds at the
    canonical empty initial context.  The direct dual to
    `nonempty_registry_hagrees_unprovable` (parameterised over `impl`/`spec`,
    just like it), demonstrating the per-context reshape removes the obstruction. -/
theorem open_empty_context_hagrees_provable (impl : ExternImpl)
    (spec : ExternBoundarySpec openDecl impl) :
    TrustedRegistryAgreesWithReachable openProg openEmptyCtx [⟨openDecl, impl, spec⟩] :=
  agreesWithReachable_of_emptyVarEnv (by rfl) (openProg_agreesWithProgram impl spec)

/-- Capstone: the reshaped FR theorem is *instantiable* for a NON-EMPTY registry.
    Composing the witness with `TypeSystemEnforcesFaultRobustness_at` discharges
    the per-context trust premise and yields the FR conclusion itself
    (`FaultRobustnessSpecForCtx`) at the canonical empty context.  This is what the
    old all-context premise made impossible.  Still parameterised over
    `impl`/`spec`: no concrete extern boundary spec is built (that — the §4.6
    *dynamic* materialisation of the de-poisoned value — is separate, larger
    work). -/
theorem open_empty_context_FR_instantiable (impl : ExternImpl)
    (spec : ExternBoundarySpec openDecl impl) (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry [⟨openDecl, impl, spec⟩])
      openProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at [⟨openDecl, impl, spec⟩] openProg s obs openEmptyCtx
    (open_empty_context_hagrees_provable impl spec)

end ExternRegimeInt
