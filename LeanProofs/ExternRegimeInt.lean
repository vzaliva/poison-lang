/-
  ExternRegimeInt.lean

  Theorems characterising when the trusted-registry fault-robustness theorem can
  be instantiated for a program that names an extern, plus the program-level FR
  capstones for the `set_err` (`@22`) and `errno` (`@21`) externs.  Imports
  `FaultRobustnessProofs` and `ExternProofs`, so it sits at the top of the proof
  stack.

  - `nonempty_registry_hagrees_unprovable`: the universal
    `TrustedRegistryAgreesWithReachable` premise used by
    `TypeSystemEnforcesFaultRobustness_allCtx` is falsifiable for any non-empty
    registry, so it is not the shape used for concrete non-empty registries.
  - `emptyCtx_FR_of_agreesWithProgram`: the positive dual. The public
    per-context theorem shape (`TypeSystemEnforcesFaultRobustness` /
    `TypeSystemEnforcesFaultRobustness_at`) is provable for a non-empty registry
    at the canonical empty initial context, where reachability collapses to the
    program AST: a program-level `TrustedRegistryAgreesWithProgram` witness then
    suffices. A trusted guarded-value producer is not covered here.
  - `open_empty_context_FR_instantiable`: composing the witness
    with `TypeSystemEnforcesFaultRobustness_at` yields the FR conclusion itself
    (`FaultRobustnessSpecForCtx`) for a NON-EMPTY registry at the empty context,
    so the per-context theorem is *instantiable* (parameterised over
    `impl`/`spec`; no concrete extern boundary spec is constructed).
  - `setErrWriteEffect_FR`: the concrete counterpart for the memory-writing
    extern `@22` (`set_err`) — program-level FR for the registry
    `[@22 set_err]` backed by the fully proven `ExternProofs.builtinSetErrSpec`.
  - `errnoExternRef_FR`: program-level FR for the bare `extern ref @21`
    (`errno`) declaration with the registry `[@21 errno]`, backed by
    `ExternProofs.builtinErrnoSpec`.
  - `errnoScenario_FR`: program-level FR for the combined declare-`@21` /
    call-`@22` / dereference program with the two-entry registry `[@21, @22]`.
-/
import LeanProofs.FaultRobustnessProofs
import LeanProofs.ExternProofs

open Std
open LeanPoison

namespace ExternRegimeInt

/-! ## Universal agreement and non-empty registries

    `TypeSystemEnforcesFaultRobustness_allCtx` takes a universal `hagrees`
    premise:
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

    The theorem below proves this concretely. The public
    `TypeSystemEnforcesFaultRobustness` takes trust per initial context, which is
    provable for non-empty registries at suitable contexts; see
    `emptyCtx_FR_of_agreesWithProgram` /
    `open_empty_context_FR_instantiable` further down. -/

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
        [] ⟨ETyp.bool, false, Predicate.noPred⟩ []],
    poison := false, pred := Predicate.noPred }

/-- The decl the `arrow_extern_member` path reconstructs from `rogueQTyp` (typ =
    the arrow source `bool`). -/
def rogueDecl : ExternDeclaration :=
  { id := 238, kind := .fn, typ := Typ.bool, argName := some "q",
    retSpec := some (ExternReturn.simple Typ.int false SyntaxPredicate.noPred),
    effects := [],
    preds := collectExternPreds (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [],
    argPoison := false, captures := [] }

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

    The positive dual to `nonempty_registry_hagrees_unprovable`. The public FR
    theorem (`TypeSystemEnforcesFaultRobustness`) requires registry agreement only
    for the actual initial context (`InitialContextTrusted`/per-context
    `TrustedRegistryAgreesWithReachable`).  At the canonical empty initial context
    (`varEnv = {}`) reachability collapses to the program AST (the `var` branch
    cannot fire), so the premise is provable for a non-empty registry. A trusted
    guarded-value producer is not covered here. -/

/-- A minimal program declaring extern `@238` (a `fn` over `int`). -/
def openProg : Expr :=
  Expr.externFn 238 "p" Typ.int false SyntaxPredicate.noPred (ExternReturn.simple Typ.int false SyntaxPredicate.noPred) [] []

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

/-- Fuse the empty-context registry-agreement bridge with the top-level FR
    theorem: at the canonical empty initial context (`openEmptyCtx`), a
    program-level `TrustedRegistryAgreesWithProgram` witness suffices to conclude
    `FaultRobustnessSpecForCtx`.  Shared by the program-level capstones in this
    file. -/
private theorem emptyCtx_FR_of_agreesWithProgram
    (tr : TrustedRegistry) (e : Expr) (s : InputSpec) (obs : ObservableSpec)
    (hprog : TrustedRegistryAgreesWithProgram e tr) :
    FaultRobustnessSpecForCtx (TrustedRegistry.toRuntimeRegistry tr) e s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at tr e s obs openEmptyCtx
    (agreesWithReachable_of_emptyVarEnv (by rfl) hprog)

/-- The single-extern program's only declaration is `openDecl`: invert
    `ExternDeclarationInProgram` on the `externFn` node.  The `externFn_return`
    branch is vacuous because `ExternReturn.simple` carries no nested extern. -/
private theorem openProg_agreesWithProgram (impl : ExternImpl)
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

/-- Capstone: the per-context FR theorem is *instantiable* for a NON-EMPTY registry.
    Composing the program-agreement witness with the top-level FR theorem (via
    `emptyCtx_FR_of_agreesWithProgram`) discharges the per-context trust premise
    and yields the FR conclusion itself (`FaultRobustnessSpecForCtx`) at the
    canonical empty context. Parameterised over `impl`/`spec`: no concrete
    guarded producer extern boundary spec is built here. -/
theorem open_empty_context_FR_instantiable (impl : ExternImpl)
    (spec : ExternBoundarySpec openDecl impl) (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry [⟨openDecl, impl, spec⟩])
      openProg s obs openEmptyCtx :=
  emptyCtx_FR_of_agreesWithProgram [⟨openDecl, impl, spec⟩] openProg s obs
    (openProg_agreesWithProgram impl spec)

/-! ## Program-level fault-robustness for the `set_err` write effect

Where `MaxCurriedFR` / `GuardedCapturesFR` / `MemReadCapturesFR` exercise *read*
dependencies of pure externs, the impure extern `@22` declares the write effect
`effects: { !errno :> (int :> clean {}) }`: a successful call writes its (clean,
gated) integer argument through the declaration-captured `errno` reference.

The trusted contract is `ExternProofs.builtinSetErrSpec` — a complete
five-field `ExternBoundarySpec` for a `.fn` (memory-writing) extern.  Its
relational `callFR` field carries the write-specific obligation: the clean argument
condition forces the two runs' written values to agree, the clean captured
`errno` reference forces them to write a **common logical cell**
(`agreeValueUnder_ref_common_loc`), and every other clean location is untouched
by the single-address writes (realization-map injectivity), so `agreeOnClean`
survives the effect.

The program here is the bare `@22` declaration node (mirroring
`memReadCaptures_FR`'s bare-declaration form); the end-to-end behavioural
examples live in `examples/extern_set_err*.poison`.  The `@21`/`@22` *combined*
scenario registry — adding the `errno` reference extern itself — is
`errnoScenario_FR` below. -/

open ExternProofs (setErrProg setErrRegistry setErr_agreesWithProgram)

/-- **Program-level fault-robustness for the `set_err` write effect.**
    Composing the program-agreement witness with the top-level FR theorem (via
    `emptyCtx_FR_of_agreesWithProgram`) yields the FR conclusion for the
    `[@22 set_err]` registry at the empty context — a program-level FR
    result whose trusted registry contains a memory-writing extern. -/
theorem setErrWriteEffect_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry setErrRegistry)
      setErrProg s obs openEmptyCtx :=
  emptyCtx_FR_of_agreesWithProgram setErrRegistry setErrProg s obs setErr_agreesWithProgram

/-! ## Program-level FR for the `@21` `errno` reference extern

Two scenarios (the `extern ref` program-level capstones; see
doc/externs.md, `@21`):

* `errnoExternRef_FR` — the bare `extern ref @21` declaration node, with the
  singleton trusted registry `[@21]` (mirrors `setErrWriteEffect_FR`'s
  bare-declaration form).
* `errnoScenario_FR` — the combined declare-`@21` / call-`@22` / deref
  program with the two-entry trusted registry `[@21, @22]`: the
  conservatively poisoned external cell is written through `set_err`'s
  declared `!errno` effect and then dereferenced.  Its trusted registry
  contains both a reference-valued extern and a memory-writing extern.

The reserved-address distinctness demanded by `ReservedDiscipline`'s first
conjunct is trivial for these registries: `errnoAddr` is the only reserved
address (`@22` is a `.fn` entry). -/

open ExternProofs (builtinErrnoDecl builtinErrnoImpl builtinErrnoSpec
  builtinSetErrDecl builtinSetErrImpl builtinSetErrSpec
  builtinSetErrRetSpec builtinSetErrEffect)

/-! ## Bare-declaration scenario -/

/-- The bare reference-extern declaration node:
    `extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {})`. -/
def errnoProg : Expr :=
  Expr.externRef 21 false SyntaxPredicate.noPred true SyntaxPredicate.noPred

/-- Trusted registry holding the `@21` reference extern with its complete
    `ExternBoundarySpec`. -/
def errnoRegistry : TrustedRegistry :=
  [⟨builtinErrnoDecl, builtinErrnoImpl, builtinErrnoSpec⟩]

/-- The single declaration syntactically reachable in `errnoProg` — the
    top-level `@21` `externRef` node — is matched by the registry. -/
private theorem errno_agreesWithProgram :
    TrustedRegistryAgreesWithProgram errnoProg errnoRegistry := by
  intro id d entry hprog hlookup
  unfold errnoProg at hprog
  cases hprog with
  | externRef =>
      have hl : TrustedRegistry.lookup? errnoRegistry 21
          = some ⟨builtinErrnoDecl, builtinErrnoImpl, builtinErrnoSpec⟩ := by
        simp [errnoRegistry, TrustedRegistry.lookup?, builtinErrnoDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl

/-- **Program-level fault-robustness for the bare `extern ref @21`
    declaration** — a program-level FR result for a reference-valued
    extern. -/
theorem errnoExternRef_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry errnoRegistry)
      errnoProg s obs openEmptyCtx :=
  emptyCtx_FR_of_agreesWithProgram errnoRegistry errnoProg s obs errno_agreesWithProgram

/-! ## Combined declare/write/read scenario -/

/-- The combined errno scenario: declare the reference, write through the
    `@22` `set_err` effect, then dereference:

    ```poison
    let errno = extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {}) in
    (extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
       effects: { !errno :> (int :> clean {}) }) 7;
    !errno
    ```
-/
def errnoScenarioProg : Expr :=
  Expr.vlet "errno"
    (Expr.externRef 21 false SyntaxPredicate.noPred true SyntaxPredicate.noPred)
    (Expr.seq
      (Expr.app
        (Expr.externFn 22 "n" Typ.int false SyntaxPredicate.noPred
          builtinSetErrRetSpec [builtinSetErrEffect] [])
        (Expr.num 7))
      (Expr.deref (Expr.var "errno")))

/-- The combined trusted scenario registry: the reference extern together with
    the write-effect extern. -/
def errnoScenarioRegistry : TrustedRegistry :=
  [⟨builtinErrnoDecl, builtinErrnoImpl, builtinErrnoSpec⟩,
   ⟨builtinSetErrDecl, builtinSetErrImpl, builtinSetErrSpec⟩]

/-- Every declaration syntactically reachable in `errnoScenarioProg` — the
    `@21` `externRef` binding and the `@22` `externFn` callee — is matched by
    the registry.  The `@22` return is `simple unit`, which carries no nested
    extern, and the remaining program nodes declare nothing. -/
private theorem errnoScenario_agreesWithProgram :
    TrustedRegistryAgreesWithProgram errnoScenarioProg errnoScenarioRegistry := by
  intro id d entry hprog hlookup
  unfold errnoScenarioProg at hprog
  cases hprog with
  | vlet_bound h1 =>
      cases h1 with
      | externRef =>
          have hl : TrustedRegistry.lookup? errnoScenarioRegistry 21
              = some ⟨builtinErrnoDecl, builtinErrnoImpl, builtinErrnoSpec⟩ := by
            simp [errnoScenarioRegistry, TrustedRegistry.lookup?, builtinErrnoDecl]
          rw [hl] at hlookup
          cases hlookup
          rfl
  | vlet_body h2 =>
      cases h2 with
      | seq_left h3 =>
          cases h3 with
          | app_fun h4 =>
              cases h4 with
              | externFn =>
                  have hl : TrustedRegistry.lookup? errnoScenarioRegistry 22
                      = some ⟨builtinSetErrDecl, builtinSetErrImpl, builtinSetErrSpec⟩ := by
                    simp [errnoScenarioRegistry, TrustedRegistry.lookup?,
                      builtinErrnoDecl, builtinSetErrDecl]
                  rw [hl] at hlookup
                  cases hlookup
                  rfl
              | externFn_return hret => cases hret
          | app_arg h5 => cases h5
      | seq_right h6 =>
          cases h6 with
          | deref h7 => cases h7

/-- **Program-level fault-robustness for the combined errno scenario**:
    declare the `@21` reference, write through the `@22` `set_err` effect,
    dereference — under the two-entry trusted registry. -/
theorem errnoScenario_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry errnoScenarioRegistry)
      errnoScenarioProg s obs openEmptyCtx :=
  emptyCtx_FR_of_agreesWithProgram errnoScenarioRegistry errnoScenarioProg s obs
    errnoScenario_agreesWithProgram

end ExternRegimeInt
