/-
  ExternBoundaryProofs.lean — Proof-heavy adapters and reachability theorems
  split off from `LeanProofs/ExternBoundary.lean`.

  This module carries the resolution, integration, and reachability
  navigation theorems consumed by the FR proof orchestration but not part
  of the public theorem-facing surface of `ExternBoundary.lean`.  Consumers
  should import this file in place of `ExternBoundary.lean` when they need
  these proof bodies.
-/
import LeanProofs.ExternBoundary

open Std

private theorem TrustedRegistryAgreesWithReachable.resolveDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry} {id : ExternId}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot id d)
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      entry.decl = d := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  exact ⟨entry, hlookup, himpl, hagrees hreachable hlookup⟩

/-- Program-covered admissibility bridge (the "unblocking" direction): if every
    context-reachable extern declaration also occurs in the
    program and the registry agrees with the program, then it agrees with
    everything reachable from `(e, ctx)`.  The two reachability constructors
    (`ast` / `var`) are discharged by `hprog` directly and by `hcover` then
    `hprog` respectively. -/
theorem TrustedRegistryAgreesWithReachable.of_programCover
    {e : Expr} {ctx : TypeContext} {tr : TrustedRegistry}
    (hcover : ∀ {id d}, ContextExternReachable e ctx id d →
                ExternDeclarationInProgram e id d)
    (hprog : TrustedRegistryAgreesWithProgram e tr) :
    TrustedRegistryAgreesWithReachable e ctx tr := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp => exact hprog hp hlookup
  | var hlk hqt => exact hprog (hcover ⟨_, _, hlk, hqt⟩) hlookup

/-- At the canonical empty initial context (`ctx.varEnv = {}`), reachability
    collapses to the program AST: the `var` constructor cannot fire (no variable
    is bound), so registry agreement with the program implies agreement with
    everything reachable.  This is the reduction that makes the per-context trust
    premise *provable* for a non-empty registry — the positive dual to
    `ExternRegimeInt.nonempty_registry_hagrees_unprovable`. -/
theorem agreesWithReachable_of_emptyVarEnv
    {e : Expr} {ctx : TypeContext} {tr : TrustedRegistry}
    (hempty : ctx.varEnv = {})
    (hprog : TrustedRegistryAgreesWithProgram e tr) :
    TrustedRegistryAgreesWithReachable e ctx tr := by
  refine TrustedRegistryAgreesWithReachable.of_programCover ?_ hprog
  intro id d hctxreach
  obtain ⟨x, _qt, hlk, _hqt⟩ := hctxreach
  rw [hempty] at hlk
  simp [VarTypeEnv.lookup] at hlk

private theorem TrustedRegistryAgreesWithReachable.resolveFnDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn} {effects : List Effect} {captures : List Capture}
    {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := captures })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hreachable hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesFn, hdecl]

private theorem TrustedRegistryAgreesWithReachable.resolvePfnDeclaration
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool}
    {retSpec : ExternReturn} {impl : ExternImpl} {memberCap : List Capture}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := memberCap })
    (hlookupRuntime : (TrustedRegistry.toRuntimeRegistry tr).get? id = some impl) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      entry.impl = impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap := by
  rcases TrustedRegistry.runtime_lookup_exists hlookupRuntime with ⟨entry, hlookup, himpl⟩
  have hdecl := hagrees hreachable hlookup
  refine ⟨entry, hlookup, himpl, ?_⟩
  simp [TrustedRegistryEntryMatchesPfn, hdecl]

theorem ExternDeclBoundarySingleMaskedContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {masked : Tag → Prop} {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot d.id d) :
    ExternDeclBoundarySingleMaskedContract masked postExpr ctx res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl := by
  intro hpredlaws hExtTyping hwfTm hTmBounded htyped μ ρ θ cf o hθwf hwf hric
    hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg hres hrd hrun hpc
  have hlookupRun := ExternDeclBoundaryRun.lookup hrun
  have hlookupRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl := hlookupRun
  rcases
      TrustedRegistryAgreesWithReachable.resolveDeclaration hagrees hreachable hlookupRuntime
    with ⟨entry, _hlookupEntry, himpl, hdecl⟩
  have hrunEntry :
      ExternDeclBoundaryRun entry.decl entry.impl ctx res
        { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf o := by
    simpa [hdecl, himpl] using hrun
  have htypedEntry : ExternBoundaryTyping.Decl entry.decl postExpr ctx res := by
    simpa [hdecl] using htyped
  exact
    ExternDeclBoundarySingleMaskedContract.of_spec
      (masked := masked) (postExpr := postExpr) (ctx := ctx) (res := res)
      (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded htypedEntry μ ρ θ cf o hθwf hwf hric
      hreg hmasked_none hmasked_absent hmasked_bounded hbnd hctxCons a pm hwfcfg hres hrd hrunEntry hpc

theorem ExternDeclBoundaryFRContract.of_trustedReachable
    {tr : TrustedRegistry} {root : Expr} {ctxRoot : TypeContext}
    {ctx : TypeContext} {postExpr : Expr} {res : TypeResult}
    {predSat : PredSat} {tm : TagMeaning}
    {d : ExternDeclaration} {impl₀ impl₁ : ExternImpl}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    (hreachable : ExternDeclarationReachableFromContext root ctxRoot d.id d) :
    ExternDeclBoundaryFRContract ctx postExpr res predSat tm
      (TrustedRegistry.toRuntimeRegistry tr) d impl₀ impl₁ := by
  intro hpredlaws hExtTyping hwfTm hTmBounded htyped μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
    o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
    a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrun₀ hrun₁
  have hlookupRun₀ := ExternDeclBoundaryRun.lookup hrun₀.run
  have hlookupRun₁ := ExternDeclBoundaryRun.lookup hrun₁.run
  have hlookupRuntime₀ :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl₀ := hlookupRun₀
  have hlookupRuntime₁ :
      (TrustedRegistry.toRuntimeRegistry tr).get? d.id = some impl₁ := hlookupRun₁
  have himpl₁₀ : impl₁ = impl₀ :=
    Option.some.inj (hlookupRuntime₁.symm.trans hlookupRuntime₀)
  rcases
      TrustedRegistryAgreesWithReachable.resolveDeclaration hagrees hreachable hlookupRuntime₀
    with ⟨entry, _hlookupEntry, himpl₀, hdecl⟩
  have hrunEntry₀ :
      ExternDeclBoundaryRunForExpr postExpr entry.decl entry.impl ctx res
        { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₀ o₀ := by
    simpa [hdecl, himpl₀] using hrun₀
  have hrunEntry₁ :
      ExternDeclBoundaryRunForExpr postExpr entry.decl entry.impl ctx res
        { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm,
          registry := TrustedRegistry.toRuntimeRegistry tr } cf₁ o₁ := by
    simpa [hdecl, himpl₀, himpl₁₀] using hrun₁
  have htypedEntry : ExternBoundaryTyping.Decl entry.decl postExpr ctx res := by
    simpa [hdecl] using htyped
  exact
    ExternDeclBoundaryFRContract.of_spec
      (ctx := ctx) (postExpr := postExpr) (res := res) (predSat := predSat)
      (tm := tm) (registry := TrustedRegistry.toRuntimeRegistry tr)
      (d := entry.decl) (impl := entry.impl) entry.spec
      hpredlaws hExtTyping hwfTm hTmBounded htypedEntry μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁
      o₀ o₁ hθ₀ hθ₁ hwf htagBounded hric₀ hric₁ hreg hcwr₀ hcwr₁ hagree
      a₀ a₁ pm hwfcfg₀ hwfcfg₁ hres₀ hres₁ hrd₀ hrd₁ hrunEntry₀ hrunEntry₁

theorem TrustedRegistryAgreesWithReachable.callBoundaryRunFn
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool} {retSpec : ExternReturn}
    {effects : List Effect} {captures : List Capture}
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .fn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := effects,
          preds := collectExternPreds retSpec effects, argPoison := argPoison,
          captures := captures })
    {implFn : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address)}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value} {mem' : Memory} {addr' : Address}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hpure : callEntry.callConfig.pureMode = false)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.fn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw, mem', addr'))
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = { callEntry.callConfig with memory := mem', nextAddr := addr' }) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.fn implFn) := by
    simpa [hregistry] using hGet
  rcases
      TrustedRegistryAgreesWithReachable.resolveFnDeclaration
        hagrees hreachable hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects captures := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem TrustedRegistryAgreesWithReachable.callBoundaryRunPfn
    {root : Expr} {ctxRoot : TypeContext} {tr : TrustedRegistry}
    (hagrees : TrustedRegistryAgreesWithReachable root ctxRoot tr)
    {id : ExternId} {x : Name} {argTyp : Typ} {argPoison : Bool} {retSpec : ExternReturn}
    {memberCap : List Capture}
    (hreachable :
      ExternDeclarationReachableFromContext root ctxRoot id
        { id := id, kind := .pfn, typ := argTyp, argName := some x,
          retSpec := some retSpec, effects := [],
          preds := collectExternPreds retSpec [], argPoison := argPoison,
          captures := memberCap })
    {implFn : VarEnv → Value → Memory → Except ExternError Value}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.pfn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw)
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = callEntry.callConfig) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec memberCap ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  have hGetRuntime :
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some (ExternImpl.pfn implFn) := by
    simpa [hregistry] using hGet
  rcases
      TrustedRegistryAgreesWithReachable.resolvePfnDeclaration
        hagrees hreachable hGetRuntime with
    ⟨entry, hlookup, himpl, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec memberCap := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using
      (TrustedRegistry.lookup_toRuntimeRegistry hlookup)
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

/-- Every extern declaration exposed by a qualified type is already in the
    initial reachable trust domain.  This is intentionally a lemma-level
    postcondition for typechecking, not an invariant threaded through the FR
    spine. -/
def QTypReachableFrom (root : Expr) (ctxRoot : TypeContext) (qt : QTyp) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot qt id d →
    ExternDeclarationReachableFromContext root ctxRoot id d

/-- Every extern declaration exposed by a captured type environment is already
    in the initial reachable trust domain. -/
def CapturedEnvReachableFrom
    (root : Expr) (ctxRoot : TypeContext) (σcap : CapturedVarEnv) : Prop :=
  ∀ {id : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d →
    ExternDeclarationReachableFromContext root ctxRoot id d

/-- Context-level monotonicity invariant for reachable extern declarations.
    Every closure-bearing qualified type in the current variable type
    environment is covered by the initial `(root, ctxRoot)` reachable domain. -/
def ContextReachableFrom (root : Expr) (ctxRoot ctx : TypeContext) : Prop :=
  ∀ {x : Name} {qt : QTyp},
    ctx.varEnv.lookup x = some qt →
    QTypReachableFrom root ctxRoot qt

namespace ContextReachableFrom

theorem refl (root : Expr) (ctxRoot : TypeContext) :
    ContextReachableFrom root ctxRoot ctxRoot := by
  intro _x _qt hlookup _id _d hqt
  exact ExternDeclarationReachableFromContext.var hlookup hqt

theorem ctxAfter
    {root : Expr} {ctxRoot ctx : TypeContext} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx) :
    ContextReachableFrom root ctxRoot (ctxAfter ctx res) := by
  intro x qt hlookup
  exact hctx (by simpa [ctxAfter] using hlookup)

theorem lookup
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    {x : Name} {qt : QTyp}
    (hlookup : ctx.varEnv.lookup x = some qt) :
    QTypReachableFrom root ctxRoot qt :=
  hctx hlookup

theorem update
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    {x : Name} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ContextReachableFrom root ctxRoot { ctx with varEnv := VarTypeEnv.update ctx.varEnv x qt } := by
  intro y qt' hlookup
  by_cases hyx : y = x
  · subst y
    have hlookup_self :
        (VarTypeEnv.update ctx.varEnv x qt).lookup x = some qt :=
      VarTypeEnv_lookup_update_eq ctx.varEnv x qt
    have hqt_eq : qt' = qt := by
      rw [hlookup_self] at hlookup
      exact Eq.symm (Option.some.inj hlookup)
    subst qt'
    exact hqt
  · have hlookup_old : ctx.varEnv.lookup y = some qt' := by
      simpa [VarTypeEnv_lookup_update_ne ctx.varEnv x y qt hyx] using hlookup
    exact hctx hlookup_old

end ContextReachableFrom

namespace ExternDeclarationReachableFromCapturedEnv

private lemma list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) :
    l.lookup k = some v → (k, v) ∈ l := by
  intro hlookup
  induction l with
  | nil =>
      simp [List.lookup] at hlookup
  | cons hd tl ih =>
      cases hd with
      | mk k' v' =>
          by_cases hEq : k == k'
          · have hk : k = k' := LawfulBEq.eq_of_beq hEq
            simp [List.lookup, hEq] at hlookup
            subst hk
            subst hlookup
            simp
          · simp [List.lookup, hEq] at hlookup
            exact List.mem_cons_of_mem _ (ih hlookup)

private theorem of_mem
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {x : Name} {qt : QTyp} {id : ExternId} {d : ExternDeclaration}
    (hmem : (x, qt) ∈ σcap)
    (hqt : ExternDeclarationReachableFromQTyp root ctxRoot qt id d) :
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d := by
  induction σcap with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk y qt' =>
          cases hmem with
          | head =>
              exact ExternDeclarationReachableFromCapturedEnv.head hqt
          | tail _ htail =>
              exact ExternDeclarationReachableFromCapturedEnv.tail (ih htail)

private theorem of_list_lookup
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {x : Name} {qt : QTyp} {id : ExternId} {d : ExternDeclaration}
    (hlookup : σcap.lookup x = some qt)
    (hqt : ExternDeclarationReachableFromQTyp root ctxRoot qt id d) :
    ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d :=
  of_mem (list_lookup_mem σcap x qt hlookup) hqt

private theorem exists_mem
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    {id : ExternId} {d : ExternDeclaration}
    (hcap : ExternDeclarationReachableFromCapturedEnv root ctxRoot σcap id d) :
    ∃ x qt,
      (x, qt) ∈ σcap ∧
      ExternDeclarationReachableFromQTyp root ctxRoot qt id d := by
  induction σcap with
  | nil =>
      cases hcap
  | cons hd tl ih =>
      cases hd with
      | mk x qt =>
          cases hcap with
          | head hqt =>
              exact ⟨x, qt, by simp, hqt⟩
          | tail htail =>
              rcases ih htail with ⟨y, qty, hmem, hqt⟩
              exact ⟨y, qty, by simp [hmem], hqt⟩

end ExternDeclarationReachableFromCapturedEnv

namespace CapturedEnvReachableFrom

private theorem of_toCaptured
    {root : Expr} {ctxRoot ctx : TypeContext}
    (hctx : ContextReachableFrom root ctxRoot ctx) :
    CapturedEnvReachableFrom root ctxRoot (VarTypeEnv.toCaptured ctx.varEnv) := by
  intro _id _d hcap
  rcases ExternDeclarationReachableFromCapturedEnv.exists_mem hcap with
    ⟨x, qt, hmem, hqt⟩
  have hlookup := VarTypeEnv_lookup_of_toCaptured_mem ctx.varEnv x qt hmem
  exact hctx hlookup hqt

private theorem qtyp_of_ofCaptured_lookup
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    {x : Name} {qt : QTyp}
    (hlookup : (VarTypeEnv.ofCaptured σcap).lookup x = some qt) :
    QTypReachableFrom root ctxRoot qt := by
  intro _id _d hqt
  have hlist := list_lookup_of_ofCaptured_lookup σcap x qt hlookup
  exact hcap (ExternDeclarationReachableFromCapturedEnv.of_list_lookup hlist hqt)

private theorem context_ofCaptured
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    (ctx : TypeContext) :
    ContextReachableFrom root ctxRoot { ctx with varEnv := VarTypeEnv.ofCaptured σcap } := by
  intro _x _qt hlookup
  exact qtyp_of_ofCaptured_lookup hcap (by simpa using hlookup)

end CapturedEnvReachableFrom

namespace ContextReachableFrom

private theorem ofCaptured_update
    {root : Expr} {ctxRoot : TypeContext} {σcap : CapturedVarEnv}
    (hcap : CapturedEnvReachableFrom root ctxRoot σcap)
    (ctx : TypeContext)
    {x : Name} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ContextReachableFrom root ctxRoot
      { ctx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x qt } := by
  exact ContextReachableFrom.update
    (CapturedEnvReachableFrom.context_ofCaptured hcap ctx) hqt

end ContextReachableFrom

namespace QTypReachableFrom

private theorem arrow_redecorate
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison₁, pred := qpred₁ } := by
  intro _id _d hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_body hmem hprog)
  | arrow_regular_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmem hcap)
  | arrow_extern_member hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_member hmem)
  | arrow_extern_return hmem hret =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_return hmem hret)
  | arrow_extern_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmem hcap)
  | arrow_regular_extern_body hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmem)

private theorem parrow_redecorate
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison₁, pred := qpred₁ } := by
  intro _id _d hreach
  cases hreach with
  | parrow_regular_body hmem hprog =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_body hmem hprog)
  | parrow_regular_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmem hcap)
  | parrow_extern_member hmem =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_member hmem)
  | parrow_extern_return hmem hret =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_return hmem hret)
  | parrow_extern_captured hmem hcap =>
      exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmem hcap)

private theorem etyp_redecorate
    {root : Expr} {ctxRoot : TypeContext} {etyp : ETyp}
    {qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := etyp, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
        { etyp := etyp, poison := qpoison₁, pred := qpred₁ } := by
  cases etyp with
  | int =>
      intro _id _d hreach
      cases hreach
  | bool =>
      intro _id _d hreach
      cases hreach
  | unit =>
      intro _id _d hreach
      cases hreach
  | string =>
      intro _id _d hreach
      cases hreach
  | ref _ls =>
      intro _id _d hreach
      cases hreach
  | arrow st1 st2 p tcls =>
      exact arrow_redecorate hqt
  | parrow st1 st2 p tcls =>
      exact parrow_redecorate hqt

theorem of_eq_redecorate
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {etyp : ETyp} {qpoison₀ qpoison₁ : Poison} {qpred₀ qpred₁ : Predicate}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (heq : qt = { etyp := etyp, poison := qpoison₀, pred := qpred₀ }) :
    QTypReachableFrom root ctxRoot
      { etyp := etyp, poison := qpoison₁, pred := qpred₁ } := by
  subst qt
  exact etyp_redecorate hqt

theorem fn_regular_body
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : Expr} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.regular x body σcap ∈ tcls)
    {id : ExternId} {d : ExternDeclaration}
    (hprog : ExternDeclarationInProgram body id d) :
    ExternDeclarationReachableFromContext root ctxRoot id d :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_regular_body hmem hprog)

private theorem fn_regular_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : Expr} {σcap : CapturedVarEnv}
    (hmem : FnTClosure.regular x body σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmem hcap)

theorem fn_extern_member
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : FnTClosure.extern id x retSpec effects σcap argQt captures ∈ tcls) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .fn, typ := st1, argName := some x,
        retSpec := some retSpec, effects := effects,
        preds := collectExternPreds retSpec effects, argPoison := argQt.poison,
        captures := captures } :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_extern_member hmem)

private theorem fn_extern_return
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId nestedId : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : FnTClosure.extern outerId x retSpec effects σcap argQt captures ∈ tcls)
    {d : ExternDeclaration}
    (hret : ExternDeclarationInReturn retSpec nestedId d) :
    ExternDeclarationReachableFromContext root ctxRoot nestedId d :=
  hqt (ExternDeclarationReachableFromQTyp.arrow_extern_return hmem hret)

private theorem fn_extern_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List FnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : FnTClosure.extern outerId x retSpec effects σcap argQt captures ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmem hcap)


theorem pfn_regular_body
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.regular x body σcap ∈ tcls)
    {id : ExternId} {d : ExternDeclaration}
    (hprog : ExternDeclarationInProgram (PExpr.toExpr body) id d) :
    ExternDeclarationReachableFromContext root ctxRoot id d :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_regular_body hmem hprog)

private theorem pfn_regular_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv}
    (hmem : PFnTClosure.regular x body σcap ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmem hcap)

theorem pfn_extern_member
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {id : ExternId} {x : Name} {retSpec : ExternReturn} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : PFnTClosure.extern id x retSpec σcap argQt captures ∈ tcls) :
    ExternDeclarationReachableFromContext root ctxRoot id
      { id := id, kind := .pfn, typ := st1, argName := some x,
        retSpec := some retSpec, effects := [],
        preds := collectExternPreds retSpec [], argPoison := argQt.poison,
        captures := captures } :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_extern_member hmem)

private theorem pfn_extern_return
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId nestedId : ExternId} {x : Name} {retSpec : ExternReturn}
    {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : PFnTClosure.extern outerId x retSpec σcap argQt captures ∈ tcls)
    {d : ExternDeclaration}
    (hret : ExternDeclarationInReturn retSpec nestedId d) :
    ExternDeclarationReachableFromContext root ctxRoot nestedId d :=
  hqt (ExternDeclarationReachableFromQTyp.parrow_extern_return hmem hret)

private theorem pfn_extern_captured
    {root : Expr} {ctxRoot : TypeContext} {st1 st2 : Typ}
    {p qpoison : Poison} {qpred : Predicate} {tcls : List PFnTClosure}
    (hqt :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls, poison := qpoison, pred := qpred })
    {outerId : ExternId} {x : Name} {retSpec : ExternReturn}
    {σcap : CapturedVarEnv} {argQt : QTyp}
    (hmem : PFnTClosure.extern outerId x retSpec σcap argQt captures ∈ tcls) :
    CapturedEnvReachableFrom root ctxRoot σcap := by
  intro _id _d hcap
  exact hqt (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmem hcap)

private theorem of_fn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.fn x st1 body st2)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.arrow st1 st2 ctx.pc
            [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _id _d hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.fn_body hprog)
      | tail _ htail => cases htail
  | arrow_regular_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | arrow_extern_member hmem =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_return hmem _hret =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_regular_extern_body hmem =>
      cases hmem with
      | head => exact hcurrent ExternDeclarationInProgram.fn_extern_body_runtime
      | tail _ htail => cases htail

private theorem of_pfn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : PExpr}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.pfn x st1 (PExpr.toExpr body) st2)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.parrow st1 st2 ctx.pc
            [PFnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _id _d hreach
  cases hreach with
  | parrow_regular_body hmem hprog =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.pfn_body hprog)
      | tail _ htail => cases htail
  | parrow_regular_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | parrow_extern_member hmem =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_return hmem _hret =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail

private theorem of_externFn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {argPoison : Bool} {argPred : SyntaxPredicate} {argQt : QTyp}
    {retSpec : ExternReturn} {effects : List Effect}
    (hpoison : argQt.poison = argPoison)
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externFn id x argTyp argPoison argPred retSpec effects cap)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.arrow argTyp (parseReturnType retSpec) ctx.pc
            [FnTClosure.extern id x retSpec effects
              (VarTypeEnv.toCaptured ctx.varEnv) argQt cap],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _nestedId _d hreach
  cases hreach with
  | arrow_regular_body hmem _hprog =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_regular_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | arrow_extern_member hmem =>
      cases hmem with
      | head => exact hpoison ▸ hcurrent ExternDeclarationInProgram.externFn
      | tail _ htail => cases htail
  | arrow_extern_return hmem hret =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.externFn_return hret)
      | tail _ htail => cases htail
  | arrow_extern_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail
  | arrow_regular_extern_body hmem =>
      cases hmem with
      | tail _ htail => cases htail

private theorem of_externPfn_result
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {argPoison : Bool} {argPred : SyntaxPredicate} {argQt : QTyp}
    {retSpec : ExternReturn}
    (hpoison : argQt.poison = argPoison)
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externPfn id x argTyp argPoison argPred retSpec cap)) :
    QTypReachableFrom root ctxRoot
      { etyp :=
          ETyp.parrow argTyp (parseReturnType retSpec) ctx.pc
            [PFnTClosure.extern id x retSpec
              (VarTypeEnv.toCaptured ctx.varEnv) argQt cap],
        poison := ctx.pc,
        pred := Predicate.noPred } := by
  intro _nestedId _d hreach
  cases hreach with
  | parrow_regular_body hmem _hprog =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_regular_captured hmem _hcap =>
      cases hmem with
      | tail _ htail => cases htail
  | parrow_extern_member hmem =>
      cases hmem with
      | head => exact hpoison ▸ hcurrent ExternDeclarationInProgram.externPfn
      | tail _ htail => cases htail
  | parrow_extern_return hmem hret =>
      cases hmem with
      | head => exact hcurrent (ExternDeclarationInProgram.externPfn_return hret)
      | tail _ htail => cases htail
  | parrow_extern_captured hmem hcap =>
      cases hmem with
      | head => exact CapturedEnvReachableFrom.of_toCaptured hctx hcap
      | tail _ htail => cases htail

private theorem of_typecheckFn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.fn x st1 body st2))
    (htc : typecheckFn ctx x st1 body st2 = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  have hres := typecheckFn_ok_eq htc
  subst hres
  show QTypReachableFrom root ctxRoot
    { etyp :=
        ETyp.arrow st1 st2 ctx.pc
          [FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)],
      poison := ctx.pc, pred := Predicate.noPred }
  exact of_fn_result hctx hcurrent

private theorem of_typecheckPfn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {st1 st2 : Typ} {body : Expr} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.pfn x st1 body st2))
    (htc : typecheckPfn ctx x st1 body st2 = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  cases hbody : body.toPExpr with
  | error err =>
      simp [typecheckPfn, hbody, bind, Except.bind] at htc
  | ok pbody =>
      simp [typecheckPfn, hbody, bind, Except.bind, pure, Except.pure] at htc
      cases htc
      have hsome : Expr.toPExpr? body = some pbody :=
        Expr_toPExpr?_eq_some_of_toPExpr_ok body pbody hbody
      have hbody_eq : PExpr.toExpr pbody = body :=
        PExpr_toExpr_of_toPExpr?_some body pbody hsome
      rw [← hbody_eq] at hcurrent
      change ∀ {id : ExternId} {d : ExternDeclaration},
        ExternDeclarationReachableFromQTyp root ctxRoot
          { etyp := ETyp.parrow st1 st2 ctx.pc
              [PFnTClosure.regular x pbody (VarTypeEnv.toCaptured ctx.varEnv)],
            poison := ctx.pc, pred := Predicate.noPred } id d →
        ExternDeclarationReachableFromContext root ctxRoot id d
      exact of_pfn_result hctx hcurrent

private theorem of_typecheckExternFn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {argPoison : Bool} {argPred : SyntaxPredicate}
    {retSpec : ExternReturn} {effects : List Effect} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externFn id x argTyp argPoison argPred retSpec effects cap))
    (htc : typecheckExternFn ctx id x argTyp argPoison argPred retSpec effects cap = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  obtain ⟨argQt, hpoison, hres⟩ :=
    typecheckExternFn_ok_res_eq ctx id x argTyp argPoison argPred retSpec effects res htc
  subst res
  change ∀ {nestedId : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot
      { etyp := ETyp.arrow argTyp (parseReturnType retSpec) ctx.pc
          [FnTClosure.extern id x retSpec effects
            (VarTypeEnv.toCaptured ctx.varEnv) argQt cap],
        poison := ctx.pc, pred := Predicate.noPred } nestedId d →
    ExternDeclarationReachableFromContext root ctxRoot nestedId d
  exact of_externFn_result hpoison hctx hcurrent

private theorem of_typecheckExternPfn
    {root : Expr} {ctxRoot ctx : TypeContext}
    {id : ExternId} {x : Name} {argTyp : Typ}
    {argPoison : Bool} {argPred : SyntaxPredicate}
    {retSpec : ExternReturn} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot
        (Expr.externPfn id x argTyp argPoison argPred retSpec cap))
    (htc : typecheckExternPfn ctx id x argTyp argPoison argPred retSpec cap = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  obtain ⟨argQt, hpoison, hres⟩ :=
    typecheckExternPfn_ok_res_eq ctx id x argTyp argPoison argPred retSpec res htc
  subst res
  change ∀ {nestedId : ExternId} {d : ExternDeclaration},
    ExternDeclarationReachableFromQTyp root ctxRoot
      { etyp := ETyp.parrow argTyp (parseReturnType retSpec) ctx.pc
          [PFnTClosure.extern id x retSpec
            (VarTypeEnv.toCaptured ctx.varEnv) argQt cap],
        poison := ctx.pc, pred := Predicate.noPred } nestedId d →
    ExternDeclarationReachableFromContext root ctxRoot nestedId d
  exact of_externPfn_result hpoison hctx hcurrent

private theorem of_non_function_etyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    (hfun : qt.etyp.isFunctionType = false) :
    QTypReachableFrom root ctxRoot qt := by
  intro _id _d hreach
  cases qt with
  | mk etyp poison pred =>
      cases etyp <;> simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow] at hfun
      all_goals cases hreach

private def ETypReachableFrom (root : Expr) (ctxRoot : TypeContext) (etyp : ETyp) : Prop :=
  ∀ {qpoison : Poison} {qpred : Predicate},
    QTypReachableFrom root ctxRoot { etyp := etyp, poison := qpoison, pred := qpred }

private theorem ETypReachableFrom.of_qtyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    ETypReachableFrom root ctxRoot qt.etyp := by
  cases qt with
  | mk etyp qpoison qpred =>
      intro _qpoison' _qpred'
      exact QTypReachableFrom.etyp_redecorate hqt

private theorem fnArrowSource
    {st1a st2a st1 st2 : Typ} {pa : Poison}
    {tcls1 : List FnTClosure} {tcl : FnTClosure}
    (hst1 : st1a = st1) (hst2 : st2a = st2)
    (hmem : tcl ∈ tcls1) :
    ∃ psrc tclsSrc,
      ETyp.arrow st1a st2a pa tcls1 = ETyp.arrow st1 st2 psrc tclsSrc ∧
      tcl ∈ tclsSrc := by
  refine ⟨pa, tcls1, ?_, hmem⟩
  rw [hst1, hst2]

private theorem pfnArrowSource
    {st1a st2a st1 st2 : Typ} {pa : Poison}
    {tcls1 : List PFnTClosure} {tcl : PFnTClosure}
    (hst1 : st1a = st1) (hst2 : st2a = st2)
    (hmem : tcl ∈ tcls1) :
    ∃ psrc tclsSrc,
      ETyp.parrow st1a st2a pa tcls1 = ETyp.parrow st1 st2 psrc tclsSrc ∧
      tcl ∈ tclsSrc := by
  refine ⟨pa, tcls1, ?_, hmem⟩
  rw [hst1, hst2]

private theorem typPair_eq_of_and_beq
    {st1a st1b st2a st2b : Typ}
    (hshape : (st1a == st1b && st2a == st2b) = true) :
    st1a = st1b ∧ st2a = st2b := by
  rw [Bool.and_eq_true] at hshape
  rcases hshape with ⟨h1, h2⟩
  exact ⟨LawfulBEq.eq_of_beq h1, LawfulBEq.eq_of_beq h2⟩

private theorem joinETyps_arrow_member_source
    {etyp1 etyp2 : ETyp} {p1 p2 : Poison}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure} {tcl : FnTClosure}
    (heq : joinETyps etyp1 etyp2 p1 p2 = ETyp.arrow st1 st2 p tcls)
    (hmem : tcl ∈ tcls) :
    (∃ psrc tclsSrc,
      etyp1 = ETyp.arrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) ∨
    (∃ psrc tclsSrc,
      etyp2 = ETyp.arrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) := by
  cases etyp1 with
  | int => cases etyp2 <;> simp [joinETyps] at heq
  | bool => cases etyp2 <;> simp [joinETyps] at heq
  | unit => cases etyp2 <;> simp [joinETyps] at heq
  | string => cases etyp2 <;> simp [joinETyps] at heq
  | ref ls1 => cases etyp2 <;> simp [joinETyps] at heq
  | parrow st1p st2p pp tclsp =>
      cases etyp2 with
      | parrow st1b st2b pb tcls2 =>
          by_cases hshape : st1p == st1b && st2p == st2b
          · simp [joinETyps, hshape] at heq
          · simp [joinETyps, hshape] at heq
      | int => simp [joinETyps] at heq
      | bool => simp [joinETyps] at heq
      | unit => simp [joinETyps] at heq
      | string => simp [joinETyps] at heq
      | ref ls => simp [joinETyps] at heq
      | arrow st1f st2f pf tclsf => simp [joinETyps] at heq
  | arrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | arrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : mergeFnTClosures tcls1 tcls2 = tcls := heq.2.2.2
            have hmemMerge : tcl ∈ mergeFnTClosures tcls1 tcls2 := by
              simpa [htcls] using hmem
            rcases mem_mergeFnTClosures_inv tcls1 tcls2 tcl hmemMerge with hleft | hright
            · exact Or.inl (fnArrowSource hst1 hst2 hleft)
            · rcases typPair_eq_of_and_beq hshape with ⟨hst1ab, hst2ab⟩
              have hst1b : st1b = st1 := by rw [← hst1ab, hst1]
              have hst2b : st2b = st2 := by rw [← hst2ab, hst2]
              exact Or.inr (fnArrowSource hst1b hst2b hright)
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : tcls1 = tcls := heq.2.2.2
            have hmem1 : tcl ∈ tcls1 := by simpa [htcls] using hmem
            exact Or.inl (fnArrowSource hst1 hst2 hmem1)
      | int =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | bool =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | unit =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | string =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | ref ls =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)
      | parrow st1p st2p pp tclsp =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (fnArrowSource heq.1 heq.2.1 hmem1)

private theorem joinETyps_parrow_member_source
    {etyp1 etyp2 : ETyp} {p1 p2 : Poison}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure} {tcl : PFnTClosure}
    (heq : joinETyps etyp1 etyp2 p1 p2 = ETyp.parrow st1 st2 p tcls)
    (hmem : tcl ∈ tcls) :
    (∃ psrc tclsSrc,
      etyp1 = ETyp.parrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) ∨
    (∃ psrc tclsSrc,
      etyp2 = ETyp.parrow st1 st2 psrc tclsSrc ∧ tcl ∈ tclsSrc) := by
  cases etyp1 with
  | int => cases etyp2 <;> simp [joinETyps] at heq
  | bool => cases etyp2 <;> simp [joinETyps] at heq
  | unit => cases etyp2 <;> simp [joinETyps] at heq
  | string => cases etyp2 <;> simp [joinETyps] at heq
  | ref ls1 => cases etyp2 <;> simp [joinETyps] at heq
  | arrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | arrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
          · simp [joinETyps, hshape] at heq
      | int => simp [joinETyps] at heq
      | bool => simp [joinETyps] at heq
      | unit => simp [joinETyps] at heq
      | string => simp [joinETyps] at heq
      | ref ls => simp [joinETyps] at heq
      | parrow st1p st2p pp tclsp => simp [joinETyps] at heq
  | parrow st1a st2a pa tcls1 =>
      cases etyp2 with
      | parrow st1b st2b pb tcls2 =>
          by_cases hshape : st1a == st1b && st2a == st2b
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : mergePFnTClosures tcls1 tcls2 = tcls := heq.2.2.2
            have hmemMerge : tcl ∈ mergePFnTClosures tcls1 tcls2 := by
              simpa [htcls] using hmem
            rcases mem_mergePFnTClosures_inv tcls1 tcls2 tcl hmemMerge with hleft | hright
            · exact Or.inl (pfnArrowSource hst1 hst2 hleft)
            · rcases typPair_eq_of_and_beq hshape with ⟨hst1ab, hst2ab⟩
              have hst1b : st1b = st1 := by rw [← hst1ab, hst1]
              have hst2b : st2b = st2 := by rw [← hst2ab, hst2]
              exact Or.inr (pfnArrowSource hst1b hst2b hright)
          · simp [joinETyps, hshape] at heq
            have hst1 : st1a = st1 := heq.1
            have hst2 : st2a = st2 := heq.2.1
            have htcls : tcls1 = tcls := heq.2.2.2
            have hmem1 : tcl ∈ tcls1 := by simpa [htcls] using hmem
            exact Or.inl (pfnArrowSource hst1 hst2 hmem1)
      | int =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | bool =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | unit =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | string =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | ref ls =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)
      | arrow st1f st2f pf tclsf =>
          simp [joinETyps] at heq
          have hmem1 : tcl ∈ tcls1 := by simpa [heq.2.2.2] using hmem
          exact Or.inl (pfnArrowSource heq.1 heq.2.1 hmem1)

private theorem ETypReachableFrom.of_joinETyps
    {root : Expr} {ctxRoot : TypeContext} {etyp1 etyp2 : ETyp}
    {p1 p2 : Poison}
    (h1 : ETypReachableFrom root ctxRoot etyp1)
    (h2 : ETypReachableFrom root ctxRoot etyp2) :
    ETypReachableFrom root ctxRoot (_root_.joinETyps etyp1 etyp2 p1 p2) := by
  intro qpoison qpred id d hreach
  generalize hetyp : _root_.joinETyps etyp1 etyp2 p1 p2 = etyp at hreach
  cases hreach with
  | arrow_regular_body hmem hprog =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_body hmemSrc hprog)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_body hmemSrc hprog)
  | arrow_regular_captured hmem hcap =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_captured hmemSrc hcap)
  | arrow_extern_member hmem =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_member hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_member hmemSrc)
  | arrow_extern_return hmem hret =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_return hmemSrc hret)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_return hmemSrc hret)
  | arrow_extern_captured hmem hcap =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_extern_captured hmemSrc hcap)
  | arrow_regular_extern_body hmem =>
      rcases
          joinETyps_arrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.arrow_regular_extern_body hmemSrc)
  | parrow_regular_body hmem hprog =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_body hmemSrc hprog)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_body hmemSrc hprog)
  | parrow_regular_captured hmem hcap =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_regular_captured hmemSrc hcap)
  | parrow_extern_member hmem =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_member hmemSrc)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_member hmemSrc)
  | parrow_extern_return hmem hret =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_return hmemSrc hret)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_return hmemSrc hret)
  | parrow_extern_captured hmem hcap =>
      rcases
          joinETyps_parrow_member_source hetyp hmem with hsrc | hsrc
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp1
        exact h1 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmemSrc hcap)
      · rcases hsrc with ⟨psrc, tclsSrc, heq, hmemSrc⟩
        subst etyp2
        exact h2 (qpoison := qpoison) (qpred := qpred)
          (ExternDeclarationReachableFromQTyp.parrow_extern_captured hmemSrc hcap)

private theorem of_joinETyps
    {root : Expr} {ctxRoot : TypeContext} {qt1 qt2 : QTyp}
    (h1 : QTypReachableFrom root ctxRoot qt1)
    (h2 : QTypReachableFrom root ctxRoot qt2) :
    QTypReachableFrom root ctxRoot
      { etyp := _root_.joinETyps qt1.etyp qt2.etyp qt1.poison qt2.poison,
        poison := joinPoison qt1.poison qt2.poison,
        pred := joinPredicates qt1.pred qt2.pred } := by
  exact ETypReachableFrom.of_joinETyps
    (ETypReachableFrom.of_qtyp h1) (ETypReachableFrom.of_qtyp h2)

private theorem of_joinTypeResults
    {root : Expr} {ctxRoot : TypeContext} {ctx : TypeContext}
    {first res : TypeResult} {rest : List TypeResult}
    (hfirst : QTypReachableFrom root ctxRoot first.qualType)
    (hrest : ∀ result ∈ rest,
      QTypReachableFrom root ctxRoot result.qualType)
    (hjoin : joinTypeResults ctx first rest = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  let joinStep :
      (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) →
        TypeResult →
        Except String
          (ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag) :=
    fun acc result =>
      match result.qualType with
      | ⟨resEtyp, resPoison, resPred⟩ =>
          Except.ok
            (_root_.joinETyps acc.1 resEtyp acc.2.2.1 resPoison,
              joinMemEnvsStrong acc.2.1 result.memEnv',
              joinPoison acc.2.2.1 resPoison,
              joinPredicates acc.2.2.2.1 resPred,
              joinTagEnvs acc.2.2.2.2.1 result.tagEnv',
              joinRegimes acc.2.2.2.2.2.1 result.regime',
              max acc.2.2.2.2.2.2.1 result.nextLoc',
              max acc.2.2.2.2.2.2.2 result.nextTag')
  have hfoldReach :
      ∀ (rs : List TypeResult)
        (acc acc' :
          ETyp × MemoryTypeEnv × Poison × Predicate × TagEnv × Regime × Loc × Tag),
        List.foldlM joinStep acc rs = .ok acc' →
        ETypReachableFrom root ctxRoot acc.1 →
        (∀ result ∈ rs, QTypReachableFrom root ctxRoot result.qualType) →
        ETypReachableFrom root ctxRoot acc'.1 := by
    intro rs
    induction rs with
    | nil =>
        intro acc acc' hfold hacc _hrest
        simp [List.foldlM_nil, pure, Except.pure] at hfold
        cases hfold
        intro qpoison qpred id d hreach
        exact hacc (qpoison := qpoison) (qpred := qpred) hreach
    | cons result rs ih =>
        intro acc acc' hfold hacc hrest'
        cases hqt : result.qualType with
        | mk resEtyp resPoison resPred =>
            simp [List.foldlM_cons, joinStep, hqt, bind, Except.bind] at hfold
            have hresReachRaw : QTypReachableFrom root ctxRoot result.qualType :=
              hrest' result (by simp)
            have hresReach :
                QTypReachableFrom root ctxRoot
                  { etyp := resEtyp, poison := resPoison, pred := resPred } := by
              intro id d hreach
              exact hresReachRaw (by simpa [hqt] using hreach)
            have hresEtypReach : ETypReachableFrom root ctxRoot resEtyp := by
              intro qpoison qpred id d hreach
              exact (QTypReachableFrom.etyp_redecorate hresReach) hreach
            have hstepReach :
                ETypReachableFrom root ctxRoot
                  (_root_.joinETyps acc.1 resEtyp acc.2.2.1 resPoison) :=
              ETypReachableFrom.of_joinETyps hacc hresEtypReach
            have htail :
                ∀ tailResult ∈ rs,
                  QTypReachableFrom root ctxRoot tailResult.qualType := by
              intro tailResult hmem
              exact hrest' tailResult (by simp [hmem])
            intro qpoison qpred id d hreach
            exact (ih _ _ hfold hstepReach htail) hreach
  cases hqtFirst : first.qualType with
  | mk etyp poison pred =>
      simp [joinTypeResults, hqtFirst, bind, Except.bind, pure, Except.pure] at hjoin
      cases hcheck :
          (List.foldlM
            (fun x result =>
              match result.qualType with
              | { etyp := resEtyp, poison := _resP, pred := _resPred } =>
                if beqETypSignature etyp resEtyp = false then
                  Except.error
                    (toString "Closure alternatives produced incompatible result types: " ++
                      toString (repr etyp) ++ toString " vs " ++
                      toString (repr resEtyp))
                else Except.ok ())
            () rest : Except String Unit) with
      | error err =>
          erw [hcheck] at hjoin
          simp at hjoin
      | ok _ =>
          erw [hcheck] at hjoin
          simp at hjoin
          cases hfold :
              List.foldlM joinStep
                (etyp, first.memEnv', poison, pred, first.tagEnv',
                  first.regime', first.nextLoc', first.nextTag') rest with
          | error err =>
              erw [hfold] at hjoin
              simp at hjoin
          | ok acc =>
              erw [hfold] at hjoin
              simp at hjoin
              cases hjoin
              have hfirstE : ETypReachableFrom root ctxRoot etyp := by
                have hfirst' :
                    QTypReachableFrom root ctxRoot
                      { etyp := etyp, poison := poison, pred := pred } := by
                  intro id d hreach
                  exact hfirst (by simpa [hqtFirst] using hreach)
                intro qpoison qpred id d hreach
                exact (QTypReachableFrom.etyp_redecorate hfirst') hreach
              have haccReach : ETypReachableFrom root ctxRoot acc.1 :=
                hfoldReach rest
                (etyp, first.memEnv', poison, pred, first.tagEnv',
                  first.regime', first.nextLoc', first.nextTag')
                acc hfold
                hfirstE
                hrest
              intro id d hreach
              exact haccReach hreach

private theorem with_etyp
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {qpoison : Poison} {qpred : Predicate}
    (hqt : QTypReachableFrom root ctxRoot qt) :
    QTypReachableFrom root ctxRoot
      { etyp := qt.etyp, poison := qpoison, pred := qpred } :=
  ETypReachableFrom.of_qtyp hqt

private theorem of_arrow_etyp_eq
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls) :
    QTypReachableFrom root ctxRoot
      { etyp := ETyp.arrow st1 st2 p tcls,
        poison := qt.poison, pred := qt.pred } := by
  cases hres : qt with
  | mk etyp qpoison qpred =>
      have harrow : etyp = ETyp.arrow st1 st2 p tcls := by
        simpa [hres] using hetyp
      subst etyp
      intro id d hreach
      exact hqt (by simpa [hres] using hreach)

private theorem of_parrow_etyp_eq
    {root : Expr} {ctxRoot : TypeContext} {qt : QTyp}
    {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    (hqt : QTypReachableFrom root ctxRoot qt)
    (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls) :
    QTypReachableFrom root ctxRoot
      { etyp := ETyp.parrow st1 st2 p tcls,
        poison := qt.poison, pred := qt.pred } := by
  cases hres : qt with
  | mk etyp qpoison qpred =>
      have hparrow : etyp = ETyp.parrow st1 st2 p tcls := by
        simpa [hres] using hetyp
      subst etyp
      intro id d hreach
      exact hqt (by simpa [hres] using hreach)

private theorem of_typecheckVar
    {root : Expr} {ctxRoot ctx : TypeContext}
    {x : Name} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (htc : typecheckVar ctx x = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  unfold typecheckVar at htc
  cases hlookup : ctx.varEnv.lookup x with
  | none =>
      simp [hlookup] at htc
  | some qt =>
      have hqt : QTypReachableFrom root ctxRoot qt :=
        ContextReachableFrom.lookup hctx hlookup
      cases qt with
      | mk etyp poison pred =>
          have hred (qpoison : Poison) (qpred : Predicate) :
              QTypReachableFrom root ctxRoot
                { etyp := etyp, poison := qpoison, pred := qpred } := by
            unfold QTypReachableFrom
            intro id d hreach
            exact (QTypReachableFrom.etyp_redecorate hqt) hreach
          cases pred with
          | noPred =>
              simp [hlookup, pure, Except.pure] at htc
              cases htc
              change QTypReachableFrom root ctxRoot
                { etyp := etyp, poison := joinPoison ctx.pc poison, pred := Predicate.noPred }
              exact hred (joinPoison ctx.pc poison) Predicate.noPred
          | guardOnly k =>
              show QTypReachableFrom root ctxRoot res.qualType
              by_cases hfun : etyp.isFunctionType = true
              · simp [hlookup, hfun] at htc
                cases htc
              · have hfunFalse : etyp.isFunctionType = false := by
                  cases hif : etyp.isFunctionType <;> simp [hif] at hfun ⊢
                cases htag : ctx.tagEnv[k]? with
                | none =>
                    simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                    cases htc
                    intro hreach
                    exact (hred (joinPoison ctx.pc poison) (Predicate.guardOnly k)) hreach
                | some tv =>
                    cases tv with
                    | mk b deps =>
                        cases b
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred true Predicate.noPred) hreach
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred ctx.pc Predicate.noPred) hreach
          | guardClosure k arg body env =>
              show QTypReachableFrom root ctxRoot res.qualType
              by_cases hfun : etyp.isFunctionType = true
              · simp [hlookup, hfun] at htc
                cases htc
              · have hfunFalse : etyp.isFunctionType = false := by
                  cases hif : etyp.isFunctionType <;> simp [hif] at hfun ⊢
                cases htag : ctx.tagEnv[k]? with
                | none =>
                    simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                    cases htc
                    intro hreach
                    exact
                      (hred (joinPoison ctx.pc poison)
                        (Predicate.guardClosure k arg body env)) hreach
                | some tv =>
                    cases tv with
                    | mk b deps =>
                        cases b
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred true Predicate.noPred) hreach
                        · simp [hlookup, hfunFalse, htag, pure, Except.pure] at htc
                          cases htc
                          intro hreach
                          exact (hred ctx.pc Predicate.noPred) hreach

end QTypReachableFrom

namespace ContextReachableFrom

theorem fnBody_of_arrow_member
    {root : Expr} {ctxRoot bodyCtx : TypeContext}
    {result1 : TypeResult} {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
    {x : Name} {body : Expr} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hqtFn : QTypReachableFrom root ctxRoot result1.qualType)
    (hetyp : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
    (hmem : FnTClosure.regular x body σcap ∈ tcls)
    (harg : QTypReachableFrom root ctxRoot argQt)
    (hvar :
      bodyCtx.varEnv = VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt) :
    ContextReachableFrom root ctxRoot bodyCtx := by
  have hqtArrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } := by
    cases hres : result1.qualType with
    | mk etyp qpoison qpred =>
        have harrow : etyp = ETyp.arrow st1 st2 p tcls := by
          simpa [hres] using hetyp
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              result1.qualType id d := by
          simpa [hres] using hreach
        exact hqtFn hreach'
  have hcap : CapturedEnvReachableFrom root ctxRoot σcap :=
    QTypReachableFrom.fn_regular_captured hqtArrow hmem
  have hctx :
      ContextReachableFrom root ctxRoot
        { bodyCtx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } :=
    ContextReachableFrom.ofCaptured_update hcap bodyCtx harg
  intro y qt hlookup
  exact hctx (by simpa [hvar] using hlookup)

theorem pfnBody_of_parrow_member
    {root : Expr} {ctxRoot bodyCtx : TypeContext}
    {result1 : TypeResult} {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
    {x : Name} {body : PExpr} {σcap : CapturedVarEnv} {argQt : QTyp}
    (hqtPfn : QTypReachableFrom root ctxRoot result1.qualType)
    (hetyp : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
    (hmem : PFnTClosure.regular x body σcap ∈ tcls)
    (harg : QTypReachableFrom root ctxRoot argQt)
    (hvar :
      bodyCtx.varEnv = VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt) :
    ContextReachableFrom root ctxRoot bodyCtx := by
  have hqtParrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } := by
    cases hres : result1.qualType with
    | mk etyp qpoison qpred =>
        have hparrow : etyp = ETyp.parrow st1 st2 p tcls := by
          simpa [hres] using hetyp
        subst etyp
        intro id d hreach
        have hreach' :
            ExternDeclarationReachableFromQTyp root ctxRoot
              result1.qualType id d := by
          simpa [hres] using hreach
        exact hqtPfn hreach'
  have hcap : CapturedEnvReachableFrom root ctxRoot σcap :=
    QTypReachableFrom.pfn_regular_captured hqtParrow hmem
  have hctx :
      ContextReachableFrom root ctxRoot
        { bodyCtx with varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x argQt } :=
    ContextReachableFrom.ofCaptured_update hcap bodyCtx harg
  intro y qt hlookup
  exact hctx (by simpa [hvar] using hlookup)

end ContextReachableFrom

namespace QTypReachableFrom

private theorem applyClosuresThreaded_forall_reachable_mem
    {α : Type} {root : Expr} {ctxRoot : TypeContext}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (items : List α) (cursor : Tag × Loc) (results : List TypeResult)
    (hOne :
      ∀ item, item ∈ items → ∀ cursor result,
        applyOne item cursor = .ok result →
        QTypReachableFrom root ctxRoot result.qualType)
    (hthread : applyClosuresThreaded applyOne items cursor = .ok results) :
    ∀ result ∈ results, QTypReachableFrom root ctxRoot result.qualType := by
  induction items generalizing cursor results with
  | nil =>
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      cases hthread
      intro result hmem
      cases hmem
  | cons item rest ih =>
      simp [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _err =>
          simp [hfirst] at hthread
      | ok first =>
          simp [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest
              (first.nextTag', first.nextLoc') with
          | error _err =>
              simp [hrest] at hthread
          | ok restResults =>
              simp [hrest, pure, Except.pure] at hthread
              cases hthread
              intro result hmem
              simp at hmem
              cases hmem with
              | inl hfirstEq =>
                  subst result
                  exact hOne item (by simp) cursor first hfirst
              | inr htail =>
                  exact
                    ih (first.nextTag', first.nextLoc') restResults
                      (fun tailItem htailMem cursor result happly =>
                        hOne tailItem (List.mem_cons_of_mem item htailMem)
                          cursor result happly)
                      hrest result htail

/-- Mirrors the post-effects "finish" tail of the `FnTClosure.extern` branch of
    `applyFnTClosureAtCursor`: the per-return-shape construction of the result
    `TypeResult` once the effects loop has produced the updated memory.

    IMPORTANT: this must stay definitionally in lockstep with that tail in
    `LeanPoison/Typecheck.lean` — `of_applyFnTClosureAtCursor` discharges the
    `convert` with `rfl`, so any change there must be mirrored here.  In
    particular every return branch (simple and both nested returns) applies
    `applyExternRegimePolicy` to `regime'`, and
    the simple return additionally materialises the regime-determined return
    guard into `tagEnv'` via `installReturnGuard` (`fuel` is the decremented
    fuel of the surrounding apply). -/
private def fnExternFinishAtCursor
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc)
    (p p1 : Poison) (unifiedEnv : VarTypeEnv)
    (tagMapping : ExtTreeMap TagIndex Tag compare) (nextTag' : Tag)
    (id : ExternId) (effects : List Effect)
    (retSpec : ExternReturn) (fuel : Nat) (memEnv : MemoryTypeEnv) : TypecheckM TypeResult :=
  match retSpec with
  | ExternReturn.simple typ poison pred =>
      match resolveSyntaxPred pred unifiedEnv tagMapping with
      | Except.error err => Except.error err
      | Except.ok v_1 =>
          match returnSpecToQTyp typ poison v_1 cursor.2 with
          | Except.error err => Except.error err
          | Except.ok v_2 =>
              Except.ok
                { qualType :=
                    normalizeAppResultByProvenance (joinPoison p1 p)
                      { etyp := v_2.1.etyp,
                        poison :=
                          joinPoison p1 (joinPoison p (joinPoison ctx.pc v_2.1.poison)),
                        pred := v_2.1.pred },
                  memEnv' := memEnv,
                  tagEnv' := installReturnGuard
                    (invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                    v_1
                    (applyExternRegimePolicy
                      (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                      id ctx.externRegime tagMapping)
                    fuel,
                  nextLoc' := v_2.2,
                  nextTag' := nextTag',
                  regime' := applyExternRegimePolicy
                    (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                    id ctx.externRegime tagMapping,
                  declared' := result2.declared' }
  | ExternReturn.nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
      match resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv nextTag' with
      | Except.error err => Except.error err
      | Except.ok (innerArgQt, nextTag'') =>
          Except.ok
            { qualType :=
                normalizeAppResultByProvenance (joinPoison p1 p)
                  { etyp :=
                      ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                        [FnTClosure.extern innerId innerArg innerRet innerEffects
                          (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures],
                    poison := joinPoison p1 (joinPoison p ctx.pc),
                    pred := Predicate.noPred },
              memEnv' := memEnv,
              tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
              nextLoc' := cursor.2,
              nextTag' := nextTag'',
              regime' := applyExternRegimePolicy
                (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                id ctx.externRegime tagMapping,
              declared' := result2.declared' }
  | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
      match resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv nextTag' with
      | Except.error err => Except.error err
      | Except.ok (innerArgQt, nextTag'') =>
          Except.ok
            { qualType :=
                normalizeAppResultByProvenance (joinPoison p1 p)
                  { etyp :=
                      ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                        [PFnTClosure.extern innerId innerArg innerRet
                          (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures],
                    poison := joinPoison p1 (joinPoison p ctx.pc),
                    pred := Predicate.noPred },
              memEnv' := memEnv,
              tagEnv' := invalidateTagDeps result2.tagEnv' (effectTargetLocs effects unifiedEnv),
              nextLoc' := cursor.2,
              nextTag' := nextTag'',
              regime' := applyExternRegimePolicy
                (invalidateRegimeDepsEffect result2.regime' result2.tagEnv' (effectTargetLocs effects unifiedEnv))
                id ctx.externRegime tagMapping,
              declared' := result2.declared' }

private theorem of_applyFnTClosureAtCursor
    {root : Expr} {ctxRoot ctx : TypeContext}
    {tcl : FnTClosure} {st1 st2 : Typ} {p p1 : Poison}
    {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {result1 result : TypeResult} {cursor : Tag × Loc}
    {fuel : Nat} {tcls : List FnTClosure}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (_hctx : ContextReachableFrom root ctxRoot ctx)
    (hqtFn : QTypReachableFrom root ctxRoot result1.qualType)
    (hfnEtyp : result1.qualType.etyp = ETyp.arrow st1 st2 p tcls)
    (harg :
      QTypReachableFrom root ctxRoot
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
          pred := argPred })
    (hmem : tcl ∈ tcls)
    (happly :
      applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx result1 cursor fuel = .ok result) :
    QTypReachableFrom root ctxRoot result.qualType := by
  have hqtArrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.arrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } :=
    QTypReachableFrom.of_arrow_etyp_eq hqtFn hfnEtyp
  unfold applyFnTClosureAtCursor at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body σcap =>
          simp [bind, Except.bind] at happly
          cases htcBody :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison p1 ctx.pc),
                  memEnv := result1.memEnv',
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred },
                  tagEnv := result1.tagEnv',
                  nextTag := cursor.1,
                  nextLoc := cursor.2,
                  regime := result1.regime',
                  externRefAllowed := false,
                  declaredExternRefs := result1.declared' } body fuel' with
          | error _err =>
              rw [htcBody] at happly
              simp at happly
          | ok bodyResult =>
              rw [htcBody] at happly
              simp at happly
              cases hbodyQt : bodyResult.qualType with
              | mk bodyEtyp bodyPoison bodyPred =>
                  simp [hbodyQt] at happly
                  cases hsub :
                      isErasureOf st2
                        { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred }
                  · simp [hsub] at happly
                  · simp [hsub, pure, Except.pure] at happly
                    cases happly
                    have hbodyCtx :
                        ContextReachableFrom root ctxRoot
                          { ctx with
                            pc := joinPoison p (joinPoison p1 ctx.pc),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                              { etyp := argEtyp,
                                poison := joinPoison ctx.pc argPoison,
                                pred := argPred },
                            tagEnv := result1.tagEnv',
                            nextTag := cursor.1,
                            nextLoc := cursor.2,
                            regime := result1.regime',
                            externRefAllowed := false,
                            declaredExternRefs := result1.declared' } :=
                      ContextReachableFrom.fnBody_of_arrow_member
                        hqtFn hfnEtyp hmem harg rfl
                    have hbodyReach :
                        ExternDeclarationReachableFromExpr root ctxRoot body := by
                      intro id d hprog
                      exact QTypReachableFrom.fn_regular_body hqtArrow hmem hprog
                    have hbodyResultReach :
                        QTypReachableFrom root ctxRoot bodyResult.qualType :=
                      IH fuel' (Nat.lt_succ_self fuel') hbodyCtx hbodyReach htcBody
                    have hbodyBaseReach :
                        QTypReachableFrom root ctxRoot
                          { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred } := by
                      intro id d hreach
                      exact hbodyResultReach (by simpa [hbodyQt] using hreach)
                    intro id d hreach
                    cases hgate : joinPoison p1 p
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := joinPoison p1 (joinPoison p bodyPoison))
                          (qpred := bodyPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := true) (qpred := Predicate.noPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
      | extern id x retSpec effects capturedEnv declaredArgQt =>
          have hcap : CapturedEnvReachableFrom root ctxRoot capturedEnv :=
            QTypReachableFrom.fn_extern_captured hqtArrow hmem
          have hargQt :
              QTypReachableFrom root ctxRoot
                { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
                  pred := argPred } := harg
          have hunifiedCtx :
              ContextReachableFrom root ctxRoot
                { ctx with
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred } } :=
            ContextReachableFrom.ofCaptured_update hcap ctx hargQt
          let unifiedEnv : VarTypeEnv :=
            VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              { etyp := argEtyp,
                poison := joinPoison ctx.pc argPoison,
                pred := argPred }
          simp [bind, Except.bind] at happly
          -- Leading argument-condition gate: throw branch is impossible on .ok.
          split at happly
          · simp at happly
          simp only [pure, Except.pure] at happly
          cases htag :
              collectAndAllocExternTags (collectExternPreds retSpec effects) cursor.1 with
          | error _err =>
              simp [htag] at happly
          | ok tagResult =>
              cases tagResult with
              | mk tagMapping nextTag' =>
                  simp [htag] at happly
                  let effectRun : TypecheckM MemoryTypeEnv :=
                    forIn effects result1.memEnv' fun effect r =>
                      match applyExternEffect effect unifiedEnv tagMapping
                          (joinPoison p (joinPoison p1 ctx.pc)) r with
                      | Except.error err => Except.error err
                      | Except.ok v => Except.ok (ForInStep.yield v)
                  let finish : MemoryTypeEnv → TypecheckM TypeResult :=
                    fnExternFinishAtCursor ctx result1 cursor p p1 unifiedEnv tagMapping
                      nextTag' id effects retSpec fuel'
                  have hwholeOk :
                      (match effectRun with
                      | Except.error err => Except.error err
                      | Except.ok v => finish v) = Except.ok result := by
                    convert happly
                    · funext _motive scrut _err _ok
                      cases scrut <;> rfl
                    · funext _motive scrut _err _ok
                      cases scrut <;> rfl
                    · rename_i memEnvArg
                      cases retSpec <;> simp [finish, fnExternFinishAtCursor, unifiedEnv]
                      · rename_i typ poison pred
                        cases resolveSyntaxPred pred unifiedEnv tagMapping <;> simp
                        · rename_i resolvedPred
                          cases returnSpecToQTyp typ poison resolvedPred cursor.2 <;> rfl
                      · rename_i innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures
                        cases resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv nextTag' <;> rfl
                      · rename_i innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures
                        cases resolveArgCondQTyp innerArgTyp innerArgPoison innerArgPred unifiedEnv nextTag' <;> rfl
                  cases hfor : effectRun with
                  | error _err =>
                      have hbad : (Except.error _err : TypecheckM TypeResult) =
                          Except.ok result := by
                        have hcongr := congrArg
                          (fun z : TypecheckM MemoryTypeEnv =>
                            match z with
                            | Except.error err => (Except.error err : TypecheckM TypeResult)
                            | Except.ok memEnv => finish memEnv) hfor
                        simpa [finish] using Eq.trans (Eq.symm hcongr) hwholeOk
                      cases hbad
                  | ok memEnv =>
                      have hfinishOk : finish memEnv = Except.ok result := by
                        have hcongr := congrArg
                          (fun z : TypecheckM MemoryTypeEnv =>
                            match z with
                            | Except.error err => (Except.error err : TypecheckM TypeResult)
                            | Except.ok memEnv => finish memEnv) hfor
                        simpa [finish] using Eq.trans (Eq.symm hcongr) hwholeOk
                      cases retSpec with
                      | simple typ poison pred =>
                          simp [finish, fnExternFinishAtCursor] at hfinishOk
                          cases hresPred :
                              resolveSyntaxPred pred unifiedEnv tagMapping with
                          | error _err =>
                              simp [hresPred] at hfinishOk
                          | ok resolvedPred =>
                              simp [hresPred] at hfinishOk
                              cases hret :
                                  returnSpecToQTyp typ poison resolvedPred cursor.2 with
                              | error _err =>
                                  simp [hret] at hfinishOk
                              | ok retPair =>
                                  cases retPair with
                                  | mk retQt nextLoc' =>
                                      simp [hret] at hfinishOk
                                      cases hfinishOk
                                      apply QTypReachableFrom.of_non_function_etyp
                                      rw [normalizeAppResultByProvenance_etyp]
                                      cases typ with
                                      | int =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | bool =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | unit =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                      | ref _ =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                      | arrow _ _ =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                      | string =>
                                          simp [returnSpecToQTyp] at hret
                                          cases hret
                                          simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                      | nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
                          simp only [finish, fnExternFinishAtCursor] at hfinishOk
                          split at hfinishOk
                          · simp at hfinishOk
                          · next innerArgQt nextTag'' hresolve =>
                            simp only [Except.ok.injEq] at hfinishOk
                            cases hfinishOk
                            have hcurrent :
                                ExternDeclarationReachableFromExpr root ctxRoot
                                  (Expr.externFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures) := by
                              intro nestedId d hprog
                              cases hprog with
                              | externFn =>
                                  exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                    ExternDeclarationInReturn.nestedFn_here
                              | externFn_return hret =>
                                  exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                    (ExternDeclarationInReturn.nestedFn_inner hret)
                            have hnestedBase :
                                QTypReachableFrom root ctxRoot
                                  { etyp :=
                                      ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                                        [FnTClosure.extern innerId innerArg innerRet innerEffects
                                          (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures],
                                    poison := ctx.pc,
                                    pred := Predicate.noPred } := by
                              intro nestedId d hreach
                              exact (QTypReachableFrom.of_externFn_result
                                  (resolveArgCondQTyp_fst_poison hresolve) hunifiedCtx hcurrent)
                                (by simpa [unifiedEnv] using hreach)
                            intro nestedId d hreach
                            cases hgate : joinPoison p1 p
                            · exact
                                (QTypReachableFrom.with_etyp
                                  (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                                  (qpred := Predicate.noPred) hnestedBase)
                                  (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                            · exact
                                (QTypReachableFrom.with_etyp
                                  (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                                  (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                      | nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
                          simp only [finish, fnExternFinishAtCursor] at hfinishOk
                          split at hfinishOk
                          · simp at hfinishOk
                          · next innerArgQt nextTag'' hresolve =>
                            simp only [Except.ok.injEq] at hfinishOk
                            cases hfinishOk
                            have hcurrent :
                                ExternDeclarationReachableFromExpr root ctxRoot
                                  (Expr.externPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures) := by
                              intro nestedId d hprog
                              cases hprog with
                              | externPfn =>
                                  exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                    ExternDeclarationInReturn.nestedPfn_here
                              | externPfn_return hret =>
                                  exact QTypReachableFrom.fn_extern_return hqtArrow hmem
                                    (ExternDeclarationInReturn.nestedPfn_inner hret)
                            have hnestedBase :
                                QTypReachableFrom root ctxRoot
                                  { etyp :=
                                      ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                                        [PFnTClosure.extern innerId innerArg innerRet
                                          (VarTypeEnv.toCaptured unifiedEnv) innerArgQt innerCaptures],
                                    poison := ctx.pc,
                                    pred := Predicate.noPred } := by
                              intro nestedId d hreach
                              exact (QTypReachableFrom.of_externPfn_result
                                  (resolveArgCondQTyp_fst_poison hresolve) hunifiedCtx hcurrent)
                                (by simpa [unifiedEnv] using hreach)
                            intro nestedId d hreach
                            cases hgate : joinPoison p1 p
                            · exact
                                (QTypReachableFrom.with_etyp
                                  (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                                  (qpred := Predicate.noPred) hnestedBase)
                                  (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                            · exact
                                (QTypReachableFrom.with_etyp
                                  (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                                  (by simpa [normalizeAppResultByProvenance, hgate] using hreach)

private theorem of_applyPFnTClosureAtCursor
    {root : Expr} {ctxRoot ctx : TypeContext}
    {tcl : PFnTClosure} {st1 st2 : Typ} {p p1 : Poison}
    {argEtyp : ETyp} {argPoison : Poison} {argPred : Predicate}
    {result1 result : TypeResult} {cursor : Tag × Loc}
    {fuel : Nat} {tcls : List PFnTClosure}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (_hctx : ContextReachableFrom root ctxRoot ctx)
    (hqtPfn : QTypReachableFrom root ctxRoot result1.qualType)
    (hpfnEtyp : result1.qualType.etyp = ETyp.parrow st1 st2 p tcls)
    (harg :
      QTypReachableFrom root ctxRoot
        { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
          pred := argPred })
    (hmem : tcl ∈ tcls)
    (happly :
      applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred
        ctx result1 cursor fuel = .ok result) :
    QTypReachableFrom root ctxRoot result.qualType := by
  have hqtParrow :
      QTypReachableFrom root ctxRoot
        { etyp := ETyp.parrow st1 st2 p tcls,
          poison := result1.qualType.poison, pred := result1.qualType.pred } :=
    QTypReachableFrom.of_parrow_etyp_eq hqtPfn hpfnEtyp
  unfold applyPFnTClosureAtCursor at happly
  cases fuel with
  | zero =>
      simp at happly
  | succ fuel' =>
      cases tcl with
      | regular x body σcap =>
          simp [bind, Except.bind] at happly
          cases htcBody :
              typecheckExpr
                { ctx with
                  pc := joinPoison p (joinPoison ctx.pc p1),
                  memEnv := result1.memEnv',
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred },
                  tagEnv := result1.tagEnv',
                  pureCtx := true,
                  nextLoc := cursor.2,
                  nextTag := cursor.1,
                  regime := result1.regime',
                  externRefAllowed := false,
                  declaredExternRefs := result1.declared' } (PExpr.toExpr body) fuel' with
          | error _err =>
              rw [htcBody] at happly
              simp at happly
          | ok bodyResult =>
              rw [htcBody] at happly
              simp at happly
              cases hbodyQt : bodyResult.qualType with
              | mk bodyEtyp bodyPoison bodyPred =>
                  simp [hbodyQt] at happly
                  cases hsub :
                      isErasureOf st2
                        { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred }
                  · simp [hsub] at happly
                  · simp [hsub, pure, Except.pure] at happly
                    cases happly
                    have hbodyCtx :
                        ContextReachableFrom root ctxRoot
                          { ctx with
                            pc := joinPoison p (joinPoison ctx.pc p1),
                            memEnv := result1.memEnv',
                            varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured σcap) x
                              { etyp := argEtyp,
                                poison := joinPoison ctx.pc argPoison,
                                pred := argPred },
                            tagEnv := result1.tagEnv',
                            pureCtx := true,
                            nextLoc := cursor.2,
                            nextTag := cursor.1,
                            regime := result1.regime',
                            externRefAllowed := false,
                            declaredExternRefs := result1.declared' } :=
                      ContextReachableFrom.pfnBody_of_parrow_member
                        hqtPfn hpfnEtyp hmem harg rfl
                    have hbodyReach :
                        ExternDeclarationReachableFromExpr root ctxRoot
                          (PExpr.toExpr body) := by
                      intro id d hprog
                      exact QTypReachableFrom.pfn_regular_body hqtParrow hmem hprog
                    have hbodyResultReach :
                        QTypReachableFrom root ctxRoot bodyResult.qualType :=
                      IH fuel' (Nat.lt_succ_self fuel') hbodyCtx hbodyReach htcBody
                    have hbodyBaseReach :
                        QTypReachableFrom root ctxRoot
                          { etyp := bodyEtyp, poison := bodyPoison, pred := bodyPred } := by
                      intro id d hreach
                      exact hbodyResultReach (by simpa [hbodyQt] using hreach)
                    intro id d hreach
                    cases hgate : joinPoison p1 p
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := joinPoison p1 (joinPoison p bodyPoison))
                          (qpred := bodyPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                    · exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := true) (qpred := Predicate.noPred) hbodyBaseReach)
                          (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
      | extern id x retSpec capturedEnv declaredArgQt =>
          have hcap : CapturedEnvReachableFrom root ctxRoot capturedEnv :=
            QTypReachableFrom.pfn_extern_captured hqtParrow hmem
          have hargQt :
              QTypReachableFrom root ctxRoot
                { etyp := argEtyp, poison := joinPoison ctx.pc argPoison,
                  pred := argPred } := harg
          have hunifiedCtx :
              ContextReachableFrom root ctxRoot
                { ctx with
                  varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
                    { etyp := argEtyp,
                      poison := joinPoison ctx.pc argPoison,
                      pred := argPred } } :=
            ContextReachableFrom.ofCaptured_update hcap ctx hargQt
          let unifiedEnv : VarTypeEnv :=
            VarTypeEnv.update (VarTypeEnv.ofCaptured capturedEnv) x
              { etyp := argEtyp,
                poison := joinPoison ctx.pc argPoison,
                pred := argPred }
          -- Leading argument-condition gate: throw branch is impossible on .ok.
          simp only [bind, Except.bind] at happly
          split at happly
          · simp at happly
          simp only [pure, Except.pure] at happly
          cases retSpec with
          | simple typ poison pred =>
              simp only [] at happly
              cases htag : collectAndAllocExternTags [pred] cursor.1 with
              | error _err =>
                  simp [htag] at happly
              | ok tagResult =>
                  cases tagResult with
                  | mk tagMapping nextTag' =>
                      simp [htag] at happly
                      cases hresPred :
                          resolveSyntaxPred pred unifiedEnv tagMapping with
                      | error _err =>
                          rw [hresPred] at happly
                          simp at happly
                      | ok resolvedPred =>
                          rw [hresPred] at happly
                          simp at happly
                          cases hret :
                              returnSpecToQTyp typ poison resolvedPred cursor.2 with
                          | error _err =>
                              simp [hret] at happly
                          | ok retPair =>
                              cases retPair with
                              | mk retQt nextLoc' =>
                                  simp [hret] at happly
                                  cases happly
                                  apply QTypReachableFrom.of_non_function_etyp
                                  rw [normalizeAppResultByProvenance_etyp]
                                  cases typ with
                                  | int =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | bool =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | unit =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                                  | ref _ =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                  | arrow _ _ =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                  | string =>
                                      simp [returnSpecToQTyp] at hret
                                      cases hret
                                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | nestedFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures =>
              simp only [] at happly
              split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                cases happly
                have hcurrent :
                    ExternDeclarationReachableFromExpr root ctxRoot
                      (Expr.externFn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerEffects innerCaptures) := by
                  intro nestedId d hprog
                  cases hprog with
                  | externFn =>
                      exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                        ExternDeclarationInReturn.nestedFn_here
                  | externFn_return hret =>
                      exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                        (ExternDeclarationInReturn.nestedFn_inner hret)
                have hnestedBase :
                    QTypReachableFrom root ctxRoot
                      { etyp :=
                          ETyp.arrow innerArgTyp (parseReturnType innerRet) ctx.pc
                            [FnTClosure.extern innerId innerArg innerRet innerEffects
                              (VarTypeEnv.toCaptured unifiedEnv) v.1 innerCaptures],
                        poison := ctx.pc,
                        pred := Predicate.noPred } := by
                  intro nestedId d hreach
                  exact (QTypReachableFrom.of_externFn_result
                      (resolveArgCondQTyp_fst_poison hresolve) hunifiedCtx hcurrent)
                    (by simpa [unifiedEnv] using hreach)
                intro nestedId d hreach
                cases hgate : joinPoison p1 p
                · exact
                    (QTypReachableFrom.with_etyp
                      (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                      (qpred := Predicate.noPred) hnestedBase)
                      (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                · exact
                    (QTypReachableFrom.with_etyp
                      (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                      (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
          | nestedPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures =>
              simp only [] at happly
              split at happly
              · simp at happly
              · next v hresolve =>
                simp only [Except.ok.injEq] at happly
                cases happly
                have hcurrent :
                    ExternDeclarationReachableFromExpr root ctxRoot
                      (Expr.externPfn innerId innerArg innerArgTyp innerArgPoison innerArgPred innerRet innerCaptures) := by
                  intro nestedId d hprog
                  cases hprog with
                  | externPfn =>
                      exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                        ExternDeclarationInReturn.nestedPfn_here
                  | externPfn_return hret =>
                      exact QTypReachableFrom.pfn_extern_return hqtParrow hmem
                        (ExternDeclarationInReturn.nestedPfn_inner hret)
                have hnestedBase :
                    QTypReachableFrom root ctxRoot
                      { etyp :=
                          ETyp.parrow innerArgTyp (parseReturnType innerRet) ctx.pc
                            [PFnTClosure.extern innerId innerArg innerRet
                              (VarTypeEnv.toCaptured unifiedEnv) v.1 innerCaptures],
                        poison := ctx.pc,
                        pred := Predicate.noPred } := by
                  intro nestedId d hreach
                  exact (QTypReachableFrom.of_externPfn_result
                      (resolveArgCondQTyp_fst_poison hresolve) hunifiedCtx hcurrent)
                    (by simpa [unifiedEnv] using hreach)
                intro nestedId d hreach
                cases hgate : joinPoison p1 p
                · exact
                    (QTypReachableFrom.with_etyp
                      (qpoison := joinPoison p1 (joinPoison p ctx.pc))
                      (qpred := Predicate.noPred) hnestedBase)
                      (by simpa [normalizeAppResultByProvenance, hgate] using hreach)
                · exact
                    (QTypReachableFrom.with_etyp
                      (qpoison := true) (qpred := Predicate.noPred) hnestedBase)
                      (by simpa [normalizeAppResultByProvenance, hgate] using hreach)

private theorem of_typecheckApp
    {root : Expr} {ctxRoot ctx : TypeContext} {e1 e2 : Expr}
    {fuel : Nat} {res : TypeResult}
    (IH :
      ∀ m < fuel, ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
        ContextReachableFrom root ctxRoot ctx →
        ExternDeclarationReachableFromExpr root ctxRoot e →
        typecheck ctx e m = .ok res →
        QTypReachableFrom root ctxRoot res.qualType)
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent :
      ExternDeclarationReachableFromExpr root ctxRoot (Expr.app e1 e2))
    (htc : typecheckApp ctx e1 e2 fuel = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  cases fuel with
  | zero =>
      simp [typecheckApp] at htc
  | succ fuel' =>
      rcases typecheckApp_arrow_structure_full ctx e1 e2 fuel' res htc with
        ⟨result2, result1, etyp2, p2, pred2, hqt2, htc2, htc1, hcases⟩
      have IH' :
          ∀ m < fuel', ∀ {ctx : TypeContext} {e : Expr} {res : TypeResult},
            ContextReachableFrom root ctxRoot ctx →
            ExternDeclarationReachableFromExpr root ctxRoot e →
            typecheck ctx e m = .ok res →
            QTypReachableFrom root ctxRoot res.qualType := by
        intro m hm ctx e res hctxm hcanm htcm
        exact IH m (Nat.lt_trans hm (Nat.lt_succ_self fuel')) hctxm hcanm htcm
      have hargRaw : QTypReachableFrom root ctxRoot result2.qualType :=
        IH fuel' (Nat.lt_succ_self fuel') hctx
          (ExternDeclarationReachableFromExpr.app_arg hcurrent)
          (by simpa [typecheck] using htc2)
      have harg :
          QTypReachableFrom root ctxRoot
            { etyp := etyp2, poison := joinPoison ctx.pc p2, pred := pred2 } :=
        QTypReachableFrom.of_eq_redecorate hargRaw hqt2
      let ctxFun : TypeContext :=
        { ctx with
          memEnv := result2.memEnv',
          tagEnv := result2.tagEnv',
          nextLoc := result2.nextLoc',
          nextTag := result2.nextTag',
          regime := result2.regime',
          declaredExternRefs := result2.declared' }
      have hctxFun : ContextReachableFrom root ctxRoot ctxFun := by
        intro x qt hlookup
        exact hctx (by simpa [ctxFun] using hlookup)
      have hfnReach : QTypReachableFrom root ctxRoot result1.qualType :=
        IH fuel' (Nat.lt_succ_self fuel') hctxFun
          (ExternDeclarationReachableFromExpr.app_fun hcurrent)
          (by simpa [typecheck, ctxFun] using htc1)
      cases hcases with
      | inl harrow =>
          rcases harrow with
            ⟨st1, st2, p, p1, tcls, results, first, rest, hfnEtyp, _hp1,
              _hnpure, _hnempty, _hsub, hthread, hresults, hjoin⟩
          have hresultsReach :
              ∀ result ∈ results,
                QTypReachableFrom root ctxRoot result.qualType :=
            applyClosuresThreaded_forall_reachable_mem
              (fun tcl cursor =>
                applyFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                  ctx result1 cursor fuel')
              tcls (result1.nextTag', result1.nextLoc') results
              (fun tcl hmem cursor result happly =>
                of_applyFnTClosureAtCursor IH' hctx hfnReach hfnEtyp harg hmem happly)
              hthread
          have hfirstReach : QTypReachableFrom root ctxRoot first.qualType :=
            hresultsReach first (by simp [hresults])
          have hrestReach :
              ∀ result ∈ rest,
                QTypReachableFrom root ctxRoot result.qualType := by
            intro result hmem
            exact hresultsReach result (by simp [hresults, hmem])
          intro id d hreach
          exact (QTypReachableFrom.of_joinTypeResults hfirstReach hrestReach hjoin) hreach
      | inr hparrow =>
          rcases hparrow with
            ⟨st1, st2, p, p1, tcls, results, first, rest, hpfnEtyp, _hp1,
              _hnempty, _hsub, hthread, hresults, hjoin⟩
          have hresultsReach :
              ∀ result ∈ results,
                QTypReachableFrom root ctxRoot result.qualType :=
            applyClosuresThreaded_forall_reachable_mem
              (fun tcl cursor =>
                applyPFnTClosureAtCursor tcl st1 st2 p p1 etyp2 p2 pred2
                  ctx result1 cursor fuel')
              tcls (result1.nextTag', result1.nextLoc') results
              (fun tcl hmem cursor result happly =>
                of_applyPFnTClosureAtCursor IH' hctx hfnReach hpfnEtyp harg hmem happly)
              hthread
          have hfirstReach : QTypReachableFrom root ctxRoot first.qualType :=
            hresultsReach first (by simp [hresults])
          have hrestReach :
              ∀ result ∈ rest,
                QTypReachableFrom root ctxRoot result.qualType := by
            intro result hmem
            exact hresultsReach result (by simp [hresults, hmem])
          intro id d hreach
          exact (QTypReachableFrom.of_joinTypeResults hfirstReach hrestReach hjoin) hreach

set_option linter.unnecessarySeqFocus false in
private theorem opEType?_nonFunction
    {op : Op} {etyp₁ etyp₂ result : ETyp}
    (hop : opEType? op etyp₁ etyp₂ = some result) :
    result.isFunctionType = false := by
  cases op <;> cases etyp₁ <;> cases etyp₂ <;> simp [opEType?] at hop
  all_goals cases hop <;> rfl

set_option linter.unnecessarySeqFocus false in
private theorem opUnaryEType?_nonFunction
    {op : UnaryOp} {etyp result : ETyp}
    (hop : opUnaryEType? op etyp = some result) :
    result.isFunctionType = false := by
  cases op <;> cases etyp <;> simp [opUnaryEType?] at hop
  all_goals cases hop <;> rfl

private theorem surfaceSpecToQTyp_nonFunction
    {typ : Typ} {poison : Poison} {pred : Predicate}
    {ctx ctx' : TypeContext} {qt : QTyp}
    (hsurf : surfaceSpecToQTyp typ poison pred ctx = .ok (qt, ctx')) :
    qt.etyp.isFunctionType = false := by
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure] at hsurf
  cases typ with
  | int | bool | unit | string =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsurf
      rw [← hsurf.1]
      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
  | ref t =>
      -- `surfaceSpecToQTyp` rejects every ref-typed `extern val` surface spec
      -- (the `extern ref` form is the only route to reference-valued externs).
      simp at hsurf
  | arrow _ _ =>
      simp at hsurf

private theorem of_typecheckExternVal
    {root : Expr} {ctxRoot ctx : TypeContext}
    {typ : Typ} {poison : Poison} {pred : SyntaxPredicate} {res : TypeResult}
    (htc : typecheckExternVal ctx typ poison pred = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  apply QTypReachableFrom.of_non_function_etyp
  have hOkPath :
      ∀ pred',
        (do
          let (tagMapping, nextTag') ← collectAndAllocExternTags [pred'] ctx.nextTag
          let resolvedPred ← resolveSyntaxPred pred' ctx.varEnv tagMapping
          let (qt, ctx') ← surfaceSpecToQTyp typ poison resolvedPred ctx
          let out : TypeResult :=
            { qualType := qt, memEnv' := ctx'.memEnv, tagEnv' := ctx.tagEnv,
              nextLoc' := ctx'.nextLoc, nextTag' := nextTag', regime' := ctx.regime,
              declared' := ctx.declaredExternRefs }
          pure out) =
            (.ok res : TypecheckM TypeResult) →
        res.qualType.etyp.isFunctionType = false := by
    intro pred' hpath
    simp [bind, Except.bind] at hpath
    cases htag : collectAndAllocExternTags [pred'] ctx.nextTag with
    | error _err =>
        simp [htag] at hpath
    | ok tagResult =>
        cases tagResult with
        | mk tagMapping nextTag' =>
            simp [htag] at hpath
            cases hresolved : resolveSyntaxPred pred' ctx.varEnv tagMapping with
            | error _err =>
                rw [hresolved] at hpath
                simp at hpath
            | ok resolvedPred =>
                rw [hresolved] at hpath
                simp at hpath
                cases hsurf : surfaceSpecToQTyp typ poison resolvedPred ctx with
                | error _err =>
                    simp [hsurf] at hpath
                | ok surfPair =>
                    cases surfPair with
                    | mk qt ctx' =>
                        simp [hsurf, pure, Except.pure] at hpath
                        cases hpath
                        exact surfaceSpecToQTyp_nonFunction hsurf
  cases poison with
  | false =>
      cases pred with
      | guardClosure idx arg body =>
          simp [typecheckExternVal] at htc
      | guardOnly idx =>
          simp [typecheckExternVal] at htc
      | noPred =>
          exact hOkPath SyntaxPredicate.noPred (by simpa [typecheckExternVal] using htc)
  | true =>
      cases pred with
      | guardClosure idx arg body =>
          exact
            hOkPath (SyntaxPredicate.guardClosure idx arg body)
              (by simpa [typecheckExternVal] using htc)
      | guardOnly idx =>
          exact
            hOkPath (SyntaxPredicate.guardOnly idx)
              (by simpa [typecheckExternVal] using htc)
      | noPred =>
          exact hOkPath SyntaxPredicate.noPred (by simpa [typecheckExternVal] using htc)

theorem of_typecheck
    {root : Expr} {ctxRoot ctx : TypeContext} {e : Expr}
    {fuel : Nat} {res : TypeResult}
    (hctx : ContextReachableFrom root ctxRoot ctx)
    (hcurrent : ExternDeclarationReachableFromExpr root ctxRoot e)
    (htc : typecheck ctx e fuel = .ok res) :
    QTypReachableFrom root ctxRoot res.qualType := by
  revert ctx e res
  induction fuel using Nat.strongRecOn with
  | ind fuel IH =>
      intro ctx e res hctx hcurrent htc
      unfold typecheck at htc
      cases fuel with
      | zero =>
          simp [typecheckExpr] at htc
      | succ fuel' =>
          cases e with
          | num n =>
              simp [typecheckExpr, typecheckInt, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | bool b =>
              simp [typecheckExpr, typecheckBool, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | unit =>
              simp [typecheckExpr, typecheckUnit, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | str s =>
              simp [typecheckExpr, typecheckString, pure, Except.pure] at htc
              cases htc
              apply QTypReachableFrom.of_non_function_etyp
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | var x =>
              exact QTypReachableFrom.of_typecheckVar hctx (by simpa [typecheckExpr] using htc)
          | op e1 op e2 =>
              have htcOp : typecheckOp ctx e1 e2 fuel' op = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckOp_structure ctx e1 e2 op fuel' res htcOp with
                ⟨_result1, _result2, resultEtyp, _htc1, _htc2, hop,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              exact opEType?_nonFunction hop
          | newRef e1 =>
              have htcNew : typecheckNewRef ctx e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckNewRef_structure ctx e1 fuel' res htcNew with
                ⟨_result1, _l, _htc1, _hl, _hint, hetyp, _hpoison, _hpred,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | assign e1 e2 =>
              have htcAssign : typecheckAssign ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckAssign_structure ctx e1 e2 fuel' res htcAssign with
                ⟨_result1, _result2, _ls, _htc1, _href, _htc2, _hint,
                  _hnextLoc, _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | deref e1 =>
              apply QTypReachableFrom.of_non_function_etyp
              have het : res.qualType.etyp = ETyp.int :=
                typecheckDeref_etyp_int ctx e1 fuel' res (by simpa [typecheckExpr] using htc)
              rw [het]
              simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
          | seq e1 e2 =>
              have htcSeq : typecheckSeq ctx e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckSeq_structure ctx e1 e2 fuel' res htcSeq with
                ⟨result1, ctx', _htc1, hctx', htc2⟩
              have hctxSeq : ContextReachableFrom root ctxRoot ctx' := by
                subst ctx'
                exact ContextReachableFrom.ctxAfter hctx
              intro id d hreach
              exact
                (IH (fuel' - 1) (by omega) hctxSeq
                  (ExternDeclarationReachableFromExpr.seq_right hcurrent)
                  (by simpa [typecheck] using htc2)) hreach
          | vlet x e1 e2 =>
              have htcVlet : typecheckVlet ctx x e1 e2 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckVlet_structure ctx x e1 e2 fuel' res htcVlet with
                ⟨result1, result2, ctx', htc1, hctx', htc2, hetyp,
                  _hmem, _htag, _hnextLoc, _hnextTag, _hregime, _hpoison, _hpred⟩
              have hqt1 : QTypReachableFrom root ctxRoot result1.qualType :=
                IH (fuel' - 1) (by omega) hctx
                  (ExternDeclarationReachableFromExpr.vlet_bound hcurrent)
                  (by simpa [typecheck] using htc1)
              have hctxUpdate :
                  ContextReachableFrom root ctxRoot
                    { ctx with varEnv := VarTypeEnv.update ctx.varEnv x result1.qualType } :=
                ContextReachableFrom.update hctx hqt1
              have hctxVlet : ContextReachableFrom root ctxRoot ctx' := by
                intro y qt hlookup
                exact hctxUpdate (by simpa [hctx'] using hlookup)
              have hqt2 : QTypReachableFrom root ctxRoot result2.qualType :=
                IH (fuel' - 1) (by omega) hctxVlet
                  (ExternDeclarationReachableFromExpr.vlet_body hcurrent)
                  (by simpa [typecheck] using htc2)
              cases hresQt : res.qualType with
              | mk resEtyp resPoison resPred =>
                  cases hqt2Qt : result2.qualType with
                  | mk etyp poison pred =>
                      have hqt2' :
                          QTypReachableFrom root ctxRoot
                            { etyp := etyp, poison := poison, pred := pred } := by
                        intro id d hreach
                        exact hqt2 (by simpa [hqt2Qt] using hreach)
                      have het : resEtyp = etyp := by
                        simpa [hresQt, hqt2Qt] using hetyp
                      subst resEtyp
                      intro id d hreach
                      exact
                        (QTypReachableFrom.with_etyp
                          (qpoison := resPoison) (qpred := resPred) hqt2') hreach
          | fn x argTyp body retTyp =>
              exact
                QTypReachableFrom.of_typecheckFn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | pfn x argTyp body retTyp =>
              exact
                QTypReachableFrom.of_typecheckPfn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | app e1 e2 =>
              exact
                QTypReachableFrom.of_typecheckApp (fuel := fuel')
                  (fun m hm {ctx} {e} {res} hctxm hcanm htcm =>
                    IH m (by omega) hctxm hcanm htcm)
                  hctx hcurrent (by simpa [typecheckExpr] using htc)
          | ite e1 e2 e3 =>
              have htcIf : typecheckIf ctx e1 e2 e3 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckIf_structure ctx e1 e2 e3 fuel' res htcIf with htrue | hfalse | hstd
              · rcases htrue with
                  ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool,
                    res2, _res3, htc2, _htc3, _hmem, _htag, _hnextLoc,
                    _hnextTag, _hregime, _hdecl, _hpoison, hetyp⟩
                let ctxTrue : TypeContext :=
                  { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
                             declaredExternRefs := _res1.declared' }
                have hctxTrue : ContextReachableFrom root ctxRoot ctxTrue := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctxTrue] using hlookup)
                have hqt2 : QTypReachableFrom root ctxRoot res2.qualType :=
                  IH (fuel' - 1) (by omega) hctxTrue
                    (ExternDeclarationReachableFromExpr.ite_then hcurrent)
                    (by simpa [typecheck, ctxTrue] using htc2)
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    cases hqt2Qt : res2.qualType with
                    | mk etyp poison pred =>
                        have hqt2' :
                            QTypReachableFrom root ctxRoot
                              { etyp := etyp, poison := poison, pred := pred } := by
                          intro id d hreach
                          exact hqt2 (by simpa [hqt2Qt] using hreach)
                        have het : resEtyp = etyp := by
                          simpa [hresQt, hqt2Qt] using hetyp
                        subst resEtyp
                        intro id d hreach
                        exact
                          (QTypReachableFrom.with_etyp
                            (qpoison := resPoison) (qpred := resPred) hqt2') hreach
              · rcases hfalse with
                  ⟨k, deps, _hmatch, _hreg, _res1, _htc1, _hbool,
                    res2, res3, _htc2, htc3, _hmem, _htag, _hnextLoc,
                    _hnextTag, _hregime, _hdecl, _hpoison, hetyp⟩
                let ctxFalse : TypeContext :=
                  { pc := ctx.pc, regime := ctx.regime, memEnv := ctx.memEnv,
                    varEnv := ctx.varEnv,
                    tagEnv := ctx.tagEnv.insert k { value := false, deps := deps },
                    nextLoc := res2.nextLoc', nextTag := res2.nextTag',
                    pureCtx := ctx.pureCtx,
                    externRegime := ctx.externRegime,
                    externRefAllowed := ctx.externRefAllowed,
                    declaredExternRefs := res2.declared' }
                have hctxFalse : ContextReachableFrom root ctxRoot ctxFalse := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctxFalse] using hlookup)
                have hqt3 : QTypReachableFrom root ctxRoot res3.qualType :=
                  IH (fuel' - 1) (by omega) hctxFalse
                    (ExternDeclarationReachableFromExpr.ite_else hcurrent)
                    (by simpa [typecheck, ctxFalse] using htc3)
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    cases hqt3Qt : res3.qualType with
                    | mk etyp poison pred =>
                        have hqt3' :
                            QTypReachableFrom root ctxRoot
                              { etyp := etyp, poison := poison, pred := pred } := by
                          intro id d hreach
                          exact hqt3 (by simpa [hqt3Qt] using hreach)
                        have het : resEtyp = etyp := by
                          simpa [hresQt, hqt3Qt] using hetyp
                        subst resEtyp
                        intro id d hreach
                        exact
                          (QTypReachableFrom.with_etyp
                            (qpoison := resPoison) (qpred := resPred) hqt3') hreach
              · rcases hstd with
                  ⟨_hstdCase, res1, htc1, _hbool, res2, htc2, res3, htc3,
                    _hmem, _htag, _hnextLoc, _hnextTag, _hregime, _hdecl, _hpoison,
                    hetyp, _hpred⟩
                have hqt1 : QTypReachableFrom root ctxRoot res1.qualType :=
                  IH (fuel' - 1) (by omega) hctx
                    (ExternDeclarationReachableFromExpr.ite_cond hcurrent)
                    (by simpa [typecheck] using htc1)
                let ctx' : TypeContext :=
                  { pc := ctx.pc, regime := res1.regime', memEnv := res1.memEnv',
                    varEnv := ctx.varEnv, tagEnv := res1.tagEnv',
                    nextLoc := res1.nextLoc', nextTag := res1.nextTag',
                    pureCtx := ctx.pureCtx,
                    externRegime := ctx.externRegime,
                    externRefAllowed := ctx.externRefAllowed,
                    declaredExternRefs := res1.declared' }
                let ctx'' : TypeContext :=
                  { ctx' with pc := joinPoison ctx.pc res1.qualType.poison }
                have hctx'' : ContextReachableFrom root ctxRoot ctx'' := by
                  intro x qt hlookup
                  exact hctx (by simpa [ctx'', ctx'] using hlookup)
                have hqt2 : QTypReachableFrom root ctxRoot res2.qualType :=
                  IH (fuel' - 1) (by omega) hctx''
                    (ExternDeclarationReachableFromExpr.ite_then hcurrent)
                    (by simpa [typecheck, ctx'', ctx'] using htc2)
                let ctxForE3 : TypeContext :=
                  { ctx'' with nextLoc := res2.nextLoc', nextTag := res2.nextTag', declaredExternRefs := res2.declared' }
                have hctxE3 : ContextReachableFrom root ctxRoot ctxForE3 := by
                  intro x qt hlookup
                  exact hctx'' (by simpa [ctxForE3] using hlookup)
                have hqt3 : QTypReachableFrom root ctxRoot res3.qualType :=
                  IH (fuel' - 1) (by omega) hctxE3
                    (ExternDeclarationReachableFromExpr.ite_else hcurrent)
                    (by simpa [typecheck, ctxForE3, ctx'', ctx'] using htc3)
                have hjoined :
                    QTypReachableFrom root ctxRoot
                      { etyp := joinETyps res2.qualType.etyp res3.qualType.etyp
                          res2.qualType.poison res3.qualType.poison,
                        poison := joinPoison res2.qualType.poison res3.qualType.poison,
                        pred := joinPredicates res2.qualType.pred res3.qualType.pred } :=
                  QTypReachableFrom.of_joinETyps hqt2 hqt3
                cases hresQt : res.qualType with
                | mk resEtyp resPoison resPred =>
                    have het :
                        resEtyp =
                          joinETyps res2.qualType.etyp res3.qualType.etyp
                            res2.qualType.poison res3.qualType.poison := by
                      simpa [hresQt] using hetyp
                    subst resEtyp
                    intro id d hreach
                    exact
                      (QTypReachableFrom.with_etyp
                        (qpoison := resPoison) (qpred := resPred) hjoined) hreach
          | unaryop op e1 =>
              have htcUnary : typecheckUnaryOp ctx op e1 fuel' = .ok res := by
                simpa [typecheckExpr] using htc
              rcases typecheckUnaryOp_structure ctx op e1 fuel' res htcUnary with
                ⟨_result1, resultEtyp, _htc1, hop, _hmem, _htag, _hnextLoc,
                  _hnextTag, _hregime, hetyp, _hpoison, _hpred⟩
              apply QTypReachableFrom.of_non_function_etyp
              rw [hetyp]
              exact opUnaryEType?_nonFunction hop
          | externVal id typ poison pred =>
              exact QTypReachableFrom.of_typecheckExternVal (by simpa [typecheckExpr] using htc)
          | externFn id arg argTyp retSpec effects =>
              exact
                QTypReachableFrom.of_typecheckExternFn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | externPfn id arg argTyp retSpec =>
              exact
                QTypReachableFrom.of_typecheckExternPfn hctx hcurrent
                  (by simpa [typecheckExpr] using htc)
          | externRef id refPoison refPred cellPoison cellPred =>
              have htcRef :
                  typecheckExternRef ctx id refPoison refPred cellPoison cellPred = .ok res := by
                simpa [typecheckExpr] using htc
              apply QTypReachableFrom.of_non_function_etyp
              simp only [typecheckExternRef, bind, Except.bind, Bool.not_eq_true', pure,
                         Except.pure, Bool.or_eq_true] at htcRef
              split at htcRef
              · simp at htcRef
              · split at htcRef
                · simp at htcRef
                · split at htcRef
                  · split at htcRef
                    · simp only [Except.ok.injEq] at htcRef
                      rw [← htcRef]
                      simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow]
                    · simp at htcRef
                    · simp at htcRef
                  · simp at htcRef
end QTypReachableFrom


private theorem TrustedRegistryAgreesWithFnTClosures.resolve
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {captures : List Capture} {capturedEnv : CapturedVarEnv} {argQt : QTyp}
    (hmem : FnTClosure.extern id x retSpec effects capturedEnv argQt captures ∈ tcls) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures := by
  -- The agreement also yields `entry.decl.argPoison = argQt.poison`; this
  -- `resolve` adapter only needs the matcher, so the poison agreement is
  -- discharged into `_hargPoison` (the binding is enforced at the agreement
  -- premise itself).
  rcases hagrees hmem with ⟨entry, hlookup, hmatch, _hargPoison⟩
  exact ⟨entry, hlookup, TrustedRegistry.lookup_toRuntimeRegistry hlookup, hmatch⟩

private theorem TrustedRegistryAgreesWithPFnTClosures.resolve
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {argQt : QTyp}
    (hmem : PFnTClosure.extern id x retSpec capturedEnv argQt captures ∈ tcls) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      (TrustedRegistry.toRuntimeRegistry tr).get? id = some entry.impl ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures := by
  rcases hagrees hmem with ⟨entry, hlookup, hmatch, _hargPoison⟩
  exact ⟨entry, hlookup, TrustedRegistry.lookup_toRuntimeRegistry hlookup, hmatch⟩

theorem TrustedRegistryAgreesWithFnTClosures.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List FnTClosure}
    (hagrees : TrustedRegistryAgreesWithFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {effects : List Effect} {captures : List Capture} {capturedEnv : CapturedVarEnv} {argQt : QTyp}
    (hmem : FnTClosure.extern id x retSpec effects capturedEnv argQt captures ∈ tcls)
    {implFn : VarEnv → Value → Memory → Address → Except ExternError (Value × Memory × Address)}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value} {mem' : Memory} {addr' : Address}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hpure : callEntry.callConfig.pureMode = false)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.fn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue
        callEntry.callConfig.memory callEntry.callConfig.nextAddr =
        Except.ok (vRaw, mem', addr'))
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = { callEntry.callConfig with memory := mem', nextAddr := addr' }) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesFn entry id x argTyp retSpec effects captures ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  rcases TrustedRegistryAgreesWithFnTClosures.resolve hagrees hmem with
    ⟨entry, hlookup, hlookupRuntime, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesFn entry id callEntry.argName argTyp retSpec effects captures := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hlookupRuntime
  have hGetDecl : callEntry.callConfig.registry.get? entry.decl.id =
      some (ExternImpl.fn implFn) := by
    simpa [TrustedRegistryEntryMatchesFn.id_eq hmatch] using hGet
  have himpl : entry.impl = ExternImpl.fn implFn := by
    exact Option.some.inj (hlookupCall.symm.trans hGetDecl)
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.fn_of_match hmatch' hpure hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩

theorem TrustedRegistryAgreesWithPFnTClosures.callBoundaryRun
    {tr : TrustedRegistry} {argTyp : Typ} {tcls : List PFnTClosure}
    (hagrees : TrustedRegistryAgreesWithPFnTClosures tr argTyp tcls)
    {id : ExternId} {x : Name} {retSpec : ExternReturn}
    {capturedEnv : CapturedVarEnv} {argQt : QTyp}
    (hmem : PFnTClosure.extern id x retSpec capturedEnv argQt captures ∈ tcls)
    {implFn : VarEnv → Value → Memory → Except ExternError Value}
    {callEntry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {v vRaw : Value}
    (hargName : callEntry.argName = x)
    (hregistry : callEntry.callConfig.registry = TrustedRegistry.toRuntimeRegistry tr)
    (hunified :
      callEntry.unifiedEnv =
        VarEnv.update callEntry.capturedEnv callEntry.argName callEntry.argValue)
    (hGet : callEntry.callConfig.registry.get? id = some (ExternImpl.pfn implFn))
    (hArg : valueMatchesTyp callEntry.argValue argTyp = true)
    (hImpl :
      implFn callEntry.unifiedEnv callEntry.argValue callEntry.callConfig.memory =
        Except.ok vRaw)
    (hValRet : validateExternReturn id retSpec vRaw = Except.ok v)
    (hcfg : cf = callEntry.callConfig) :
    ∃ entry,
      TrustedRegistry.lookup? tr id = some entry ∧
      TrustedRegistryEntryMatchesPfn entry id x argTyp retSpec captures ∧
      ExternCallBoundaryRun entry.decl entry.impl callEntry res cf v := by
  rcases TrustedRegistryAgreesWithPFnTClosures.resolve hagrees hmem with
    ⟨entry, hlookup, hlookupRuntime, hmatch⟩
  have hmatch' :
      TrustedRegistryEntryMatchesPfn entry id callEntry.argName argTyp retSpec captures := by
    simpa [hargName] using hmatch
  have hlookupCall : callEntry.callConfig.registry.get? entry.decl.id = some entry.impl := by
    rw [hregistry]
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hlookupRuntime
  have hGetDecl : callEntry.callConfig.registry.get? entry.decl.id =
      some (ExternImpl.pfn implFn) := by
    simpa [TrustedRegistryEntryMatchesPfn.id_eq hmatch] using hGet
  have himpl : entry.impl = ExternImpl.pfn implFn := by
    exact Option.some.inj (hlookupCall.symm.trans hGetDecl)
  exact
    ⟨entry, hlookup, hmatch,
      ExternCallBoundaryRun.pfn_of_match hmatch' hunified hlookupCall himpl
        hArg hImpl hValRet hcfg⟩
