# FFI Axioms: Per-Extern Evidence Registry

Status: design document, companion to `doc/ffi-proposal.md`.

This document proposes a unified per-extern evidence model for all FFI
contracts: the driver supplies, for each registered extern, a bundle of
proofs witnessing the contracts that extern needs to satisfy. The bundle
is a runtime input to the fault-robustness proof — not a set of global
axioms admitted once and for all.

Two of the five contracts below (**A**, **B**) are already admitted as
universally-quantified axioms in `LeanProofs/ExternAxioms.lean` and are
used by the current proof development. The remaining three (**C**, **D**,
**E**) are proposed new contracts needed to close the pending
extern-related `sorry`s. Under this proposal, **all five migrate into
per-extern evidence**, and `ExternAxioms.lean` ends up axiom-free.

### Two layers: typing vs. implementation

The contracts split cleanly along a fundamental axis:

- **Typing-layer (A, B).** Properties of an extern *declaration*. They
  apply to every declared extern in the program AST regardless of
  whether a runtime implementation has been registered under the same
  id. They are consumed by the typechecker and by typing-level FR
  reasoning. A program with a declaration but no matching registration
  still needs A and B to typecheck; it just errors at runtime on
  dispatch.
- **Implementation-layer (C, D, E).** Properties of a registered
  runtime *implementation* — claims that the driver-supplied code is
  well-behaved. They apply only when an impl is actually present in
  the registry. An unregistered declaration contributes no
  implementation-layer obligation because there is no impl whose
  behaviour needs to be constrained.

The evidence registry below reflects this split: declaration evidence
is keyed by extern id (one bundle per declaration); implementation
evidence is keyed by `(id, impl)` (one bundle per registration).

## Context

The extern runtime is implemented (`LeanPoison/Runtime.lean`,
`LeanPoison/BigStep.lean`). Three `sorry`s remain in `LeanProofs/` that
genuinely require driver-supplied evidence:

1. `wfConfig` preservation for `app`, fn-dispatch case
   (`LeanProofs/SemanticsProperties.lean`).
2. `wfConfig` preservation for `externVal` case, `ref int` subcase
   (`LeanProofs/SemanticsProperties.lean`).
3. `terminatesTo_extern_absurd` replacement at six call sites
   (`LeanProofs/FaultRobustnessProofs.lean`).

The typing-side floor in `LeanProofs/ExternAxioms.lean` contributes two
live axioms (Contracts A and B below). The new design folds these into
the same evidence bundle as the three new contracts (C, D, E).

## Design principles

- **Evidence passing over global axioms.** Every trust-level obligation
  is a proof term attached to the specific extern it concerns, not a
  universally-quantified axiom. The top-level FR theorem takes a
  "trusted registry" as input.
- **Typing / implementation separation.** Declaration-scoped
  obligations (typing-layer) and impl-scoped obligations
  (implementation-layer) live in distinct evidence bundles. Keeping the
  two apart lets a program typecheck without any impl evidence, and
  lets a driver supply impl evidence only for the subset of declared
  externs it actually registers.
- **Minimality.** Each contract expresses one thing that cannot be
  proved structurally. Where the shape check (`valueMatchesTyp`), the
  first-order input restriction, or the int-only heap model already
  discharge an obligation, no contract is introduced.
- **Granularity.** Narrow per-invocation / per-registration claims are
  preferred over monolithic `wfConfig`-style ones.
- **Composition.** Contracts address distinct state components: tag
  mapping, type-level guard cells, runtime memory values, address
  ordering, initial registry bounds. The overlap audit at the end
  confirms no redundancy.
- **Semantic force for syntactic annotations.** Language-level `effects`
  clauses on `extern fn` gain runtime semantic meaning via Contract C.

## The evidence registry

Two evidence bundles, one per layer, packaged into a single
`TrustedRegistry` input to the FR proof.

### Typing-layer: declaration evidence

```lean
/-- Typing-layer evidence: properties of an extern *declaration*.
    Required for every extern in the program AST regardless of
    registration status. -/
structure ExternDeclarationEvidence (id : ExternId) : Prop where
  -- Contract A: tag-mapping coherence (all declaration kinds)
  tagSoundness    : Contract_A id
  -- Contract B: impure guard provenance (impure declarations only;
  --              `True` otherwise)
  guardProvenance : Contract_B id
```

### Implementation-layer: registered-impl evidence

```lean
/-- Implementation-layer evidence: properties of a registered runtime
    implementation. Required only for ids that actually appear in the
    runtime registry. Fields that do not apply to a given impl kind
    reduce to `True`. -/
structure ExternImplEvidence
    (id : ExternId) (impl : ExternImpl) : Prop where
  -- Contract C: fn frame (.fn only; True otherwise)
  frame           : Contract_C id impl
  -- Contract D: fn address monotonicity (.fn only; True otherwise)
  addrMono        : Contract_D id impl
  -- Contract E: ref-val init address bound
  --             (.val (.loc _) at ref int only; True otherwise)
  refInBounds     : Contract_E id impl
```

### The combined trusted registry

```lean
/-- Trusted registry: one typing-layer bundle per declared extern,
    plus one implementation-layer bundle per registered impl. -/
structure TrustedRegistry where
  -- Typing-layer: covers every declared extern (from program AST).
  declEv  : ∀ id, ExternDeclared id → ExternDeclarationEvidence id
  -- Implementation-layer: covers every registered impl (from driver).
  reg     : ExternRegistry
  implEv  : ∀ id impl,
              reg.get? id = some impl → ExternImplEvidence id impl
```

Equivalent list-shaped view (what the driver actually writes):

```lean
/-- One entry per registered impl; pairs impl with its
    implementation-layer evidence. -/
structure TrustedExternImpl where
  id       : ExternId
  impl     : ExternImpl
  evidence : ExternImplEvidence id impl

/-- One entry per declared extern; carries typing-layer evidence. -/
structure TrustedExternDeclaration where
  id       : ExternId
  evidence : ExternDeclarationEvidence id

def TrustedRegistry.ofLists
    (decls : List TrustedExternDeclaration)
    (impls : List TrustedExternImpl)
    (huniqDecls : decls.Pairwise (fun a b => a.id ≠ b.id))
    (huniqImpls : impls.Pairwise (fun a b => a.id ≠ b.id))
    (hcover    : ∀ e ∈ impls, ∃ d ∈ decls, d.id = e.id) :
    TrustedRegistry := ...
```

`hcover` enforces that every registered impl has a matching
declaration — an impl without a declaration is a driver bug that the
typechecker has no contract to reason about.

FR-level theorems take `(tr : TrustedRegistry)` and destructure the
appropriate layer on demand: `tr.declEv id hdecl` at
extern-declaration typechecking sites, and `tr.implEv id impl hreg` at
runtime dispatch sites. Non-extern proof sites are unaffected.

## Contracts

### Contract A — Tag Mapping Soundness

**Layer:** typing (declaration-scoped).
**Status:** ✅ **Already admitted and used.**
Lives today as `axiom externTagSoundness` in
`LeanProofs/ExternAxioms.lean`. Consumed by the current proof
development at extern-declaration typechecking sites. Under this
proposal, restated as a per-declaration field in
`ExternDeclarationEvidence`.

**Current admitted form (universally quantified):**

```lean
-- LeanProofs/ExternAxioms.lean (existing, live axiom)
axiom externTagSoundness
  (tm : TagMeaning)
  (mapping : TagMapping)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag
              = .ok (mapping, nextTag')) :
  TagMappingRespectsTagMeaning tm mapping preds env
```

**Proposed per-declaration form:**

```lean
def Contract_A (id : ExternId) : Prop :=
  ∀ (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (tm : TagMeaning) (mapping : TagMapping)
    (nextTag nextTag' : Tag),
    DeclaredPredsFor id = some preds →
    collectAndAllocExternTags preds nextTag
      = .ok (mapping, nextTag') →
    TagMappingRespectsTagMeaning tm mapping preds env
```

Parameterised by `id` alone — no `impl` argument, because Contract A
is about the declared predicates of an extern, not about any
registered implementation. `DeclaredPredsFor id` scopes the claim to
the predicates of the single extern declaration bearing `id`; the
universal form is recovered by quantifying over all ids that appear
in the declaration environment.

**Plain-English intuition.**

> Whatever predicates my extern declaration names, the fresh tags we
> allocate for them are compatible with any tag meaning the surrounding
> typing context might assign.

**Discussion.** Not structurally provable because `tm` is universally
quantified and `wfTagMeaningCtx` does not constrain fresh tags. The
semantic content is unchanged by per-declaration phrasing; the
relocation into the typing-layer evidence bundle is purely structural.
Applies to all declaration kinds because any extern declaration
(`externVal`, `externFn`, `externPfn`) can carry predicates. Does not
depend on whether an impl is registered for this id.

### Contract B — Impure Extern Guard Provenance

**Layer:** typing (declaration-scoped).
**Status:** ✅ **Already admitted and used.**
Lives today as `axiom externGuardProvenance` in
`LeanProofs/ExternAxioms.lean`. Consumed by the current FR proof
development at impure extern call sites. Under this proposal, restated
as a per-declaration field in `ExternDeclarationEvidence`, scoped to
impure (`externFn`) declarations.

**Current admitted form (universally quantified):**

```lean
-- LeanProofs/ExternAxioms.lean (existing, live axiom)
axiom externGuardProvenance
  (ctx : TypeContext) (r : TypeResult)
  (hcall : ImpureExternCallOk ctx r)
  (hpc : ctx.pc = true)
  (l : Loc) (k : Tag) (qt_out : QTyp)
  (hout : trustedGuardedCell r.memEnv' r.regime' l k qt_out) :
  ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
```

**Proposed per-declaration form:**

```lean
def Contract_B (id : ExternId) : Prop :=
  IsImpureExternDeclaration id →
  ∀ (ctx : TypeContext) (r : TypeResult),
    ImpureExternCallOkForId id ctx r →
    ctx.pc = true →
    ∀ l k qt_out,
      trustedGuardedCell r.memEnv' r.regime' l k qt_out →
      ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
```

The hypothesis `IsImpureExternDeclaration id` makes the claim vacuous
for `externVal` and `externPfn` declarations. `ImpureExternCallOkForId
id ctx r` refines the existing `ImpureExternCallOk` to calls that
dispatch through `id` specifically.

**Plain-English intuition.**

> If my impure extern produces a trusted-guarded cell in the output,
> there was already a trusted-guarded cell at the same location in the
> input. Impure externs do not conjure new guards while pc is poisoned.

**Discussion.** Same semantic content as the current axiom, narrowed
to a specific id. Vacuous for `externVal` and `externPfn` declarations
because only `externFn` triggers the FR `ImpureExternCallOk` path.
Like Contract A, Contract B is a property of the declaration's
type-level summary, not of any registered impl: it constrains what
typing results an impure extern *could* produce, regardless of whether
a runtime impl backs it.

### Contract C — Extern Fn Frame

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new).** Keystone of the semantics-side
story. A claim about how the driver-supplied `fn` impl behaves at
runtime — not required when no impl is registered.

**Per-extern form:**

```lean
/-- Concrete address set denoted by an effects clause at dispatch.
    Shared with Contract B's typing-side use so typing and semantics
    stay definitionally synchronised. -/
def resolveEffects (effs : List Effect)
    (env : VarEnv) (arg : Value) (reg : ExternRegistry)
    : List Address := sorry  -- concrete definition to be supplied

def Contract_C (id : ExternId) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn f =>
      ∀ (effs : List Effect),
        DeclaredEffectsFor id = some effs →
        ∀ {env : VarEnv} {arg v : Value}
          {m₀ mem' : Memory} {addr₀ addr' : Address}
          {reg : ExternRegistry},
          reg.get? id = some (.fn f) →
          f env arg m₀ addr₀ = .ok (v, mem', addr') →
          ∀ a, a < addr₀ →
               a ∉ resolveEffects effs env arg reg →
               mem'.lookup a = m₀.lookup a
  | _     => True
```

**Plain-English intuition.**

> An extern `fn` only writes to cells listed in its declared `effects`
> clause, plus any it allocated during the call. Every other
> pre-existing cell is bit-identical before and after the call.

**Discussion.** Without this contract, `effects` is a typing decoration
with no runtime teeth. With it:

- **`wfMem` preservation becomes local.** Cells outside effects inherit
  `wfMem addr₀ m₀` via frame + monotonicity; cells inside effects and
  freshly allocated cells are integer-valued under the current heap
  model. No separate `wfMem` axiom is needed.
- **FR carries cleanness and guards across extern calls.** Cells
  outside effects keep pre-call guards and cleanness — mirroring
  `PreservesInheritedCleanLocs` for user closures, and the single
  biggest lever for FR across extern fn *dispatches* inside
  `StepFRApp`.  (The six former `terminatesTo_extern_absurd` call sites
  sit at extern *declaration*, not dispatch, so they consume A and E —
  not C.)
- **The driver burden is natural.** Drivers typically know *what they
  wrote*; proving "I only wrote to X and Y" is easier than a global
  `wfMem` claim.

Open formalisation points:

- `resolveEffects` needs a concrete definition. Sharing with Contract
  B's typing-side effect reasoning keeps the two synchronised by
  construction.
- `DeclaredEffectsFor` is a placeholder: a declaration-environment
  mapping `ExternId → declaration syntax` must live somewhere —
  probably a small extension to `Config` or a companion static map.
  Contract E also needs this.

### Contract D — Extern Fn Address Monotonicity

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new).** Surgical; consumed at a single
proof site. A claim about how the driver-supplied `fn` impl behaves at
runtime.

**Per-extern form:**

```lean
def Contract_D (id : ExternId) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn f =>
      ∀ {env : VarEnv} {arg v : Value}
        {m₀ mem' : Memory} {addr₀ addr' : Address},
        f env arg m₀ addr₀ = .ok (v, mem', addr') →
        addr₀ ≤ addr'
  | _     => True
```

**Plain-English intuition.**

> An extern `fn` can allocate new cells (pushing `nextAddr` up) but
> never rewinds — the fresh-allocation boundary only moves forward.

**Discussion.** Consumed at the `app` fn-case of `wfConfig`
preservation to re-prove `wfVarEnv addr' cfg.varEnv` via monotonicity;
also load-bearing in the whole-evaluation `nextAddr` monotonicity
lemma once extended to fn dispatch (which in turn feeds Contract E's
intermediate-cfg transport).

Independent of Contract C: "only effects cells and cells ≥ addr₀ are
mutated" is compatible with `addr' = 0` and `mem' = ∅`, violating
monotonicity. D cannot be derived from C.

### Contract E — Registered Ref-Typed Extern Val in Bounds

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new).** Narrow: only ref-typed `.val`
registrations. A claim about the registered runtime value, hence
impl-scoped even though the value has no dispatch behaviour of its
own.

**Per-extern form:**

```lean
def Contract_E (id : ExternId) (impl : ExternImpl) : Prop :=
  match impl with
  | .val (.loc a) =>
      DeclaredTypeFor id = some (Typ.ref .int) →
      ∀ (cfg₀ : Config),
        InitialConfig cfg₀ →
        cfg₀.registry.get? id = some (.val (.loc a)) →
        a < cfg₀.nextAddr
  | _             => True
```

**Plain-English intuition.**

> Any reference the driver registers at type `ref int` must live inside
> the initial memory — its address is strictly below the initial
> `nextAddr`.

**Discussion.** Stated at the initial configuration. The intermediate
claim `wfValue cfg.nextAddr (Value.loc a)` at a reachable `cfg` follows
from Contract E at init plus the (proven) whole-evaluation `nextAddr`
monotonicity lemma.

Discharged by the driver at setup: `Main.lean` initialises
`Config.memory` with integer cells at the addresses named in ref-typed
externVal registrations, then sets `Config.nextAddr` strictly above
them. Vacuous for all impls except `.val (.loc _)`.

## How evidence is consumed

Typing-layer evidence is retrieved by id from `tr.declEv`;
implementation-layer evidence by `(id, impl)` from `tr.implEv`:

```lean
-- Before (global axioms):
theorem FaultRobustness_step ... := by
  ...
  have := externGuardProvenance ctx r hcall hpc l k qt hout          -- B
  have := externTagSoundness tm mapping preds env _ _ halloc          -- A
  ...

-- After (evidence registry, two layers):
theorem FaultRobustness_step (tr : TrustedRegistry) ... := by
  ...
  -- Typing-layer lookup (no registration required):
  have hdecl := tr.declEv id hDeclared
  have := hdecl.guardProvenance hImpure ctx r hcallId hpc l k qt hout -- B
  have := hdecl.tagSoundness preds env tm mapping _ _ hpreds halloc   -- A

  -- Implementation-layer lookup (only when dispatching):
  have himpl := tr.implEv id impl hreg
  have := himpl.frame effs hEffs hreg hrun a hlo hne                  -- C
  ...
```

Top-level theorems — `TypeSystemEnforcesFaultRobustness` and
companions — gain a `tr : TrustedRegistry` parameter and thread it to
whichever `StepFR*` modules need it. Pure-Poison steps are unaffected;
`tr` is carried but never destructured.

## Migration plan for Contracts A and B

Both live today as admitted axioms and have call sites spread across
`LeanProofs/`. Moving them into the typing-layer evidence bundle is a
structural refactor, not a semantic change:

1. Introduce `ExternDeclarationEvidence`, `ExternImplEvidence`, and
   `TrustedRegistry` in `LeanProofs/ExternAxioms.lean` (or a sibling
   file).
2. Re-derive the current universal axiom statements from the bundle
   fields as *theorems* (trivial once `tr` is in scope):

   ```lean
   theorem externTagSoundness_of_registry
       (tr : TrustedRegistry) ... :
       -- same conclusion as the old axiom
       ... :=
     (tr.declEv id hDeclared).tagSoundness ...
   ```

3. Thread `tr` through the top-level FR theorems and intermediate
   lemmas that reach extern sites.
4. Retire the original `axiom` declarations. At that point
   `ExternAxioms.lean` contains **zero** `axiom` declarations — only
   structure definitions, `Contract_*` predicates, and helper lemmas.

Because A and B are typing-layer, migration can proceed independently
of any decision about the implementation-layer contracts (C/D/E).
Step 4 is the concrete axiom-hygiene payoff: the file that today
admits two live axioms becomes axiom-free.

## Sorries discharged

Status below is as of the current `ffi` branch.

| `sorry` location | Layer | Evidence consumed | Current status | Notes |
|------------------|-------|-------------------|----------------|-------|
| `SemanticsProperties.lean:425` — `app` fn-case `wfConfig` preservation | impl | `implEv.frame` (C), `implEv.addrMono` (D) | ⏳ open | C gives `wfMem addr' mem'` via frame + int-only heap; D gives `wfVarEnv addr' cfg.varEnv` via monotonicity. |
| `SemanticsProperties.lean:1899` — `externVal` `ref int` `wfConfig` preservation | impl | `implEv.refInBounds` (E) + proven `nextAddr` monotonicity | ⏳ open | E at init, monotonicity transports to intermediate `cfg`. |
| `FaultRobustnessProofs.lean` — former `terminatesTo_extern_absurd` × 6 | typing (+ impl for `ref int` val) | `declEv.tagSoundness` (A); `implEv.refInBounds` (E) only for the `externVal (ref int)` subcase | ✅ **currently vacuous** — closed without any FFI evidence | See "Vacuous-premise note" below. |

### Vacuous-premise note on the six `terminatesTo_extern_absurd` sites

These six sites currently close **without any `sorry` and without
consuming Contracts A or E**. The reason is a property of the present
FR theorem statement, not of the extern contracts:

- The theorem instantiates `terminatesTo` against a `Config` literal
  that omits the `registry` field, so `Config.registry` defaults to
  `emptyExternRegistry` (the default in `LeanPoison/Syntax.lean`).
- Under an empty registry, `beval` for any of `externVal` / `externFn`
  / `externPfn` returns `.runtimeError (ExternError.format (.missing
  id))` — the registry lookup fails.
- `terminatesTo` is the success relation, so the premise is
  unsatisfiable. Each of the six cases closes by `cases fuel` + `simp
  [LeanPoison.beval, emptyExternRegistry] at hbeval`.

This is an honest proof, but it reveals that the current top-level FR
statement is **trivially true for extern declarations** — it silently
assumes no extern can ever succeed. When the evidence-registry refactor
threads a populated `Config.registry` (and the corresponding
`TrustedRegistry` with `declEv` / `implEv`) into the theorem, these
six cases will re-open and become real obligations:

- Three sites (`externFn`, `externPfn`, plus the non-ref subcase of
  `externVal`) will consume `declEv.tagSoundness` (Contract A).
- Three sites for `externVal` (one of them doubling with the above
  where the declared type is `ref int`) will additionally consume
  `implEv.refInBounds` (Contract E).
- Contracts B, C, D remain out of scope here because these sites are
  at extern *declaration* form, not at extern call dispatch. They are
  consumed inside `StepFRApp` when an extern closure is actually
  applied.

### `FnTClosure.extern` representation gap (follow-up)

While closing the six vacuous sites, a structural gap surfaced that
will bite when the registry is populated: `valueHasETyp.closure` and
`deepValueQTypProperty.closure` currently only match
`FnTClosure.regular` members; neither has a constructor for
`FnTClosure.extern`. Under the vacuous-premise closure this is never
reached, but once a populated registry is threaded in, the FR theorem
will need either:

- an additional constructor on `valueHasETyp` / `deepValueQTypProperty`
  for `FnTClosure.extern`; or
- Contract A to directly supply the value-typing witness for extern
  closures at each call site.

Flagging this as a design follow-up for the evidence-registry refactor
— the choice between "extend the inductive" and "have A do the work"
affects both the shape of Contract A in the bundle and the overall
size of the refactor.

### Other extern-related sorries

All other extern-related `sorry`s in the proof development concern
top-level extern *declarations* (which leave `Config` unchanged) and
close mechanically without any evidence — the same pattern as the six
former `terminatesTo_extern_absurd` sites, and for the same reason
(empty-registry default in the theorem statement).

## Overlap audit

The five contracts address distinct parts of extern state. No
redundancy, no contradiction.

| | Object addressed | Quantifier | When checked |
|---|---|---|---|
| A | tag mapping vs. `TagMeaning` | ∀ typing context | typecheck time |
| B | type-level trusted guard cells | ∀ impure call to id | typecheck time |
| C | runtime memory values outside `effects` | ∀ fn call to id | dispatch time |
| D | `nextAddr` ordering | ∀ fn call to id | dispatch time |
| E | registered `loc` address | per registration | init |

B and C both touch "effects" but at different layers (type-level guards
vs. value-level memory). Sharing one `resolveEffects` definition keeps
typing and semantics synchronised; the two contracts still compose
rather than overlap.

## Latent obligations

Discharged today by existing restrictions. Each would reintroduce an
evidence field (flavour: Contract C) if the matching restriction
loosened.

- **Effect-cell value boundedness.** For each `a ∈ resolveEffects`,
  `wfValue addr' (mem'[a])`. Free under the int-only heap model.
- **Fresh-cell value boundedness.** Same on `[addr₀, addr')`. Same
  status.
- **Fn return value boundedness.** `wfValue addr' v`. Free because
  extern `fn` returns are first-order non-ref.
- **Pfn return value boundedness.** `wfValue cfg.nextAddr v`. Free for
  the same reason.

## Stability and determinism

Not captured as contracts; not required by current pending `sorry`s.
Within-run determinism is a property of the runtime by construction.
Cross-run stability is only needed if FR is extended to compare
independent runs of the same extern directly.

## Summary

Five contracts, two layers:

| # | Name | Layer | Status | Scope | Consumed at |
|---|------|-------|--------|-------|-------------|
| A | Tag Mapping Soundness | typing | ✅ admitted (to migrate) | every declaration | extern-decl typechecking |
| B | Impure Extern Guard Provenance | typing | ✅ admitted (to migrate) | impure (`externFn`) declarations | StepFR App fn-case |
| C | Extern Fn Frame | impl | 🟡 proposed | registered `.fn` impls | `wfConfig` preservation + FR |
| D | Extern Fn Address Monotonicity | impl | 🟡 proposed | registered `.fn` impls | `wfConfig` preservation |
| E | Registered Ref-Typed Extern Val In Bounds | impl | 🟡 proposed | registered `.val (.loc _)` at `ref int` | `externVal` preservation + FR declaration sites |

**Typing-layer (A, B)** constrain properties of extern declarations in
the program AST. They are consumed whenever a declaration is
typechecked, regardless of whether a runtime implementation is
registered under the same id.

**Implementation-layer (C, D, E)** constrain well-behavedness of the
driver-supplied runtime code (or registered value, in E's case). They
are consumed only when the registry actually contains an impl for
that id — an unregistered declaration carries no implementation-layer
obligation.

Contracts A and B already exist as universally-quantified axioms and
are consumed by the current proof development; migrating them into
`ExternDeclarationEvidence` is structural. Contracts C, D, and E are
new and close the three pending extern-related `sorry`s by landing in
`ExternImplEvidence`.

End state: `ExternAxioms.lean` contains zero `axiom` declarations —
only the `TrustedRegistry`, `ExternDeclarationEvidence`, and
`ExternImplEvidence` structures, `Contract_{A,B,C,D,E}` predicate
definitions, and derived compatibility theorems restating the old
universal axiom forms from the bundle. The top-level FR theorem
becomes evidence-parameterised:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (tr : TrustedRegistry) (cfg₀ : Config)
    (hreg : cfg₀.registry = tr.reg) ... :
  ... FR conclusion ...
```

Concrete drivers (e.g. `Main.lean`) supply a `TrustedRegistry` with
concrete proofs — typing-layer evidence for every declared extern plus
implementation-layer evidence for every registered impl. Abstract
reasoning and separate-compilation scenarios supply hypothetical
registries to prove component FR independently.
