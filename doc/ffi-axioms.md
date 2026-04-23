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
extern-related `sorry`s. Under this proposal, **all five migrate into the
same per-extern evidence bundle**, and `ExternAxioms.lean` ends up
axiom-free.

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
  is a proof term attached to the specific registered extern it
  concerns, not a universally-quantified axiom. The top-level FR
  theorem takes a "trusted registry" as input.
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

The driver supplies a `TrustedRegistry` pairing the runtime
`ExternRegistry` with per-entry evidence bundles.

```lean
/-- Per-extern evidence. Fields that do not apply to a given impl kind
    reduce to `True`, so drivers supply a single proof shape regardless
    of kind. -/
structure ExternEvidence (id : ExternId) (impl : ExternImpl) : Prop where
  -- Contract A: tag-mapping coherence (all kinds)
  tagSoundness    : Contract_A id impl
  -- Contract B: impure guard provenance (.fn only; True otherwise)
  guardProvenance : Contract_B id impl
  -- Contract C: fn frame (.fn only; True otherwise)
  frame           : Contract_C id impl
  -- Contract D: fn address monotonicity (.fn only; True otherwise)
  addrMono        : Contract_D id impl
  -- Contract E: ref-val init address bound
  --              (.val (.loc _) at ref int only; True otherwise)
  refInBounds     : Contract_E id impl

/-- A trusted registry: runtime registry + per-entry evidence. -/
structure TrustedRegistry where
  reg      : ExternRegistry
  evidence : ∀ id impl,
               reg.get? id = some impl → ExternEvidence id impl
```

Equivalent list-shaped view (what the driver actually writes):

```lean
structure TrustedExtern where
  id       : ExternId
  impl     : ExternImpl
  evidence : ExternEvidence id impl

def TrustedRegistry.ofList (xs : List TrustedExtern)
    (huniq : xs.Pairwise (fun a b => a.id ≠ b.id)) :
    TrustedRegistry := ...
```

FR-level theorems take `(tr : TrustedRegistry)` and destructure
`tr.evidence id impl hreg` at each extern call site to consume the
specific contract field they need. Non-extern proof sites are
unaffected: `tr` threads through but is not consumed.

## Contracts

### Contract A — Tag Mapping Soundness

**Status:** ✅ **Already admitted and used.**
Lives today as `axiom externTagSoundness` in
`LeanProofs/ExternAxioms.lean`. Consumed by the current proof
development at extern-declaration typechecking sites. Under this
proposal, restated as a per-extern field in the evidence bundle.

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

**Proposed per-extern form:**

```lean
def Contract_A (id : ExternId) (_impl : ExternImpl) : Prop :=
  ∀ (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (tm : TagMeaning) (mapping : TagMapping)
    (nextTag nextTag' : Tag),
    DeclaredPredsFor id = some preds →
    collectAndAllocExternTags preds nextTag
      = .ok (mapping, nextTag') →
    TagMappingRespectsTagMeaning tm mapping preds env
```

`DeclaredPredsFor id` scopes the claim to the predicates of the single
extern declaration bearing `id`; the universal form is recovered by
quantifying over all ids that appear in the declaration environment.

**Plain-English intuition.**

> Whatever predicates my extern declaration names, the fresh tags we
> allocate for them are compatible with any tag meaning the surrounding
> typing context might assign.

**Discussion.** Not structurally provable because `tm` is universally
quantified and `wfTagMeaningCtx` does not constrain fresh tags. The
semantic content is unchanged by per-extern phrasing; the relocation
into the evidence bundle is purely structural. Applies to all impl
kinds because any extern declaration can carry predicates.

### Contract B — Impure Extern Guard Provenance

**Status:** ✅ **Already admitted and used.**
Lives today as `axiom externGuardProvenance` in
`LeanProofs/ExternAxioms.lean`. Consumed by the current FR proof
development at impure extern call sites. Under this proposal, restated
as a per-extern field scoped to `.fn` impls.

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

**Proposed per-extern form:**

```lean
def Contract_B (id : ExternId) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn _ =>
      ∀ (ctx : TypeContext) (r : TypeResult),
        ImpureExternCallOkForId id ctx r →
        ctx.pc = true →
        ∀ l k qt_out,
          trustedGuardedCell r.memEnv' r.regime' l k qt_out →
          ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
  | _     => True
```

where `ImpureExternCallOkForId id ctx r` refines the existing
`ImpureExternCallOk` to dispatches through `id` specifically.

**Plain-English intuition.**

> If my impure extern produces a trusted-guarded cell in the output,
> there was already a trusted-guarded cell at the same location in the
> input. Impure externs do not conjure new guards while pc is poisoned.

**Discussion.** Same semantic content as the current axiom, narrowed to
a specific id. Vacuous for `.val` and `.pfn` because only `.fn`
triggers the FR `ImpureExternCallOk` path.

### Contract C — Extern Fn Frame

**Status:** 🟡 **Proposed (new).** Keystone of the semantics-side
story.

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

**Status:** 🟡 **Proposed (new).** Surgical; consumed at a single
proof site.

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

**Status:** 🟡 **Proposed (new).** Narrow: only ref-typed `.val`
registrations.

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

```lean
-- Before (global axiom):
theorem FaultRobustness_step ... := by
  ...
  have := externGuardProvenance ctx r hcall hpc l k qt hout
  ...

-- After (evidence registry):
theorem FaultRobustness_step (tr : TrustedRegistry) ... := by
  ...
  have hev := tr.evidence id impl hreg
  have := hev.guardProvenance ctx r hcallId hpc l k qt hout
  ...
```

Top-level theorems — `TypeSystemEnforcesFaultRobustness` and
companions — gain a `tr : TrustedRegistry` parameter and thread it to
whichever `StepFR*` modules need it. Pure-Poison steps are unaffected;
`tr` is carried but never destructured.

## Migration plan for Contracts A and B

Both live today as admitted axioms and have call sites spread across
`LeanProofs/`. Moving them into the evidence bundle is a structural
refactor, not a semantic change:

1. Introduce `TrustedRegistry` and `ExternEvidence` in
   `LeanProofs/ExternAxioms.lean` (or a sibling file).
2. Re-derive the current universal axiom statements from the bundle
   fields as *theorems* (trivial once `tr` is in scope):

   ```lean
   theorem externTagSoundness_of_registry
       (tr : TrustedRegistry) ... :
       -- same conclusion as the old axiom
       ... :=
     (tr.evidence id impl hreg).tagSoundness ...
   ```

3. Thread `tr` through the top-level FR theorems and intermediate
   lemmas that reach extern sites.
4. Retire the original `axiom` declarations. At that point
   `ExternAxioms.lean` contains **zero** `axiom` declarations — only
   structure definitions, `Contract_*` predicates, and helper lemmas.

Step 4 is the concrete axiom-hygiene payoff: the file that today admits
two live axioms becomes axiom-free.

## Sorries discharged

| `sorry` location | Evidence fields consumed | Notes |
|------------------|--------------------------|-------|
| `SemanticsProperties.lean` — `app` fn-case `wfConfig` preservation | `frame` (C), `addrMono` (D) | C gives `wfMem addr' mem'` via frame + int-only heap; D gives `wfVarEnv addr' cfg.varEnv` via monotonicity. |
| `SemanticsProperties.lean` — `externVal` `ref int` `wfConfig` preservation | `refInBounds` (E) + proven `nextAddr` monotonicity | E at init, monotonicity transports to intermediate `cfg`. |
| `FaultRobustnessProofs.lean` — `terminatesTo_extern_absurd` × 6 | `tagSoundness` (A), `refInBounds` (E) | Six FR obligations at extern *declaration* sites (three in the masked single-run theorem, three in the step theorem, one per extern form). A covers tag-mapping coherence for the declared predicates in all three forms. E covers the `ref int` subcase of `externVal`, where the registered runtime `.val (.loc a)` must lie below `nextAddr`. Contracts B and C are *not* consumed here because declarations do not invoke dispatch; they are consumed inside `StepFRApp` at the application of extern closures. |

Other extern-related `sorry`s concern top-level extern *declarations*
(which leave `Config` unchanged) and close mechanically without any
evidence.

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

One unified per-extern evidence model. Five contracts:

| # | Name | Status | Impl kinds | Consumed at |
|---|------|--------|------------|-------------|
| A | Tag Mapping Soundness | ✅ admitted (to migrate) | all | extern-decl typechecking |
| B | Impure Extern Guard Provenance | ✅ admitted (to migrate) | `.fn` | StepFR App fn-case |
| C | Extern Fn Frame | 🟡 proposed | `.fn` | `wfConfig` preservation + FR |
| D | Extern Fn Address Monotonicity | 🟡 proposed | `.fn` | `wfConfig` preservation |
| E | Registered Ref-Typed Extern Val In Bounds | 🟡 proposed | `.val (.loc _)` at `ref int` | `externVal` preservation + FR declaration sites |

Contracts A and B already exist as universally-quantified axioms and
are consumed by the current proof development; migrating them into the
evidence bundle is structural. Contracts C, D, and E are new and close
the three pending extern-related `sorry`s.

End state: `ExternAxioms.lean` contains zero `axiom` declarations —
only the `TrustedRegistry` / `ExternEvidence` structures,
`Contract_{A,B,C,D,E}` predicate definitions, and derived
compatibility theorems restating the old universal axiom forms from
the bundle. The top-level FR theorem becomes
evidence-parameterised:

```lean
theorem TypeSystemEnforcesFaultRobustness
    (tr : TrustedRegistry) (cfg₀ : Config)
    (hreg : cfg₀.registry = tr.reg) ... :
  ... FR conclusion ...
```

Concrete drivers (e.g. `Main.lean`) supply a `TrustedRegistry` with
concrete proofs; abstract reasoning and separate-compilation scenarios
supply hypothetical registries to prove component FR independently.
