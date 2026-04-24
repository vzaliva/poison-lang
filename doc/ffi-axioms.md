# FFI Axioms: Per-Extern Evidence Registry

Status: design document, companion to `doc/ffi-proposal.md`.

This document proposes a unified per-extern evidence model for all FFI
contracts: the driver supplies, for each registered extern, a bundle of
proofs witnessing the contracts that extern needs to satisfy. The bundle
is a runtime input to the fault-robustness proof — not a set of global
axioms admitted once and for all.

Two of the six contracts below (**A**, **B**) are already admitted as
universally-quantified axioms in `LeanProofs/ExternAxioms.lean` and are
used by the current proof development. The remaining four (**C**,
**D**, **E**, **F**) are proposed new contracts needed to close the
pending extern-related `sorry`s and to state fault-robustness for
executable externs. Under this proposal, **all six migrate into
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

## Open issues from independent review (2026-04-23)

An independent review surfaced twenty-two structural gaps across three
rounds. Each is tracked below and cross-referenced from the affected
contract section. Items marked **Blocking** change contract
statements; **High** items require additional content or formulation
changes.

**Round 1 (R1–R7)**: evidence-registry shape, uninhabitability of A,
missing ids on type-level closures, adequacy of C/D/E, level mismatch
of `resolveEffects`, weakness of E, missing declaration environment.

**Round 2 (R8–R14)**: F is not aligned with FR's actual two-run shape;
F's declaration lookup invents a nonexistent `Typ.arrow` flavour; E
models the wrong logical location; E is missing a relational agreement
clause; C lacks a runtime-instantiation preservation clause; the
migration plan for A misrepresents the old axiom as rederivable; stale
counts and field names still point implementers at the old evidence
shape.

**Round 3 (R15–R22)**: F still conflates the two runs' input cursors;
F's effect-memory agreement is too permissive for post-clean effect
cells; the DeclEnv is defined but not actually threaded into
contracts; `ProgramDeclsMatch` is ill-grounded against `TypeContext` /
`Config`; F's `cleanInputAgreement` lacks a `VarTypeEnv` to interpret
env bindings; E's E4 clean-condition is too narrow vs. the FR
`qtypCleanUnder R qt` notion; the extern-closure representation gap
is actually a prerequisite, not a follow-up; a small syntactic mistake
in E's memory-value form.

- **R1 — Blocking: Contract A is uninhabitable as stated.**
  `∀ tm, TagMappingRespectsTagMeaning tm mapping preds env` is false
  whenever `mapping` contains an entry for a `guardClosure` but `tm`
  (possibly empty) does not map the allocated tag to the expected
  guard descriptor. The fix is to change the theorem shape so extern
  tag allocation *provides or extends* a compatible `TagMeaning`,
  rather than asking a driver to prove compatibility with every
  possible `tm`. The present `axiom externTagSoundness` in
  `LeanProofs/ExternAxioms.lean` inherits this issue. See Contract A
  below for the revised formulation.

- **R2 — Blocking: id-indexed evidence cannot be recovered at
  current type-level call sites.** `FnTClosure.extern` and
  `PFnTClosure.extern` (`LeanPoison/Syntax.lean:440`) do not carry
  `ExternId`, and `applyFnTClosure` drops nested ids when creating
  inner extern closures (`LeanPoison/Typecheck.lean:1349`). The
  contract-statements that reference `ImpureExternCallOkForId id`,
  `DeclaredPredsFor id`, `DeclaredEffectsFor id`, and `DeclaredTypeFor
  id` therefore cannot be consumed at their intended call sites
  without a prerequisite syntax change (propagate ids into the
  type-level closure representation) or a re-indexing of evidence by
  closure summary rather than by id.

- **R3 — Blocking: C/D/E alone are not sufficient for FR of
  executable externs.** `pfn` and `fn` impls receive the full
  `VarEnv` and `Memory` as read-only inputs (`LeanPoison/
  Runtime.lean:80`). An impl that returns a syntactically clean value
  can still leak poisoned input data into the returned value or into
  memory it is allowed to write. FR requires a **relational**
  per-call contract: *clean-equivalent* inputs must yield
  *clean-equivalent* outputs, in accordance with the declared return
  and effects summary. This is added below as **Contract F — Poison
  Non-Leakage**.

- **R4 — High: Contract C does not imply `wfConfig` preservation on
  its own.** The frame statement covers *pre-existing* addresses
  outside the effects set; it says nothing about addresses inserted
  by the impl that lie outside `[addr₀, addr')`. `wfConfig` requires
  *every* post-memory key to be `< nextAddr`. An impl could insert at
  `addr' + 100` and still satisfy C and D. Fix: add a **domain
  bound** clause to Contract C — every key in `mem'` is either an
  allowed old/effect key (i.e. present in `m₀` or in
  `resolveEffects`) or lies in `[addr₀, addr')`.

- **R5 — High: `resolveEffects` is stated at the wrong level.**
  Typing-side effects update logical `LocSet`s drawn from
  `VarTypeEnv` (`LeanPoison/Typecheck.lean:1278`). The present
  formulation of `resolveEffects` takes a `VarEnv` and produces
  runtime `Address`es directly, which bypasses the realisation map
  `θ` that FR uses to bridge type-level locations to runtime
  addresses. Contract C should be stated in logical/type-level terms
  and bridged via `θ` so the runtime frame lines up with the
  typing-side invalidation used by FR.

- **R6 — High: Contract E's bound is too weak for `ref int` extern
  vals.** `a < cfg.nextAddr` (`doc/ffi-axioms.md`) is enough for
  `wfValue`, but FR/type safety for refs also requires a realisation
  witness `θ.lookup l = some a` (`LeanProofs/TypeSafety.lean:912`)
  and actual memory presence (`LeanProofs/TypeSafety.lean:944`). E
  should be an initial-state ref-realisation contract: the registered
  `Value.loc a` is witnessed by a type-level location `l` in the
  initial memory environment, with `θ` mapping `l ↦ a` and
  `cfg₀.memory` containing an integer at `a`.

- **R7 — High: `TrustedRegistry` lacks a real declaration table.**
  The list-shaped declarations currently store only `id` and
  evidence. Contracts A, C, E invoke `DeclaredPredsFor id`,
  `DeclaredEffectsFor id`, `DeclaredTypeFor id` — all of which
  require an actual declaration environment. The `hcover`
  side-condition only proves id agreement, not kind/type/effects/
  return-summary agreement between the program AST, the runtime
  registry, and the evidence table. Fix: promote
  `TrustedRegistry` to carry an explicit declaration environment
  (kind, declared type, declared effects, declared predicates per
  id) and prove three-way consistency: AST ↔ registry ↔ evidence.

- **R8 — Blocking: Contract F is not aligned with FR's actual
  two-run shape.** The previous F used a single `μ` and single `θ`,
  but FR's `agreeValueUnder` is relational over two memories *and*
  two realisation maps (`LeanProofs/FaultRobustness.lean:445`). F
  also omitted `predSat` and the regime. F must be restated in
  StepFR shape: `predSat`, `regime`, `μ₀ μ₁`, `θ₀ θ₁`, and
  post-state agreement. Revised form appears in Contract F below.

- **R9 — Blocking: Contract F's declaration lookup shape is
  invalid.** The prior sketch wrote `DeclaredTypeFor id = some
  (.arrow argTyp retTyp effs)`, but `DeclaredTypeFor` returns
  `Option Typ` and `Typ.arrow` has no effects-or-QTyps flavour
  (extern callables are represented differently in the AST). For
  extern callables the contract must consume declaration fields
  (`argTyp : Typ`, `retSpec : ExternReturn`, `effects`) directly
  from `ExternDeclaration`, plus the call-site `TypeResult` /
  computed QTyp, not a synthesised arrow type.

- **R10 — Blocking: Contract E models the wrong logical location.**
  `memEnv₀.lookup l = some { etyp := .ref .int, .. }` is ill-formed:
  `MemoryTypeEnv.lookup` returns *cell contents*, and memory cells
  are always `ETyp.int`. The `ref` type lives in the *extern value's
  result QTyp* whose `ETyp.ref` contains a fresh logical location
  `l`. E must connect the typechecking result's allocated ref loc
  to `Value.loc a`, not require a memory cell whose type is itself
  `ref int`.

- **R11 — Blocking: extern ref values need a relational agreement
  obligation.** E as stated proves address realisation and memory
  presence for a single run. But if a clean extern val `@id : ref
  int` exposes a reference, post-`agreeOnClean` for the newly
  introduced logical location also needs the two runs' heap contents
  at the realised address to agree. Otherwise a "clean" ref can
  expose divergent external heap contents while still satisfying E.
  E needs a second clause bounding two-run divergence at registered
  ref addresses.

- **R12 — High: Contract C does not preserve runtime instantiation
  for effect cells.** The frame/domain clauses in C allow an impl to
  *delete* an effect-frame address entirely. `wfConfig` may still
  hold, but `runtimeInstantiatesCtx` requires every typed logical
  location realised by θ to have a runtime memory cell
  (`LeanProofs/TypeSafety.lean:944`). C needs an additional
  post-presence clause: every logical location retained or newly
  bound in the post `memEnv` has a corresponding populated runtime
  cell.

- **R13 — High: Migration plan for Contract A is still misleading.**
  The plan says to rederive the old universal axiom's "same
  conclusion" — but R1 already established that conclusion is false.
  The plan must instead say consumers are rewritten to take the
  extended `tm'` witness produced by A1/A2, with matching transport
  through `PredSatLaws` and `wfTagMeaningCtx` at the call sites that
  currently consume `externTagSoundness`.

- **R14 — High: Stale counts and field names remain.** Multiple
  passages still refer to "five contracts" / "three new contracts";
  the sorries-discharged table still names `implEv.refInBounds`
  instead of the new `implEv.refInit`. These are now more than
  wording issues because they point implementers at the old evidence
  shape.

- **R15 — Blocking: Contract F conflates the two runs' input
  cursors.** The previous draft required both runs to call `f` with
  the same `addr₀`. StepFR quantifies *two independent* runtime
  configs and address cursors — extern calls start from `addr₀` and
  `addr₁` independently. F must quantify separate input cursors and
  relate outputs under post-state agreement, not force a shared
  cursor.

- **R16 — Blocking: F's effect-memory agreement is too permissive.**
  "Cells in the effect frame may differ" is too strong. Effects can
  write *clean* cells: `applyExternEffect` stores `joinPoison pc
  effect.poison`, so under clean `pc` and clean effect poison the
  post cell is clean. F must require agreement for post-clean effect
  cells; only post-dirty cells may differ.

- **R17 — Blocking: `DeclEnv` is defined but not threaded into
  contracts.** The document defines `DeclaredPredsFor (Δ : DeclEnv)`
  etc. but the contracts still write `DeclaredPredsFor id`,
  `DeclaredEffectsFor id`, and `IsImpureExternDeclaration id`
  without `Δ`. Fix: make every contract take `d : ExternDeclaration`
  directly (evidence indexed by declaration, not bare id), or thread
  `Δ` as an explicit parameter. Indexing by `ExternDeclaration` is
  simpler and matches how Contract F already reads `d.effects` /
  `d.retSpec` / `d.kind`.

- **R18 — Blocking: `ProgramDeclsMatch ctx declEnv` is not grounded
  in the current objects.** `TypeContext` does not contain the
  program AST; neither does `Config`, so `programOf cfg₀` does not
  exist. The consistency premise should be against the expression
  `e` being typechecked: `ProgramDeclsMatch e tr.declEnv`, where
  `e : Expr` is the top-level program input to FR.

- **R19 — High: F's `cleanInputAgreement` lacks variable typing
  context.** Captured runtime environment agreement needs the
  corresponding `VarTypeEnv` (or `CapturedVarEnv`) to interpret
  which bindings and types line up; `MemoryTypeEnv` alone is not
  enough. F must thread a `ρ : VarTypeEnv` to give
  `agreeVarEnvUnder` its type context.

- **R20 — High: E4's clean-condition is too narrow.** `IsCleanAtRegistration d`
  omits predicate-guarded clean cells: FR cleanness is
  `qtypCleanUnder R qt`, which includes guard-depoisoned values
  when the regime maps the tag to true. Predicate-guarded extern
  refs are *not* automatically FR-irrelevant. E4 should be
  conditional on `qtypCleanUnder R tcRes.qualType` at the
  typechecking-result QTyp, not on `IsCleanAtRegistration d` alone.

- **R21 — High: The extern-closure representation gap is a
  prerequisite, not a follow-up.** `valueHasETyp`,
  `deepValueQTypProperty`, and `agreeValueUnder` currently match
  `FnTClosure.regular` only. Contract F cannot establish clean
  agreement for returned extern callables (nested or top-level)
  until these constructors — or equivalent evidence threaded
  through Contract A — are part of the design. Promote this gap
  from "follow-up" to "prerequisite refactor" alongside R2 and R7.

- **R22 — High: Contract E uses invalid memory-value syntax.**
  `cfg.memory.lookup a = some (.int n)` is wrong: runtime `Memory`
  is `Address → Int` (or `Address → Option Int`), so the matching
  form is `cfg.memory.lookup a = some n`. Small but affects the
  formal statement.

Further redesign needed before the contracts below can be
instantiated in Lean. The sections below have been updated *where the
fix is a formulation change*; where the fix requires a syntax/typing
refactor (R2, R5, R7, R21), the current formulation is left as a
sketch with the dependency flagged.

**R17-driven reindexing.** Under R17, every contract is reindexed by
`d : ExternDeclaration` rather than by bare `ExternId`. Evidence
fields accept `d` as their primary parameter; the evidence bundle
itself is parametrised by `d`; lookups like `DeclaredPredsFor` are
replaced by direct field accesses `d.preds`, `d.effects`,
`d.retSpec`, `d.kind`. This dispenses with the `DeclaredPredsFor Δ id`
threading entirely.

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
the same evidence bundle as the four new contracts (C, D, E, F).

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
    registration status.  Indexed by the declaration itself (R17),
    so fields can read `d.preds`, `d.kind`, etc. directly. -/
structure ExternDeclarationEvidence (d : ExternDeclaration) : Prop where
  -- Contract A: tag-mapping coherence (all declaration kinds)
  tagSoundness    : Contract_A d
  -- Contract B: impure guard provenance (impure declarations only;
  --              `True` otherwise)
  guardProvenance : Contract_B d
```

### Implementation-layer: registered-impl evidence

```lean
/-- Implementation-layer evidence: properties of a registered runtime
    implementation, paired with its declaration so fields can read
    declared effects/ret-spec/kind directly (R17).  Required only
    when an impl is present in the registry; fields that do not
    apply to a given impl kind reduce to `True`. -/
structure ExternImplEvidence
    (d : ExternDeclaration) (impl : ExternImpl) : Prop where
  -- Contract C: fn frame (.fn only; True otherwise)
  frame           : Contract_C d impl
  -- Contract D: fn address monotonicity (.fn only; True otherwise)
  addrMono        : Contract_D d impl
  -- Contract E: ref-val init realisation + bound
  --             (.val (.loc _) at ref int only; True otherwise)
  refInit         : Contract_E id impl
  -- Contract F: fn/pfn poison non-leakage (relational, R3)
  nonLeakage      : Contract_F id impl
```

### Declaration environment (addresses R7)

Contracts A, B, C, E, F all reference the declared shape of an
extern: predicates, impureness, type, effects, return summary. These
cannot be looked up from `id` alone — `TrustedRegistry` must carry
an explicit **declaration environment** that pairs each id with its
AST-supplied declaration shape, and prove three-way consistency with
the program AST and the runtime registry.

```lean
/-- The AST-visible shape of an extern declaration, captured as a
    structure so the evidence layer can destructure it. Concrete
    fields mirror the `externVal` / `externFn` / `externPfn` AST
    constructors. -/
structure ExternDeclaration where
  id      : ExternId
  kind    : ExternKind            -- .val | .fn | .pfn
  typ     : Typ
  preds   : List SyntaxPredicate  -- empty for externVal unless guarded
  effects : List Effect           -- non-empty only for externFn
  retSpec : Option ExternReturn   -- non-trivial for externFn/externPfn

/-- Declaration environment: one entry per extern id mentioned in
    the program AST. -/
abbrev DeclEnv := Std.HashMap ExternId ExternDeclaration
```

Contracts read declaration fields directly from `d : ExternDeclaration`
(R17): `d.preds`, `d.effects`, `d.retSpec`, `d.kind`. The earlier
`DeclaredPredsFor Δ id` helper family is therefore unnecessary and
has been removed.

### The combined trusted registry

```lean
/-- Trusted registry (R7-aware, R17-reindexed, R18-corrected).
    Carries an explicit declaration environment, typing-layer
    evidence per declaration, implementation-layer evidence per
    registered impl, and program-consistency premises against the
    expression being typechecked (not against TypeContext or
    Config). -/
structure TrustedRegistry (e : Expr) where
  -- Declaration environment: every extern id in the program AST.
  declEnv : DeclEnv
  -- Typing-layer: one bundle per declared id, indexed by the
  -- declaration itself (R17).
  declEv  : ∀ id d, declEnv.get? id = some d →
              ExternDeclarationEvidence d
  -- Runtime implementations: one per registered id.
  reg     : ExternRegistry
  -- Implementation-layer: indexed by (d, impl) rather than (id, impl).
  implEv  : ∀ id d impl,
              declEnv.get? id = some d →
              reg.get? id = some impl →
              ExternImplEvidence d impl
  -- Three-way consistency:
  -- C1: every registered impl has a matching declaration entry.
  hCover      : ∀ id impl, reg.get? id = some impl →
                  ∃ d, declEnv.get? id = some d
  -- C2: registered impl kind matches declared kind.
  hKindAgree  : ∀ id impl d,
                  reg.get? id = some impl →
                  declEnv.get? id = some d →
                  implKind impl = d.kind
  -- C3: `declEnv` agrees with the program `e` being typechecked
  --     (R18): every extern declaration node inside `e` appears in
  --     declEnv with the same shape.
  hProgramConsistent : ProgramDeclsMatch e declEnv
```

`ProgramDeclsMatch e declEnv` walks the expression `e` and checks
that every extern-declaration subterm (`externVal id ...`,
`externFn id ...`, `externPfn id ...`) has a corresponding entry in
`declEnv` whose fields agree with the AST. `e` — the program
expression — is where the declarations actually live; neither
`TypeContext` nor `Config` carries the program AST (R18), so the
premise is phrased against `e`.

Equivalent list-shaped view (what the driver actually writes):

```lean
structure TrustedExternDeclaration where
  decl     : ExternDeclaration
  evidence : ExternDeclarationEvidence decl

structure TrustedExternImpl where
  decl     : ExternDeclaration
  impl     : ExternImpl
  evidence : ExternImplEvidence decl impl

def TrustedRegistry.ofLists (e : Expr)
    (decls : List TrustedExternDeclaration)
    (impls : List TrustedExternImpl)
    (huniqDecls : decls.Pairwise (fun a b => a.decl.id ≠ b.decl.id))
    (huniqImpls : impls.Pairwise (fun a b => a.decl.id ≠ b.decl.id))
    (hCover     : ∀ x ∈ impls, ∃ d ∈ decls, d.decl.id = x.decl.id)
    (hKindAgree : ∀ x ∈ impls, implKind x.impl = x.decl.kind)
    (hProgramConsistent : ProgramDeclsMatch e decls) :
    TrustedRegistry e := ...
```

FR-level theorems take `(tr : TrustedRegistry e)` where `e` is the
expression being typechecked, and destructure the appropriate layer
on demand: `tr.declEv id d hEntry` at extern-declaration typechecking
sites, and `tr.implEv id d impl hDecl hReg` at runtime dispatch
sites. Non-extern proof sites are unaffected.

## Contracts

### Contract A — Tag Mapping Soundness

**Layer:** typing (declaration-scoped).
**Status:** ⚠️ **Affected by review findings R1 (Blocking,
uninhabitability), R7 (declaration environment — resolved by
indexing on `d : ExternDeclaration` per R17).**

Lives today as `axiom externTagSoundness` in
`LeanProofs/ExternAxioms.lean`. Consumed by the current proof
development at extern-declaration typechecking sites. Under this
proposal, restated as a per-declaration field in
`ExternDeclarationEvidence` — but the current statement (both the
admitted axiom and the prior per-declaration form) is uninhabitable:
an empty `TagMeaning` paired with a non-empty `guardClosure` mapping
contradicts the conclusion.

**Current admitted form (live, but uninhabitable as stated — R1):**

```lean
-- LeanProofs/ExternAxioms.lean (existing, live axiom; R1 applies)
axiom externTagSoundness
  (tm : TagMeaning)
  (mapping : TagMapping)
  (preds : List SyntaxPredicate) (env : VarTypeEnv)
  (nextTag nextTag' : Tag)
  (halloc : collectAndAllocExternTags preds nextTag
              = .ok (mapping, nextTag')) :
  TagMappingRespectsTagMeaning tm mapping preds env
```

**Revised per-declaration form (addresses R1, R17):**

The fix is to change allocation from *requiring* compatibility with
every `tm` to *providing* a `tm` (or an extension of an ambient one)
that is compatible with the allocated mapping. Indexed by
`d : ExternDeclaration`, the predicates come straight from `d.preds`.

```lean
-- Form A1: allocation extends any ambient tm to a compatible one.
def Contract_A (d : ExternDeclaration) : Prop :=
  ∀ (env : VarTypeEnv)
    (tm : TagMeaning) (mapping : TagMapping)
    (nextTag nextTag' : Tag),
    FreshFrom tm nextTag →
    collectAndAllocExternTags d.preds nextTag
      = .ok (mapping, nextTag') →
    ∃ tm',
      TagMeaning.Extends tm tm' ∧
      TagMappingRespectsTagMeaning tm' mapping d.preds env
```

```lean
-- Form A2: allocation returns its own compatible tm (cleaner, but
--          requires threading tm through typechecking output).
def Contract_A (d : ExternDeclaration) : Prop :=
  ∀ (env : VarTypeEnv)
    (mapping : TagMapping)
    (nextTag nextTag' : Tag),
    collectAndAllocExternTags d.preds nextTag
      = .ok (mapping, nextTag') →
    ∃ tm, TagMappingRespectsTagMeaning tm mapping d.preds env
```

Form A1 keeps the "ambient tm" threading the existing proof
development expects but adds an `Extends` extension witness. Form A2
is cleaner but requires that allocation return a tm alongside the
mapping, which is a shape change to `collectAndAllocExternTags`.

**Plain-English intuition.**

> Whatever predicates my extern declaration names, fresh-tag
> allocation can be paired with a tag meaning that honours them. In
> other words, allocating extern tags *chooses* or *provides* a
> compatible `TagMeaning` — it does not ask the surrounding context to
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
**Status:** ✅ **Already admitted and used.** ⚠️ Affected by review
finding R2 (ids missing from `FnTClosure.extern`) at the consumption
site: `ImpureExternCallOkFor d ctx r` cannot be formulated without
ids on type-level closures.

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

**Proposed per-declaration form (R17-reindexed):**

```lean
def Contract_B (d : ExternDeclaration) : Prop :=
  d.kind = .fn →
  ∀ (ctx : TypeContext) (r : TypeResult),
    ImpureExternCallOkFor d ctx r →
    ctx.pc = true →
    ∀ l k qt_out,
      trustedGuardedCell r.memEnv' r.regime' l k qt_out →
      ∃ qt_in, trustedGuardedCell ctx.memEnv ctx.regime l k qt_in
```

The hypothesis `d.kind = .fn` makes the claim vacuous for `externVal`
and `externPfn` declarations. `ImpureExternCallOkFor d ctx r` refines
the existing `ImpureExternCallOk` to calls whose typing dispatches
through `d` specifically (consuming the id-on-closure refactor from
R2).

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
**Status:** 🟡 **Proposed (new).** ⚠️ **Affected by review findings
R4 (domain bound), R5 (level mismatch), R12 (runtime-instantiation
preservation).** The revised form below incorporates all three
fixes.

A claim about how the driver-supplied `fn` impl behaves at runtime —
not required when no impl is registered.

**Revised per-extern form (addresses R4, R5, R12):**

```lean
/-- Logical (type-level) effect set: a set of `Loc`s drawn from
    `VarTypeEnv` describing which memory-typed cells the impl is
    permitted to disturb.  This is the *type-level* shape typing
    already reasons about; see `LeanPoison/Typecheck.lean` line 1278
    for the `LocSet`-style update performed on effects. -/
def resolveEffectsLogical (effs : List Effect)
    (ctx : TypeContext) (argTyp : QTyp) : LocSet := ...

/-- Runtime address-level image of a logical effect set under a
    realisation map θ bridging type-level locations to concrete
    addresses. -/
def resolveEffectsRuntime (ls : LocSet) (θ : RealizationMap)
    : Set Address :=
  { a | ∃ l ∈ ls, θ.lookup l = some a }

def Contract_C (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn f =>
      d.kind = .fn →
      ∀ (ctx ctx' : TypeContext)
        (argTyp : QTyp) (θ θ' : RealizationMap)
        (memEnv' : MemoryTypeEnv),
        let ls    := resolveEffectsLogical d.effects ctx argTyp
        let frame := resolveEffectsRuntime ls θ
        ∀ {env : VarEnv} {arg v : Value}
          {m₀ mem' : Memory} {addr₀ addr' : Address},
          f env arg m₀ addr₀ = .ok (v, mem', addr') →
          -- Suppose typing models the call's post-state as
          -- `(ctx', memEnv', θ')`.
          TypingModelsFnCall d ctx ctx' argTyp memEnv' θ θ' →
          -- C1 — Frame: pre-existing cells outside the effect
          --             frame are unchanged.
          (∀ a, a < addr₀ → a ∉ frame → mem'.lookup a = m₀.lookup a)
          ∧
          -- C2 — Domain bound (R4): every key in mem' is either a
          --             pre-existing/effect-frame key or lies in
          --             the fresh range [addr₀, addr').
          (∀ a, mem'.lookup a ≠ none →
                 (m₀.lookup a ≠ none ∨ a ∈ frame ∨
                  (addr₀ ≤ a ∧ a < addr')))
          ∧
          -- C3 — Runtime-instantiation preservation (R12): every
          --      logical location typed in memEnv' and realised by
          --      θ' to a concrete address has a populated runtime
          --      cell in mem'.  An effect-framed cell may change
          --      *contents* but must not be deleted.
          (∀ l a, memEnv'.lookup l ≠ none → θ'.lookup l = some a →
                  mem'.lookup a ≠ none)
  | _     => True
```

`TypingModelsFnCall d ctx ctx' argTyp memEnv' θ θ'` packages the
hypothesis that typing's view of the post-state (`ctx'`, `memEnv'`,
`θ'`) corresponds to the runtime execution — the same correspondence
StepFR already relies on for other operators. C3 then ties the
typing view to the runtime heap.

**Plain-English intuition.**

> An extern `fn` only writes to cells named in its declared `effects`
> clause (via their type-level `Loc`s realised by θ), plus any it
> allocated during the call. Every other pre-existing cell is
> bit-identical before and after, and no cell appears in `mem'` at an
> address outside that combined region.

**Discussion.** Without this contract, `effects` is a typing decoration
with no runtime teeth. With it:

- **`wfMem` preservation follows.** Under the domain-bound clause
  (C2), every key in `mem'` is within `addr'` whenever (a) pre-existing
  keys were within `addr₀ ≤ addr'`, (b) effect-frame keys were within
  `addr₀`, and (c) fresh keys are below `addr'` by construction. C1
  alone was insufficient (R4): it did not forbid an impl from inserting
  at `addr' + 100`.
- **FR carries cleanness and guards across extern calls.** The
  logical frame aligns with type-level invalidation: cells whose `Loc`s
  are outside `ls` keep their pre-call guards and cleanness because
  their realised addresses are outside `frame`. This is the bridge
  through `θ` that R5 requires.
- **The driver burden is natural.** Drivers typically know *what they
  wrote* and *where they allocated*; proving C1 + C2 is usually
  easier than proving a global `wfMem` claim.

Open formalisation points:

- `resolveEffectsLogical` and `LocSet` need concrete definitions.
  The typing-side effect propagation (`Typecheck.lean:1278`) already
  manipulates a logical effect-update structure; that structure is
  the natural source.
- `resolveEffectsRuntime` depends on `θ`. FR always has a `θ` in
  scope at extern call sites (it is the realisation map witnessing
  `consistentWithRegime`), so this is available at consumption time.
- `d.effects` / `d.retSpec` / `d.kind` read directly from the
  declaration bundle (R17); no separate `DeclaredEffectsFor`
  helper is needed.

### Contract D — Extern Fn Address Monotonicity

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new).** Surgical; consumed at a single
proof site. A claim about how the driver-supplied `fn` impl behaves at
runtime.

**Per-extern form (R17-reindexed):**

```lean
def Contract_D (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn f =>
      d.kind = .fn →
      ∀ {env : VarEnv} {arg v : Value}
        {m₀ mem' : Memory} {addr₀ addr' : Address},
        f env arg m₀ addr₀ = .ok (v, mem', addr') →
        addr₀ ≤ addr'
  | _     => True
```

D does not use any field of `d` beyond the kind guard (the claim is
purely operational about `f`'s output cursor). Indexing by `d` keeps
the evidence-bundle shape uniform — all impl-layer contracts take
`(d, impl)` — so `ExternImplEvidence d impl` destructures cleanly.

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

### Contract E — Registered Ref-Typed Extern Val: Realisation and Two-Run Agreement

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new).** ⚠️ **Affected by review findings
R6 (bound too weak), R10 (wrong logical location in prior draft),
R11 (missing two-run agreement).** The revised form below pins the
fresh logical `Loc` that *extern-val typechecking* allocates in its
result QTyp to the driver-registered `Value.loc a`, adds runtime
presence, and adds a relational cross-run clause so two runs cannot
expose divergent heap contents through the same registered ref.

Narrow: only ref-typed `.val` registrations. The typechecker for
`externVal @id : ref int` produces a `TypeResult` whose result-QTyp
is of the shape `QTyp.mk (ETyp.ref l) poison pred` for a freshly
allocated logical location `l : Loc` (the `l` lives in the result's
etyp, not in `MemoryTypeEnv` cell contents, which are always
`ETyp.int`). Contract E relates that `l` to the runtime `Value.loc
a` the registry supplies.

**Revised per-extern form (addresses R6, R10, R11, R17, R20, R22):**

```lean
def Contract_E (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  match impl with
  | .val (.loc a) =>
      -- Only ref-typed externVal declarations are in scope.
      d.kind = .val → d.typ = Typ.ref .int →
      ∀ (tcRes : TypeResult) (l : Loc),
        -- tcRes is what typechecking produced for this declaration;
        -- l is the fresh Loc in tcRes.qualType.etyp.
        ExternValTypecheckResult d tcRes l →
        -- Two runs of the same program with the same registry.
        ∀ (cfg₀ cfg₁ : Config)
          (μ₀ μ₁ : MemoryTypeEnv) (θ₀ θ₁ : RealizationMap) (R : Regime),
          InitialConfigPair d cfg₀ cfg₁ μ₀ μ₁ θ₀ θ₁ R →
          cfg₀.registry.get? d.id = some (.val (.loc a)) →
          cfg₁.registry.get? d.id = some (.val (.loc a)) →
          -- E1 — θ realises l to a in both runs.
          (θ₀.lookup l = some a ∧ θ₁.lookup l = some a)
          ∧
          -- E2 — Runtime bound in both runs.
          (a < cfg₀.nextAddr ∧ a < cfg₁.nextAddr)
          ∧
          -- E3 — Runtime instantiation: cell at a is populated with
          --      an integer in both runs.  (R22: Memory is Address →
          --      Option Int, so the matching form is `some n`, not
          --      `some (.int n)`.)
          (∃ n₀ : Int, cfg₀.memory.lookup a = some n₀)
          ∧
          (∃ n₁ : Int, cfg₁.memory.lookup a = some n₁)
          ∧
          -- E4 — Two-run agreement on heap contents at a, conditioned
          --      on FR's own cleanness notion (R20): the result QTyp
          --      is qtypCleanUnder R at the initial regime. This
          --      covers predicate-guarded cells that become clean
          --      under the regime's guard-tag mapping.
          (qtypCleanUnder R tcRes.qualType →
             ∃ n : Int,
               cfg₀.memory.lookup a = some n
               ∧ cfg₁.memory.lookup a = some n)
  | _             => True
```

The auxiliary predicates:

- `ExternValTypecheckResult d tcRes l` says `tcRes` is the result
  typechecking produces for declaration `d`, and `l` is the fresh
  `Loc` inside `tcRes.qualType.etyp` when that `etyp` is `ETyp.ref l`.
- `InitialConfigPair d cfg₀ cfg₁ μ₀ μ₁ θ₀ θ₁ R` asserts both
  configurations are initial and well-formed with respect to their
  respective `μᵢ`, `θᵢ`, and the regime `R`, with the declaration
  `d` consistent in both.
- `qtypCleanUnder R qt` is the existing FR cleanness predicate from
  `LeanProofs/FaultRobustness.lean` — it accounts for guard-depoisoned
  values when the regime maps the tag to `true`. The prior condition
  `IsCleanAtRegistration d` (R20) was too narrow: it missed
  predicate-guarded cells. Using `qtypCleanUnder` captures every
  case FR itself regards as clean.
  declaration `d` is declared with `poison = false` and with a
  predicate that is trivially satisfied at the driver-supplied
  initial state (so FR regards this registered cell as clean).

**Plain-English intuition.**

> Any reference the driver registers at type `ref int` is grounded
> both in the typing environment and in the runtime heap: the fresh
> logical `Loc` that the typechecker allocates in the extern-val
> result is mapped by `θ` to the registered address, the address is
> in bounds, and the cell holds an integer. Across two runs sharing
> the same registry, the logical and runtime bindings match; and if
> the declaration promises a clean ref, the two heaps actually agree
> on that cell.

**Discussion.** The reviewer's R10 / R11 points were load-bearing:

- **R10**: the previous draft looked up `l` in `MemoryTypeEnv` and
  asked for a cell of type `ref int`. That is ill-typed —
  `MemoryTypeEnv` stores cell contents, always `ETyp.int`. The
  `ref`-ness lives in the *TypeResult's `qualType.etyp`* for the
  extern-val expression, where the typechecker allocates the fresh
  `Loc`. The revised form extracts `l` from there and connects it
  to `Value.loc a` via `θ`.
- **R11**: without a cross-run clause, a "clean" extern ref could
  silently expose divergent heap contents to two otherwise-agreeing
  runs. E4 requires that when the result QTyp is clean under the
  regime, the two runs' heaps agree at the registered address.
- **R20**: the cleanness condition on E4 is `qtypCleanUnder R
  tcRes.qualType`, not `IsCleanAtRegistration d`. A
  predicate-guarded extern ref can *become* clean when the regime
  maps its tag to true; FR regards such a cell as clean and expects
  two-run agreement at that point. Tying E4 to the FR cleanness
  predicate catches that case automatically.
- **R22**: `Memory.lookup` returns `Option Int`, so the populated-
  cell form is `some n`, not `some (.int n)`.

Intermediate-configuration transport (from initial to reachable
`cfgᵢ`) requires:

- `nextAddr` monotonicity (proven once extended to fn dispatch via
  Contract D).
- `θ` monotonicity — realisation maps grow by allocation and never
  forget earlier bindings; this is a prerequisite lemma.
- Memory monotonicity at read-only ref positions, which Contract C
  must preserve (see R12: runtime-instantiation preservation).

Discharged by the driver at setup: `Main.lean` initialises
`Config.memory` identically in both runs at the addresses named in
ref-typed externVal registrations and sets `Config.nextAddr` strictly
above them, then constructs matching `memEnv₀`/`θ₀` and
`memEnv₁`/`θ₁` bindings. Vacuous for all impls except
`.val (.loc _)`.

### Contract F — Extern Fn/Pfn Poison Non-Leakage

**Layer:** implementation (impl-scoped).
**Status:** 🟡 **Proposed (new, from review finding R3).** ⚠️
**Affected by review findings R8 (two-run shape) and R9 (declaration
lookup).** The revised form below restates F in StepFR shape — two
memory-type envs, two realisation maps, `predSat`, regime — and
reads declaration fields directly from `ExternDeclaration` rather
than from a synthesised `Typ.arrow`.

F is the load-bearing FR property for executable externs. Without
it, Contracts C/D/E/D together do *not* imply fault-robustness,
because an impl can receive clean-equivalent inputs (agreeing on all
clean positions) and still produce return values or memory effects
that diverge on clean positions by reading poisoned parts of the
input.

**Revised per-extern form (addresses R8, R9, R15, R16, R17, R19):**

```lean
/-- FR-shaped clean-input agreement: both memory-type environments,
    both realisation maps, a variable typing environment for
    captured envs (R19), plus `predSat` and regime are threaded
    exactly as StepFR threads them.  `agreeValueUnder` is the
    existing two-μ/two-θ FR notion from
    `LeanProofs/FaultRobustness.lean:445`; `agreeVarEnvUnder` and
    `agreeMemUnder` are its environment- and memory-level lifts. -/
def cleanInputAgreement
    (predSat : PredSat) (R : Regime)
    (ρ : VarTypeEnv)                -- R19: typing context for envs
    (μ₀ μ₁ : MemoryTypeEnv) (θ₀ θ₁ : RealizationMap)
    (argTyp : QTyp)
    (env₀ env₁ : VarEnv) (arg₀ arg₁ : Value)
    (m₀ m₁ : Memory) : Prop :=
  agreeVarEnvUnder   predSat R ρ μ₀ μ₁ θ₀ θ₁ env₀ env₁ ∧
  agreeValueUnder    predSat R   μ₀ μ₁ θ₀ θ₁ argTyp arg₀ arg₁ ∧
  agreeMemUnder      predSat R   μ₀ μ₁ θ₀ θ₁ m₀ m₁

def Contract_F (d : ExternDeclaration) (impl : ExternImpl) : Prop :=
  match impl with
  | .fn f =>
      d.kind = .fn →
      -- Typechecking produced a call-site TypeResult with the
      -- computed argument and return QTyps; those QTyps are what
      -- FR sees, not `d.typ`.
      ∀ (callTc : ExternFnCallTypecheck d)
        (predSat : PredSat) (R : Regime) (ρ : VarTypeEnv)
        (μ₀ μ₁ : MemoryTypeEnv) (θ₀ θ₁ : RealizationMap)
        (μ₀' μ₁' : MemoryTypeEnv) (θ₀' θ₁' : RealizationMap)
        (R' : Regime),
        -- Typing predicts post-state per the effects summary; this
        -- is the FR-standard post-call typing slot.
        TypingModelsFnCall d callTc
          ρ μ₀ μ₁ θ₀ θ₁ R  μ₀' μ₁' θ₀' θ₁' R' →
        -- R15: the two runs have *independent* input cursors
        -- `addr₀ᵢ` and produce *independent* post cursors
        -- `addr'ᵢ`.
        ∀ {env₀ env₁ : VarEnv} {arg₀ arg₁ v₀ v₁ : Value}
          {m₀ m₀' m₁ m₁' : Memory}
          {addr_0 addr_0' addr_1 addr_1' : Address},
          f env₀ arg₀ m₀ addr_0 = .ok (v₀, m₀', addr_0') →
          f env₁ arg₁ m₁ addr_1 = .ok (v₁, m₁', addr_1') →
          cleanInputAgreement
            predSat R ρ μ₀ μ₁ θ₀ θ₁
            callTc.argQTyp env₀ env₁ arg₀ arg₁ m₀ m₁ →
          -- F1: clean-equivalent inputs yield clean-equivalent
          --     return values per the computed retQTyp.
          agreeValueUnder predSat R' μ₀' μ₁' θ₀' θ₁'
            callTc.retQTyp v₀ v₁
          ∧
          -- F2: post-memories agree on every post-clean cell
          --     (R16).  `agreeMemUnderCleanCells` requires agreement
          --     at every address `a` whose post-cell poison is
          --     clean under `R'` — including effect-written cells
          --     whose write discharged under a clean pc.  Only
          --     post-dirty cells may differ.
          agreeMemUnderCleanCells
            predSat R' μ₀' μ₁' θ₀' θ₁' m₀' m₁'
  | .pfn f =>
      d.kind = .pfn →
      ∀ (callTc : ExternPfnCallTypecheck d)
        (predSat : PredSat) (R : Regime) (ρ : VarTypeEnv)
        (μ₀ μ₁ : MemoryTypeEnv) (θ₀ θ₁ : RealizationMap),
        ∀ {env₀ env₁ : VarEnv} {arg₀ arg₁ v₀ v₁ : Value}
          {m₀ m₁ : Memory},
          f env₀ arg₀ m₀ = .ok v₀ →
          f env₁ arg₁ m₁ = .ok v₁ →
          cleanInputAgreement
            predSat R ρ μ₀ μ₁ θ₀ θ₁
            callTc.argQTyp env₀ env₁ arg₀ arg₁ m₀ m₁ →
          -- Pure externs leave memory unchanged, so only return
          -- agreement is required; μ, θ, R are unchanged.
          agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁
            callTc.retQTyp v₀ v₁
  | _ => True
```

Auxiliary predicates:

- `ExternFnCallTypecheck d` / `ExternPfnCallTypecheck d` bundle the
  typechecking-time information for a specific call site: the
  computed `argQTyp` and `retQTyp` (drawn from `d.retSpec` plus
  call-site instantiation), fresh-tag mapping, allocated Locs, etc.
  These cannot be recovered from `d.typ` alone (R9): `Typ.arrow` has
  no QTyp or effects flavour.
- `TypingModelsFnCall d callTc ρ μᵢ θᵢ R μᵢ' θᵢ' R'` asserts the
  typing-side view of the post-state (`μ'ᵢ`, `θ'ᵢ`, `R'`)
  corresponds to the runtime execution — the same FR discipline
  StepFR already applies to user-closure calls. `ρ` is the variable
  typing environment carried into captured-env agreement (R19).
- `agreeMemUnderCleanCells` is the memory-level cleanness-agreement
  predicate: it requires agreement at every address whose **post**
  cell is clean under `R'`, including effect-written cells whose
  write discharged under a clean pc (R16). Only cells that are
  *post-dirty* may differ. `applyExternEffect` records a cell as
  `joinPoison pc effect.poison`, so a clean pc + clean effect
  poison produces a post-clean cell even inside the effect frame —
  and that cell must agree across runs.

**Plain-English intuition.**

> If two runs call the same extern `fn` or `pfn` with inputs that
> agree on every clean position (environment, argument, memory), the
> outputs must also agree on every clean position — the declared
> return type for the return value, and the declared effects for the
> post-memory. The impl may *see* poisoned input, but it cannot make
> its clean output *depend* on it.

**Discussion.** F is the core FR property for trusted externs.
C/D/E are *hygienic* properties — they keep `wfConfig` / `wfMem`
preservation intact across extern dispatch — but do not constrain
information flow. F closes the FR case by tying the clean projection
of outputs to the clean projection of inputs.

Quantification is *relational*: F talks about pairs of runs of the
same impl, not about a single run. This matches the shape of the FR
theorem itself.

Pure externs (`pfn`) have no memory obligation (no mutation) so F
collapses to return-value agreement. Impure externs (`fn`) need both
return-value agreement and per-cell clean-cell memory agreement
(R16).

Open formalisation points:

- `cleanInputAgreement`, `agreeMemUnder`, and
  `agreeMemUnderCleanCells` need concrete definitions. The first
  two are straightforward lifts of the existing `agreeValueUnder`
  to environments and memories; the third requires the logical
  effect-set story from Contract C (R5 fix).
- Quantification over `μ` and `θ` makes F a family of claims indexed
  by typing artifacts that FR threads at the call site. Drivers
  discharge F generically: a trusted `fn` impl that only inspects
  clean parts of its inputs satisfies F for all `μ, θ`; one that
  reads poisoned parts and writes them onto clean outputs does not.
- F interacts with the nested-return shape of extern dispatch: if a
  fn returns a callable, the returned closure must itself satisfy F
  at its own call sites. The simplest treatment is to require
  nested-return wrapper shapes to be externs (which they already
  are) with their own id-indexed F evidence.

**Relation to Contracts A–E.** F is orthogonal to all four:
- A, B are typing-layer; F is implementation-layer relational.
- C is a per-call frame (single run); F is a two-run agreement.
- D is an address monotonicity invariant; F has nothing to say about
  addresses.
- E is an init-time value claim; F is a per-call claim.

## How evidence is consumed

Typing-layer evidence is retrieved by `(id, d)` from `tr.declEv`;
implementation-layer evidence by `(id, d, impl)` from `tr.implEv`
(R17-reindexed):

```lean
-- Before (global axioms):
theorem FaultRobustness_step ... := by
  ...
  have := externGuardProvenance ctx r hcall hpc l k qt hout          -- B
  have := externTagSoundness tm mapping preds env _ _ halloc          -- A
  ...

-- After (evidence registry, two layers, R17-reindexed):
theorem FaultRobustness_step (e : Expr) (tr : TrustedRegistry e) ... := by
  ...
  -- Typing-layer lookup (no registration required):
  have hdecl := tr.declEv id d hDeclared      -- hDeclared : declEnv.get? id = some d
  have := hdecl.guardProvenance hKindFn ctx r hcallD hpc l k qt hout    -- B
  have := hdecl.tagSoundness env tm mapping _ _ hFresh halloc            -- A

  -- Implementation-layer lookup (only when dispatching):
  have himpl := tr.implEv id d impl hDeclared hreg
  have ⟨hFrame, hDomain, hInstant⟩ :=                                    -- C
    himpl.frame hKindFn ctx ctx' argTyp θ θ' memEnv' hrun hTypModel
  have hMono := himpl.addrMono hrun                                      -- D
  have ⟨hRetAgree, hMemAgree⟩ :=                                         -- F
    himpl.nonLeakage hKindFn callTc
      predSat R ρ μ₀ μ₁ θ₀ θ₁ μ₀' μ₁' θ₀' θ₁' R'
      hTypingModels hrun₀ hrun₁ hInputClean
  -- Contract E (ref-val initialisation) is consumed at init:
  have ⟨hθ, hBound, hPresent, hCleanAgree⟩ :=                            -- E
    himpl.refInit hKindVal hTypeRefInt
      tcRes l hExternValTc cfg₀ cfg₁ μ₀ μ₁ θ₀ θ₁ R hInitPair hreg₀ hreg₁
  ...
```

Top-level theorems — `TypeSystemEnforcesFaultRobustness` and
companions — take `(e : Expr) (tr : TrustedRegistry e)` and thread
`tr` to whichever `StepFR*` modules need it. Pure-Poison steps are
unaffected; `tr` is carried but never destructured.

## Migration plan for Contracts A and B

Both live today as admitted axioms and have call sites spread across
`LeanProofs/`. Moving them into the typing-layer evidence bundle is
a structural refactor for B, and a *semantic* rewrite for A — the
original Contract A conclusion is uninhabitable (R1), so the plan
must rewrite its consumers rather than rederive the old axiom.

1. Introduce `ExternDeclaration`, `DeclEnv`,
   `ExternDeclarationEvidence`, `ExternImplEvidence`, and
   `TrustedRegistry` in `LeanProofs/ExternAxioms.lean` (or a sibling
   file).

2. **Contract B (structural migration):** re-derive the current
   universal axiom statement from the bundle field as a theorem:

   ```lean
   theorem externGuardProvenance_of_registry
       (e : Expr) (tr : TrustedRegistry e)
       (id : ExternId) (d : ExternDeclaration)
       (hDeclared : tr.declEnv.get? id = some d)
       (hImpure   : d.kind = .fn) ... :
       -- same conclusion as the old externGuardProvenance axiom,
       -- narrowed to declaration `d`.
       ... :=
     (tr.declEv id d hDeclared).guardProvenance hImpure ...
   ```

   B's semantic content is unchanged; only the quantifier is
   narrowed to a specific id.

3. **Contract A (semantic rewrite — R13):** the old
   `externTagSoundness` conclusion
   `TagMappingRespectsTagMeaning tm mapping preds env` is false for
   arbitrary `tm` (R1). The evidence-registry form (A1 or A2) gives
   an *extended* `tm'` that respects the mapping. Consumers must
   change accordingly:

   - Each site that today concludes
     `TagMappingRespectsTagMeaning tm mapping preds env` must be
     rewritten to obtain `tm'` from the evidence, together with a
     witness that `tm'` extends `tm`.
   - The extension witness is threaded through the downstream
     `PredSatLaws` and `wfTagMeaningCtx` transport lemmas so that
     any predSat / wfTagMeaning hypothesis about `tm` is first
     *transported* to `tm'` before the guard descriptor is
     recovered.
   - A provable `tm'_extends_tm_preserves_*` helper family will
     likely emerge: one lemma per typing invariant that currently
     hangs off `tm`.

   There is no plan step that "keeps the old conclusion" — R1
   rules that out. The concrete refactor is:

   - rename / replace every `externTagSoundness ...` call to the
     evidence form with the extension witness;
   - add transport lemma invocations at the boundary;
   - delete the old axiom.

4. Thread `tr` through the top-level FR theorems and intermediate
   lemmas that reach extern sites.

5. Retire the original `axiom` declarations in
   `LeanProofs/ExternAxioms.lean`. At that point that file contains
   **zero** `axiom` declarations — only structure definitions,
   `Contract_*` predicate definitions, and helper/transport lemmas.

Because A and B are typing-layer, migration can proceed
independently of any decision about the implementation-layer
contracts (C, D, E, F). Step 5 is the concrete axiom-hygiene payoff.

## Sorries discharged

Status below is as of the current `ffi` branch.

| `sorry` location | Layer | Evidence consumed | Current status | Notes |
|------------------|-------|-------------------|----------------|-------|
| `SemanticsProperties.lean:425` — `app` fn-case `wfConfig` preservation | impl | `implEv.frame` (C — C1 frame, C2 domain bound, C3 runtime-instantiation), `implEv.addrMono` (D) | ⏳ open | C3 gives `wfMem addr' mem'` via domain bound + heap + instantiation preservation; D gives `wfVarEnv addr' cfg.varEnv` via monotonicity. |
| `SemanticsProperties.lean:1899` — `externVal` `ref int` `wfConfig` preservation | impl | `implEv.refInit` (E) + proven `nextAddr` monotonicity | ⏳ open | E at init (E1 θ-realisation + E2 bound + E3 runtime presence), monotonicity transports to intermediate `cfg`. |
| `FaultRobustnessProofs.lean` — former `terminatesTo_extern_absurd` × 6 | typing (+ impl for `ref int` val) | `declEv.tagSoundness` (A, revised form); `implEv.refInit` (E) only for the `externVal (ref int)` subcase | ✅ **currently vacuous** — closed without any FFI evidence | See "Vacuous-premise note" below. |
| FR at extern fn/pfn dispatch inside `StepFRApp` | impl | `implEv.nonLeakage` (F) — return-value agreement + effects-bounded memory agreement | 🔜 not yet materialised | Becomes a real obligation once registry is threaded and `FnTClosure.extern` carries ids (R2). This is the StepFR-level site where F is consumed. |

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
  `implEv.refInit` (Contract E).
- Contracts B, C, D remain out of scope here because these sites are
  at extern *declaration* form, not at extern call dispatch. They are
  consumed inside `StepFRApp` when an extern closure is actually
  applied.

### `FnTClosure.extern` representation gap (prerequisite — R21)

⚠️ **Elevated from follow-up to prerequisite by R21.** `valueHasETyp`,
`deepValueQTypProperty`, and `agreeValueUnder` all currently match
`FnTClosure.regular` only; none has a constructor or branch for
`FnTClosure.extern`. Under the vacuous-premise closure this is
never reached, but once a populated registry is threaded in:

- Contract F cannot establish clean agreement for returned extern
  callables — whether top-level (the `retQTyp` of an `externFn`
  declaration could itself be a function type) or nested (an extern
  returning a callable). `agreeValueUnder` has no extern closure
  branch to apply.
- Contract C's `wfMem` preservation similarly depends on
  `valueHasETyp` being able to type extern closure cells if the
  heap ever holds them.

Two resolutions:

- **Extend the inductives.** Add an `.extern` constructor to each of
  `valueHasETyp`, `deepValueQTypProperty`, `agreeValueUnder` that
  consumes the id-indexed evidence and produces the closure-typed
  / cleanness verdict.
- **Thread evidence through Contract A / F.** Contract A supplies
  the value-typing witness; Contract F supplies the agreement
  witness. The inductives then have no extern branch but consumers
  at extern call sites invoke the evidence directly.

The choice affects Contract A's shape (whether it must produce
`valueHasETyp` or only tag mapping) and the extent of the
refactor. Either way, this must be decided **before** Contracts C
and F can be stated concretely in Lean — it is a prerequisite
refactor, alongside R2 (ids on closures) and R7 / R18 (declaration
environment + program-consistency premise).

### Other extern-related sorries

All other extern-related `sorry`s in the proof development concern
top-level extern *declarations* (which leave `Config` unchanged) and
close mechanically without any evidence — the same pattern as the six
former `terminatesTo_extern_absurd` sites, and for the same reason
(empty-registry default in the theorem statement).

## Overlap audit

The six contracts address distinct parts of extern state. No
redundancy, no contradiction.

| | Object addressed | Shape | Quantifier | When checked |
|---|---|---|---|---|
| A | tag-mapping existence compatible with `preds` | existential (R1) | ∀ declaration | typecheck time |
| B | type-level trusted guard cells | absolute | ∀ impure call to id | typecheck time |
| C | runtime memory frame + domain bound | absolute | ∀ fn call to id | dispatch time |
| D | `nextAddr` ordering | absolute | ∀ fn call to id | dispatch time |
| E | registered `loc` realised + initialised | absolute | per registration | init |
| F | clean-input → clean-output | **relational** (pairs of runs) | ∀ fn/pfn call to id | dispatch time |

B and C both touch "effects" but at different layers (type-level
guards vs. value-level memory). Sharing one `resolveEffectsLogical`
definition (with a θ-realisation bridge to `resolveEffectsRuntime`)
keeps typing and semantics synchronised; the two contracts still
compose rather than overlap.

F is the only relational contract: it reasons about pairs of runs.
A, B, C, D, E are all about a single run (or a single registration, in
E's case).

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

Six contracts, two layers:

| # | Name | Layer | Status | Scope | Consumed at |
|---|------|-------|--------|-------|-------------|
| A | Tag Mapping Soundness | typing | ⚠️ admitted, uninhabitable as stated (R1) | every declaration | extern-decl typechecking |
| B | Impure Extern Guard Provenance | typing | ✅ admitted (R2 at call site) | impure (`externFn`) declarations | StepFR App fn-case |
| C | Extern Fn Frame (+ domain bound) | impl | 🟡 proposed (revised for R4, R5) | registered `.fn` impls | `wfConfig` preservation + FR |
| D | Extern Fn Address Monotonicity | impl | 🟡 proposed | registered `.fn` impls | `wfConfig` preservation |
| E | Ref-Typed Extern Val: Initial Realisation | impl | 🟡 proposed (strengthened for R6) | registered `.val (.loc _)` at `ref int` | `externVal` preservation + FR declaration sites |
| F | Extern Fn/Pfn Poison Non-Leakage | impl | 🟡 proposed (new, from R3) | registered `.fn` / `.pfn` impls | FR at extern dispatch (relational) |

**Typing-layer (A, B)** constrain properties of extern declarations in
the program AST. They are consumed whenever a declaration is
typechecked, regardless of whether a runtime implementation is
registered under the same id.

**Implementation-layer (C, D, E, F)** constrain well-behavedness of
the driver-supplied runtime code (or registered value, in E's case).
They are consumed only when the registry actually contains an impl
for that id — an unregistered declaration carries no
implementation-layer obligation.

Contracts A and B already exist as universally-quantified axioms and
are consumed by the current proof development; migrating them into
`ExternDeclarationEvidence` is structural. A additionally requires the
R1 formulation fix. Contracts C, D, E, F are new and together close
the pending extern-related FR obligations by landing in
`ExternImplEvidence`.

End state (once R1, R2, R5, R7, R18, R21 are resolved and
C/D/E/F are instantiated): `ExternAxioms.lean` contains zero
`axiom` declarations — only the `TrustedRegistry`, `DeclEnv`,
`ExternDeclaration`, `ExternDeclarationEvidence`, and
`ExternImplEvidence` structures, `Contract_{A,B,C,D,E,F}` predicate
definitions, and derived compatibility theorems restating the old
universal axiom forms from the bundle. The top-level FR theorem
becomes evidence-parameterised, indexed by the program expression
`e` (R18):

```lean
theorem TypeSystemEnforcesFaultRobustness
    (e : Expr) (tr : TrustedRegistry e) (cfg₀ : Config)
    (hreg : cfg₀.registry = tr.reg) ... :
  ... FR conclusion about `e` under cfg₀ ...
```

`TrustedRegistry e` carries `tr.hProgramConsistent :
ProgramDeclsMatch e tr.declEnv` as a field, so the
program-consistency premise is part of `tr` and does not need a
separate theorem hypothesis.

Concrete drivers (e.g. `Main.lean`) supply a `TrustedRegistry` with
concrete proofs — typing-layer evidence for every declared extern plus
implementation-layer evidence for every registered impl. Abstract
reasoning and separate-compilation scenarios supply hypothetical
registries to prove component FR independently.

## Prerequisite refactors

The review findings identify two prerequisites that cannot be
addressed within this document alone:

- **R2 — ids on type-level extern closures.** `FnTClosure.extern` and
  `PFnTClosure.extern` in `LeanPoison/Syntax.lean` must propagate
  `ExternId` through `applyFnTClosure` (`LeanPoison/Typecheck.lean`)
  so that `ImpureExternCallOkFor d` and analogous predicates can be
  stated. Without this refactor, per-declaration evidence cannot be
  consumed at type-level call sites.
- **R7 — explicit declaration environment.** `TrustedRegistry`
  introduces `DeclEnv` as a required field; the FR theorem carries
  it via `TrustedRegistry e`. This is a threading refactor through
  all FR statements, not a contract change per se.
- **R18 — program-consistency premise grounded in `e`, not `ctx`
  or `cfg`.** The top-level FR theorem must be indexed by the
  program expression `e : Expr` being typechecked, so
  `ProgramDeclsMatch e tr.declEnv` is a valid claim. Threading `e`
  explicitly through FR — rather than trying to recover it from
  `TypeContext` or `Config` — is a prerequisite for stating
  `TrustedRegistry e`.
- **R21 — extern-closure representation gap.** `valueHasETyp`,
  `deepValueQTypProperty`, and `agreeValueUnder` must either gain
  `.extern` constructors or Contract A / F must be strengthened to
  supply their witnesses at extern call sites. Either way, this
  decision precedes the concrete Lean form of Contracts C and F.

All four refactors are prerequisites to instantiating the revised
contracts A, C, E, F in Lean. R1 (Contract A's uninhabitability) is
a formulation fix local to the contract statement, but its
elimination from `LeanProofs/ExternAxioms.lean` requires updating
every consumer of the current `externTagSoundness` signature.
