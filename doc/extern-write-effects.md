# Extern Ref Trust: Plan for `@21`

## Status

Implemented end to end. The surface form, gates, boundary contract, and
threading below are all in the tree:

- Trusted spec: `ExternProofs.builtinErrnoSpec` (axioms
  `propext`/`Classical.choice`/`Quot.sound` only).
- Program-level FR: `ExternRegimeInt.errnoExternRef_FR` (bare declaration)
  and `ExternRegimeInt.errnoScenario_FR` (combined `@21`/`@22`
  declare/write/read);
  the migrated `@22` capstone `ExternRegimeInt.setErrWriteEffect_FR` remains
  axiom-clean modulo the top-level theorem's pre-existing `native_decide`
  baseline.
- Examples: `examples/extern_errno.poison`, `examples/extern_ref_*.poison`.
- The declared-set/no-declare typechecker lemmas live in
  `LeanProofs/TypeSafety.lean` (`typecheck_declared'_mono`,
  `typecheck_declared'_eq_of_not_allowed`); the reserved-address invariants
  (`RegistryReservedWF`, `ReservedDiscipline`) are threaded through
  `StepFR`/`StepFRPost` exactly as planned below.

The remainder of this document is the design rationale and plan it was built
from; the entry for `@21` in `doc/externs.md` describes the resulting
language-level behavior.

## Problem

`@21` models an external `errno` cell as a stable reference supplied by the
runtime registry. The pre-pivot surface form (now rejected) was:

```poison
extern val @21 : (ref int :> clean {})
```

That form is ambiguous. It says the returned value is a clean reference, but it
does not separately say what is known about the memory cell behind the
reference. The pre-pivot implementation filled that gap by seeding the fresh
logical cell as clean (`surfaceSpecToQTyp`). That is too strong for
fault-robustness unless the theorem also knows that both runs initially
contain the external cell and agree on its contents.

There are two distinct obligations:

- **Reference trust:** the extern returns a stable, well-formed location value.
- **Cell-content trust:** the memory at that location has the declared
  qualified type, and if it is clean then paired runs agree on it.

The old `extern val` syntax collapses those obligations into one annotation.

## Proposed Surface

Introduce an explicit reference-valued extern form:

```poison
extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {})
```

The annotation before `points_to:` describes the reference value. The
`points_to:` annotation describes the cell content. Like the other extern
forms, `extern ref` is an expression: it is usually bound with `let`, but it
may appear anywhere a `ref int` expression is accepted (subject to the
placement restrictions below).

The old ref-typed `extern val` form is rejected. `extern val` is reserved for
scalar values; `extern ref` is the only spelling for external memory handles.

### Restrictions (load-bearing; rationale in the sections below)

- **Poisoned `points_to:` only.** The typechecker rejects
  `points_to: (int :> clean ...)` with an explicit error. This is a real
  expressiveness limitation, described in "Limitation: no clean `points_to:`
  cells" below. The grammar and Ott keep the annotation slot general so only
  the typechecker gate moves if the limitation is lifted.
- **At most one `extern ref` declaration per extern id per program**,
  including across the two arms of an `if`. `typecheckIf` already threads
  fresh-allocation state serially — the else arm starts from the then arm's
  `nextLoc`/`nextTag` (`Typecheck.lean:2271`, `Typecheck.lean:2305`) — so
  threading the declared-id set the same way rejects cross-arm duplicates
  with no extra machinery. Note this is a *new, program-level* rule: the
  driver's `register` rejects duplicate ids at *registration* time
  (`Typecheck.lean:2358`), which does not constrain how often a program
  *declares* an id.
- **`extern ref` may not appear under `fn`/`pfn` bodies.** This confines each
  declaration site to evaluate-at-most-once positions. The language currently
  has no loop construct; if one is ever added, its body must join this
  exclusion — the `ReservedDiscipline` invariant below depends on it.
  Enforcement follows the language's deferred body typechecking: `pfn` bodies
  are rejected at declaration (the `toPExpr` conversion has no
  extern-declaration form), `fn` bodies at application (a never-applied `fn`
  whose body contains an `extern ref` typechecks, like any other type error
  in a never-applied body; that body never evaluates, so soundness is
  unaffected).

## Limitation: no clean `points_to:` cells

A trusted *initialized* external cell — `points_to: (int :> clean {})` —
cannot be supported by this design. The rejection above is a language
limitation to be documented as such, not a temporary gate on unfinished
proofs.

The obstruction: the declaration introduces the cell as a *fresh* logical
location, and two postconditions of `StepFRPost` are contradictory for a
fresh clean cell. `FreshCleanLocsUnrealizedOneRun` (`StepFR.lean:950`) forces
every fresh clean cell to be unrealized, while the returned ref value must be
*realized* at that same location: `valueHasETyp.loc`
(`TypeSafety.lean:1006`) demands a θ binding for any typed ref result,
whatever the ref qualifier says, and a clean ref additionally routes result
agreement through `agreeValueUnder.clean_ref` (`FaultRobustness.lean:625`)
over the same binding. No trusted hypothesis can reconcile unrealized with
realized. The invariant is not an
artifact: a clean cell asserts that paired runs agree on its contents, and
that agreement must have a source — a mid-evaluation allocation has none.

Lifting the limitation requires the cell to *pre-exist* rather than be minted
at the declaration: represent reserved external cells in the initial type
context and input spec (a canonical logical location in the initial `memEnv`,
realized by the initial θ, with cross-run agreement supplied by the existing
initial clean-cell premise). The declaration then typechecks as a lookup
instead of an allocation. That needs a registry-aware initial-context
construction and an `InputSpec` extension — out of scope here. In practice
little is lost: a write effect re-establishes cleanness (as `@22`'s `set_err`
does), so the conservative declare-poisoned / write / read-clean flow covers
the errno use case.

## Boundary Intuition

An `extern ref` expression introduces a fresh logical location `ell`, inserts
the `points_to:` qualifier for `ell` into the memory type environment, and
returns `ref {ell}` with the qualifier from `(ref int :> ...)`. At runtime the
registry supplies a fixed concrete address (`Value.loc errnoAddr`), and the
fault-robustness proof realizes `ell` to that address by extending the
realization map θ.

Because `points_to:` is poisoned, the new cell is not a clean input: clean
agreement and fresh-clean-location obligations for the cell are vacuous
(`locsRegime.noPred_ok` covers its regime consistency). The proof needs the
concrete address to exist in memory, to lie below `nextAddr`, and — the crux —
to be insertable into θ without breaking injectivity.

## Why the realization map is the crux

This obligation shapes the restrictions above and the threading step below.

- Any ref-typed result forces realization: `StepFRPost` requires
  `valueHasETyp` for the returned value (`StepFR.lean:131`), and
  `valueHasETyp.loc` (`TypeSafety.lean:1006`) demands
  `θᵢ'.lookup ell = some errnoAddr` in both runs *regardless of the ref
  qualifier's poison* — declaring the ref value poisoned would not avoid
  this. The clean qualifier additionally routes result agreement through
  `agreeValueUnder.clean_ref` (`FaultRobustness.lean:625`) over the same
  binding. The declaration must therefore extend θ.
- Every declaration-level post goes through `StepFRPost`, which demands
  `wfExtendsMap θ θ'` (`StepFR.lean:129`), and `wfRealizationMap` is
  injectivity (`TypeSafety.lean:974–988`). Inserting `ell ↦ errnoAddr` is
  legal only if `errnoAddr` is not already in θ's range.
- That freshness is *not derivable* from existing invariants:
  `runtimeInstantiatesCtx` only gives `range(θ) ⊆ dom(μ)`, and the presence
  fact puts `errnoAddr` *into* `dom(μ)`. `extern ref` is the first construct
  binding a fresh logical location to an old address, so the freshness
  side-condition of `ExtTreeMap_insert_preserves_injectivity` has no existing
  supplier.

Consequences:

- **Static discipline.** The program-wide duplicate prohibition rules out two
  logical locations claiming the same reserved address (including across `if`
  arms, where serialized allocation gives the two arms distinct logical
  cells); the `fn`/`pfn` exclusion rules out re-evaluating one declaration
  site — via repeated application — against the same static context with an
  already-extended θ (which would falsify the invariant below at the second
  evaluation). With both, the declaration-step hypothesis can be plain
  freshness, no disjunctive "already bound at `ell`" case.
- **Dynamic invariant (`ReservedDiscipline`).** Reserved addresses of
  *not-yet-declared* extern-ref ids are unrealized:
  `∀ id a, reserved id a → id ∉ ctx.declaredExternRefs → a ∉ range(θ)`.
  Carrier: a declared-extern-ref set on `TypeContext` and `TypeResult`
  (threaded like the other typing state; see step 3). This lives in the
  internal StepFR machinery, which may change; the extern boundary and the
  top-level statement only ever see named instances of it.
- **Registry well-formedness.** Reserved addresses must be pairwise distinct
  across extern ids, else one declaration's θ-insert falsifies another id's
  invariant instance. As implemented this is *not* a `TrustedRegistry` field
  (`TrustedRegistry` remains a plain `List TrustedExternEntry`): distinctness
  is the first conjunct of `ReservedDiscipline` itself, stated over the
  runtime registry, which keeps the invariant's preservation lemmas
  self-contained — no separate registry hypothesis needs threading through
  the step proofs.

## Where the config facts live

The presence (`μ.contains errnoAddr`) and bound (`errnoAddr < nextAddr`) facts
are carried by a standalone config-indexed predicate (working name
`RegistryReservedWF`), **not** folded into `wfConfig`: a registry-dependent
`wfConfig` breaks the ~100+ registry-agnostic coercions that move `wfConfig`
across configs differing only in registry fields. The standalone
reserved-address definitions (`RegistryReservedBelow`,
`wfValue_loc_of_RegistryReservedBelow`, `Semantics.lean:71–132`) exist for
exactly this reason and are the base to build on. Both conjuncts of
`RegistryReservedWF` are monotone along evaluation (memory
only inserts/updates; `nextAddr` only grows), so preservation is one generic
lemma rather than per-proof-site churn.

## Top-level theorem impact (kept minimal)

The public statements — `TypeSystemEnforcesFaultRobustness` and
`FaultRobustnessSpec` (`FaultRobustnessProofs.lean:3320–3335`) — are textually
unchanged. The additions, each a named predicate with a one-line docstring:

- `FaultRobustnessSpecForCtx` (`FaultRobustness.lean:817`): one new initial
  premise `ctx.declaredExternRefs = []`, beside the existing
  `ctx.tagEnv = {}`. This is a **semantic precondition on the
  context-parametric spec**, not internal plumbing: like `ctx.pc = false` and
  `ctx.tagEnv = {}`, it narrows which custom initial contexts the spec
  covers, and callers instantiating it at hand-built contexts must satisfy
  it. Its docstring should say so.
- `FaultRobustnessPointwise` (private, `FaultRobustness.lean:786`): per run,
  `RegistryReservedWF registry μᵢ aᵢ` beside the existing `wfConfig` premises,
  and "reserved addresses unrealized in the initial θᵢ" (the
  `ReservedDiscipline` instance at an empty declared set).

These are honest trusted initial-state assumptions of the same character as
the existing `wfConfig`/`runtimeInstantiatesCtx` premises: the initial state
must actually contain the registry's reserved cells and must not pre-claim
their addresses.

## Steps

Ordered high-risk-first; the prototype needs no syntax, so syntax churn waits
until the boundary shape is validated.

### 1. Prototype the `@21` declaration fields (highest risk — do first)

Pure proof-side, against a hand-rolled `ExternDeclaration`: prove
`declFR`/`declSingle`-shaped lemmas producing `StepFRPost`, with the runtime
facts supplied as explicit hypotheses:

- the registry entry returns `Value.loc errnoAddr`;
- `errnoAddr` is present in memory (for `runtimeInstantiatesCtx` of θ');
- `errnoAddr < nextAddr` (for `wfValue`);
- `errnoAddr ∉ range(θ)` in both runs (for the injectivity-preserving insert).

Expected content: the `wfExtendsMap` insert lemma via
`ExtTreeMap_insert_preserves_injectivity`; `runtimeInstantiatesCtx` extension
at `ell`; `locsRegime.noPred_ok` for the poisoned cell; vacuity of
`agreeOnClean`/`FreshCleanLocsUnrealized` for the cell; `clean_ref` agreement
for the result. Done means the postconditions hold with hypotheses no stronger
than the list above — this validates the boundary shape before anything else
is built on it.

### 2. Boundary contract for the ref kind (user-visible — keep crisp)

- `ExternDeclarationKind.ref` with a cell-qualifier field on
  `ExternDeclaration` (`ExternRuntime.lean:50`). A ref declaration pairs with
  the existing `ExternImpl.val (Value.loc a)` — no runtime change.
- `ExternBoundarySpec` keeps its five fields, and the new facts enter as a
  **ref-gated premise inside the existing `declFR`/`declSingle` field types**
  (shape `d.kind = .ref → ReservedCellFacts … → …`), bundling
  lookup/presence/bound/θ-freshness from step 1 into one named record rather
  than four loose premises. This is a field-*type* change, so every existing
  trusted spec (`@10`/`@11`, `@22`, `@23`, …) re-enters its decl proofs to
  introduce-and-discard the hypothesis its kind makes irrelevant — small but
  real churn to budget for. Call fields are vacuous for the ref kind (a
  reference extern is a declaration, not a callable).
- Operational repair: the current `.val` clause
  (`wfConfig cfg → wfValue cfg.nextAddr v`, `ExternRuntime.lean:487–512`) is
  unprovable for loc values, since registry-agnostic `wfConfig` admits any
  cursor. Scalars keep the current shape; loc well-formedness moves to a
  lookup-aware clause discharged from `RegistryReservedBelow` via
  `wfValue_loc_of_RegistryReservedBelow`.
- `TrustedRegistry`: add the reserved-address-distinctness field;
  extend `toRuntimeRegistry` / `runtime_lookup_exists` / `operationalSafe`
  for the new kind.

### 3. Syntax and typing

- AST: new `Expr.externRef` constructor (`Syntax.lean`), carrying the ref
  qualifier and the `points_to:` qualifier.
- Parser: `grammar.js` rule + `Parser.lean` XML conversion; `Pretty.lean`
  printer.
- **Ott changes (flagged):** new `extern_ref` production in the expression
  grammar (near `poison-lang.ott:95`) with tex hom; a new `extern_ref` typing
  rule (fresh location allocation, `points_to:` cell insertion, ref result);
  the `extern_val` rule (`poison-lang.ott:1287`) stops allocating locations —
  the `externValConvert` auxiliary (`poison-lang.ott:370`) loses its ref case.
- Typechecker: new `typecheckExternRef` (fresh `ell`, seed cell from
  `points_to:`, poisoned-only gate); delete the ref branch of
  `surfaceSpecToQTyp` (`Typecheck.lean:1047–1058`) and reject ref-typed
  `extern val` with a clear error pointing at `extern ref`.
- Restrictions: a defaulted `externRefAllowed : Bool := true` flag on
  `TypeContext` (set false when descending into `fn`/`pfn` bodies; flows
  downward only), and `declaredExternRefs` on `TypeContext` **and**
  `TypeResult` for program-wide duplicate rejection (threaded serially
  through `typecheckIf` arms, mirroring `nextLoc`, so cross-arm duplicates
  are caught too). The latter is the churn
  point: unlike defaulted-and-forgotten fields, the declared set must
  *propagate*, so every `TypeResult` literal in `Typecheck.lean` and the
  proof-side `ctxAfter` need the new field threaded. Budget for mechanical
  churn here; the `externRegime` field (`Typecheck.lean:305–310`) is the
  precedent for keeping record-update noise low.

### 4. Examples and docs

- Migrate the ref-typed `extern val @21` fixtures to the new form — precisely:
  `extern_errno`, `extern_set_err`, `extern_set_err_stale_guard`,
  `extern_set_err_unrelated_guard`, `extern_fn_captures_clause`,
  `extern_fn_captures_violation`, `extern_effect_under_poisoned_function`,
  `extern_effect_under_poisoned_pc`; plus `lp55xx-read` (`@233`/`@234`, two
  distinct ids — fine under the duplicate rule).
- Regenerate goldens and **review the semantic shifts**, don't just accept
  them: the errno cell is now poisoned until written, so a bare deref
  (`extern_errno`) reports a poisoned result type, while the `@22` flows stay
  clean *after* the `set_err` write effect re-seeds the cell.
- New examples: a basic `extern ref` + deref (poisoned result); assignment
  through the extern ref followed by deref (cell re-qualified by the write);
  an `extern ref` + `set_err @22` end-to-end flow. New `.fail` fixtures for
  each rejection: ref-typed `extern val`, clean `points_to:`, sequential
  duplicate declaration of one id, cross-`if`-arm duplicate declaration,
  `extern ref` under `fn`/`pfn`.
- Update `doc/poison-lang-description.tex` (extern section: the two-layer
  contract, the restrictions, the conservative-poisoned default, and the
  clean-`points_to:` limitation stated as a language limitation with its
  one-paragraph rationale).
- Update `doc/externs.md` (the `@21` entry) and `doc/ffi-proposal.md` (the
  errno surface in item 1), both of which show the ref-typed `extern val`
  spelling that becomes a rejection. Finish with a stale-grep pass over
  `doc/` (e.g. `rg "extern val @.*ref" doc/`) so no document keeps the
  rejected form.
- Validate this file and any other touched markdown with
  `npx markdownlint-cli`.

### 5. Assemble `builtinErrnoSpec`

Build the trusted boundary spec for `@21`: ref-kind declaration with poisoned
`points_to:`, declaration fields from step 1 routed through the step-2
contract, vacuous call fields, repaired operational field. Include it in a
small trusted scenario registry alongside `@22` (distinctness witness is
trivial while `errnoAddr` is the only reserved address). This delivers the
trusted artifact *before* the broad threading below.

### 6. End-to-end capstone and threading (broad but mechanical — do last)

- `SemanticsProperties.lean`: the three orchestration-facing lemmas gain a
  hypothesis on the initial config stated as the **full** `RegistryReservedWF`
  (presence *and* bound), not just the bound: the operational `val`/ref clause
  consumes the bound conjunct, the FR declaration case needs presence at the
  declaration point, and both must be preserved along the same evaluation
  prefix. Preservation is trivial in both conjuncts (memory only
  inserts/updates, `nextAddr` monotone, registry constant).
- StepFR machinery: thread `ReservedDiscipline` as a pre/post conjunct through
  `StepFR_single_run`/`StepFRPost` and the per-operator files. Precedent: the
  `PreservesInheritedCleanLocsOneRun` rollout — same shape of mechanical
  update at each rcases/construct site. Preservation per operator is easy:
  θ extensions either bind fresh `nextAddr` addresses (above every reserved
  address) or are the extern-ref insert itself (which moves its id into the
  declared set).
- Orchestration discharges the invariant from the new top-level premises.
- Capstone: a program-level theorem for a concrete errno scenario
  (declare `@21`, call `@22`, deref), mirroring `setErrWriteEffect_FR`.

## Interaction with the committed `@22` trust

`setErrWriteEffect_FR` and the `@22` examples bind errno through the
to-be-rejected `extern val @21` spelling, and their derivations were built
with the cell seeded clean. Migration flips the cell's pre-write state to
poisoned. The write effect re-establishes a clean cell, so the capstone
survives in substance, but expect proof rework wherever a concrete typechecker
run over a migrated fixture is instantiated — not just golden regeneration.
Re-verify the `@22` axiom-cleanliness after the migration.

## Impact Assessment

- **Language syntax:** yes. Adds `extern ref ... points_to: ...`; rejects
  ref-typed `extern val`, clean `points_to:` (a documented limitation, see
  above), program-wide duplicate declarations, and `extern ref` under
  `fn`/`pfn`.
- **Ott specification:** yes — flagged in step 3 (new production + typing
  rule; `externValConvert` loses its ref case).
- **Typing semantics:** yes. Ref-valued externs get separate qualifiers for
  the reference and the pointed-to cell; new typing-state fields
  (`externRefAllowed`, `declaredExternRefs`).
- **Runtime semantics:** no intended change. The registry still supplies
  `ExternImpl.val (Value.loc a)`.
- **Top-level theorem:** public statements textually unchanged; three named
  initial-state premises added in `FaultRobustnessSpecForCtx` /
  `FaultRobustnessPointwise` (declared set empty, reserved cells present and
  bounded, reserved addresses initially unrealized). The declared-set premise
  is a semantic precondition narrowing the admissible contexts of the
  context-parametric spec.
- **Extern boundary:** new ref kind; one bundled hypothesis record on the
  declaration obligations; reserved-address distinctness rides as the first
  conjunct of `ReservedDiscipline` over the runtime registry rather than as a
  `TrustedRegistry` field (`TrustedRegistry` is unchanged).
- **Proof risk:** concentrated in step 1 (boundary shape, done first) and the
  step-6 threading (broad but mechanical, done last, after the trusted spec
  already exists). The `wfConfig` fold is explicitly avoided.
