# Extern Regime Handling — Working Notes

Status: **analysis / planning**. This note isolates the regime
issue for extern-produced predicates from the broader extern poison discussion
in `doc/extern-poison.md`.

## 1. Problem Description

Extern return and effect specifications may introduce predicates intended to act
as latent de-poisoning markers. For example, an `open`-style extern may return a
poisoned integer where `ret >= 0` means the value is a valid file descriptor and
can safely be treated as clean after a matching runtime check.

The current implementation allocates fresh concrete guard tags for extern
predicates at the extern use site. The fault-robustness guard regime, however,
is defined only over tags that appear in the initial critical-input
specification. Tags allocated while typechecking an extern call are therefore
outside the regime domain available to the public FR scenario.

As a result, downstream checks can syntactically match an extern-produced
predicate, but the fault-robustness theorem cannot use the regime to de-poison
the value. The typechecker falls back to the conservative conditional path when
the fresh tag is absent from the regime, and the joined result remains poisoned.

## 2. Analysis

This appears to be a real expressiveness limitation rather than a soundness
bug. The current behavior is conservative: values remain poisoned unless they
are clean outright or their guard tag is known true in the regime.

The limitation matters because extern-produced predicates are meant to describe
facts about extern-produced values that are later consumed by ordinary Poison
checks.
Without a way for the regime to talk about those tags, return predicates on
externs are mostly decorative for fault-robustness. They can affect ordinary
typechecker behavior under manually supplied concrete regimes, but those
regimes are not generally well-formed under the public FR theorem.

The motivating `open` case exposes the problem clearly:

- `open` may return `-1` or a nonnegative file descriptor.
- The returned value should remain poisoned until checked.
- After `fd >= 0`, downstream code should be able to treat `fd` as clean.
- Under the current FR regime model, the fresh return tag for `fd >= 0` is not
  part of the regime domain, so the check cannot justify FR-level de-poisoning.

This issue likely affects both immediate extern returns and memory cells written
by extern effects when those writes install fresh predicates.

## 3. Historical Context: Why `TagIndex` Exists

`TagIndex` is not a generic typing wrapper around `Nat`; it was introduced for
a specific fault-robustness reason in issue #132. See
`doc/issue-132-proposal.md` for the full proposal and `LeanPoison/Syntax.lean`
(around the `TagIndex` definition) and `LeanPoison/Typecheck.lean`
(`collectAndAllocExternTags`, `resolveSyntaxPred`) for the implementation.

### 3.1 The Bug `TagIndex` Fixed

Before issue #132, extern specifications carried concrete `Tag` values baked
into `FnTClosure.extern` at declaration time. Two independent applications of
the same extern then reused the same concrete tag. The motivating example was:

```poison
let f =
  extern fn u : (unit) -> ((int :> poisoned { 5, v => (v >= 0) }))
in
let x = f unit in
let y = f unit in
if (x >= 0) then y else 0
```

Both `x` and `y` carried concrete tag `5`. The `if (x >= 0)` check established
tag `5` as known-true in `tagEnv`, and `y` then incorrectly inherited that
knowledge. This violated the freshness invariant the FR proof relies on: for
regular expressions, `generateFreshTag` allocates a fresh tag per use; the
extern path reused declaration-time tags.

### 3.2 The Resolution and Its Scoping Rule

Tag numbers in extern specifications were turned into *local symbolic names*
of a distinct type `TagIndex`. The typechecker allocates a fresh concrete
`Tag` per use site via `collectAndAllocExternTags` (build a per-site
`TagIndex -> Tag` mapping) and `resolveSyntaxPred` (substitute concrete tags
into the predicate). The per-site mapping (`TagMapping`) is discarded after
resolution.

The proposal's scoping rule, verbatim:

> Each extern definition (`extern val`, `extern fn`, `extern pfn`) has its own
> local symbolic tag namespace. The same literal number in two different
> extern definitions has no semantic connection. Nested returned externs are
> separate definitions with their own namespaces — they stay symbolic until
> applied.

`TagIndex` was deliberately made a `structure` rather than an `abbrev` for
`Nat` to prevent accidental mixups with `Tag` and to enforce the boundary
between source-level symbolic indices and allocator-produced concrete tags.

### 3.3 Implications for the Extern-Regime Design

`TagIndex` should remain an implementation mechanism for allocating fresh
concrete tags from declaration-local extern predicate syntax. It should not be
part of the user-facing FR scenario.

The user-facing selector should instead name extern ids. An extern id is already
the stable handle for an extern declaration. If an extern is treated as
potentially faulty, all output predicate tags produced by that extern are
part of the scenario's regime domain. This does not assert that any predicate
is true or that any value is clean; it only says that the regime must record a
truth value for those generated tags. This matches the intuition used for
critical inputs: the scenario names the source of possible fault, not each
internal tag allocation separately.

This also keeps the original `TagIndex` scoping rule intact. Reusing the same
local tag number inside different extern declarations has no FR-level meaning,
because regime selection happens by extern id.

## 4. Proposed Resolution

Extend the user-facing `InputSpec` with extern ids that are treated as
potentially faulty:

```lean
regimeExterns : List ExternId
```

The meaning is whole-extern selection. If an extern id appears in
`s.regimeExterns`, every output predicate tag generated by that extern is
included in the regime domain. If the same extern is called twice, both
concrete instantiations are included. If the extern has both return predicates
and effect predicates, all of those output tags are included.

Listing an extern id is a domain statement, not a trust statement. The concrete
regime still assigns each generated tag either `true` or `false`, and the
ordinary regime-consistency obligations still require each closure-backed tag's
assignment to agree with predicate satisfaction for the runtime value or memory
cell carrying the tag. Guard-only tags have no extra predicate-satisfaction
obligation, matching the existing regime model.

This field should contain ids only, not copies of predicate bodies. Predicate
meaning remains in the extern declaration and is tracked by the existing
`TagMeaning` / `GuardDesc` machinery after typechecking allocates concrete
tags.

Extern return/effect predicates whose extern id is not listed continue to
behave conservatively for FR: syntactic guard matching may find them, but the
active concrete regime has no entry for the generated concrete tag, so the
typechecker takes the conservative path.

### 4.1 Call-Site Regime Extension

The core typechecker and proof machinery operate on concrete `Tag` values.
Qualified types carry concrete `Predicate.guardClosure k ...`, and `Regime`
is a map from concrete `Tag` to `Bool`. Since ordinary typing rules consult
`ctx.regime`, extern-regime handling must be part of typechecking itself. A
proof-only trace cannot make a later `if` take a regime-determined branch.

When the typechecker allocates fresh concrete output tags for a selected extern,
it should extend the active regime at that call site. The existing local
`TagMapping` still resolves declaration-local `TagIndex` syntax to fresh
concrete tags. The new behavior is:

- if the extern id is not listed in `regimeExterns`, no regime entry is added;
- if the extern id is listed, every generated output tag that is actually
  attached to the returned value or an effect-written memory cell is inserted
  into `TypeResult.regime'` with the scenario's chosen `Bool`;
- if an effect predicate is erased by the existing poison/control-flow gate, no
  active predicate tag is installed and no regime entry is needed for that
  erased predicate.

The typechecker therefore needs a typechecker-visible extern-regime policy, not
only a proof-side `InputSpec` field. There are two useful granularities:

```lean
-- Executable/debugging interface: one value for every output tag of an extern.
externRegimeExec? : ExternId → Option Bool

-- Proof scenario interface: may choose per generated concrete tag.
externRegimeProof? : ExternId → Tag → Option Bool
```

The executable form is what a CLI such as `--extern-regime "238=true"` can
reasonably provide: every generated output tag for extern id `238` receives the
same boolean. The proof form is more precise because it is tied to a particular
deterministic typechecking run: after allocation, the scenario can assign
different booleans to different concrete output tags. In both cases, `some b`
means insert `k ↦ b` into the active `Regime`; `none` means leave `k` outside
the active regime.

Nested returned externs follow the same rule when they are later applied. The
outer call may return an extern value, but output tags for the nested extern are
generated by the later call to the nested extern's own id.

### 4.2 Regime Evolution

The current proof infrastructure uses `Regime.monotoneStep`: during
typechecking, regime entries may be dropped but never added or changed. That is
too strong once selected extern calls can create fresh output tags. The intended
replacement is a monotonicity-like relation: the regime is monotone for old
tags, but selected extern calls may add fresh tags.

Compared to the old regime invariant:

- existing entries still shrink monotonically: if `ctx.regime` maps `k` to
  `b`, then the result regime either still maps `k` to `b` or drops `k`;
- existing entries never change truth value;
- old absent tags are not persistently invented later: a tag below the incoming
  `ctx.nextTag` cannot appear in the result regime unless it was already
  present, except for branch-local refinements described below;
- the primary persistent additions are fresh tags allocated during the
  transition for output predicates of listed extern ids;
- any persistent added extern tag is fresh relative to the incoming context, so
  it cannot already occur in initial variables, initial memory cells, or
  pre-existing guard knowledge;
- branch-local guard refinements, if used by a rule, are a separate case. The
  Ott unknown-guard rules are written with temporary branch regimes
  `R[k |-> true]` and `R[k |-> false]`; the current Lean typechecker instead
  takes the conservative standard path without inserting such regime facts.
  If branch-local regime refinements are retained or reintroduced, the
  evolution relation should treat them as local refinements that are joined or
  discarded at the enclosing rule boundary, not as persistent extern additions;
- assignment invalidation and branch joins still shrink the active regime.
  They apply equally to initial critical-input tags and to tags introduced by
  selected extern calls.

Informally, this is "monotone modulo fresh selected extern outputs." The old
`Regime.monotoneStep` should remain available as a corollary for expressions
that do not add selected extern-output tags. Proofs that currently use
monotonicity to transport facts about old tags should be refactored to use the
old-tag part of the new relation.

The static exact-domain interpretation of `wfRegime R s` should remain an
initial-state property: initially, `R` is defined exactly for tags in
`inputSpecTags s`. After typechecking starts, the active regime domain is
stateful. The bridge invariant should say that every active tag is one of:

- a surviving initial critical-input tag;
- a surviving fresh output tag created by a selected extern call;
- a branch-local refinement currently inside a rule that introduces such
  refinements.

At rule boundaries, branch-local refinements must either be consumed by the
selected branch or removed by the existing join/discard behavior. This dynamic
domain should be justified by the regime-evolution relation, not by a
precomputed list of all future tags.

Branch placement therefore matters. If an extern call is made before a later
conditional, the generated tag can survive and drive the later guard check. If
separate extern calls occur in different branches of an unknown conditional,
their fresh regime entries are normally lost at the branch join, because
`joinRegimes` keeps only entries present with the same value on both sides.
This is conservative and consistent with the rest of the regime machinery, but
it means the design is most useful when the extern-produced value is bound
before the conditional that consumes its predicate.

### 4.3 Generated-Tag Handling

Use the existing typechecker point where extern predicates are resolved:

- `collectAndAllocExternTags` allocates fresh concrete tags;
- `resolveSyntaxPred` substitutes those concrete tags into returned/effect
  predicates;
- the extern typing rule attaches the resolved predicates to a returned value
  or effect-written memory cell.

At that same point, the typechecker should query the extern-regime policy and
extend `regime'` for selected extern-output tags. The proof should use the local
facts from this typechecking step: the generated tags are fresh, they came from
the current extern id, and they are attached to the produced value or written
cell.

The mechanism should cover returns and effects uniformly:

- simple extern return predicates;
- extern effect predicates written into memory cells;
- nested extern return/effect predicates when the nested extern is later
  applied.

If a selected extern is listed but produces no active output predicate tag in a
particular call, the regime is unchanged for that call.

### 4.4 Consistency And `masked`

This section separates three things that are easy to conflate: the active
typechecker regime, the consumer-side consistency invariant, and the proof-only
`masked` predicate.

The active `Regime` is part of typechecking. If a generated extern tag is meant
to drive regime-aware de-poisoning, it must be inserted into `ctx.regime` before
a later guard check consults that tag. `masked` cannot substitute for this:
masked tags are precisely tolerated as absent from the regime, so the executable
typechecker would still take the conservative path.

On the consumer side, do not introduce a special value-level consistency
relation for extern tags after they have been attached to values or memory
cells. Use the same regime handling already used elsewhere:

- initial critical-input tags are checked by the existing initial
  `consistentRegimeSpec` machinery;
- selected extern-output tags are fresh, so they impose no initial
  variable/memory obligation;
- after an extern call creates a value or memory cell carrying a selected
  extern-output tag, the existing `valueConsistentWithRegime` /
  `consistentWithRegime` predicates express the relationship between `R(k)` and
  predicate satisfaction.

For example, if an extern return has the qualified type:

```lean
int :> poisoned { k, fd => fd >= 0 }
```

then the ordinary regime invariant says the runtime value is consistent with
`R(k)`: when `R(k) = true`, the predicate holds; when `R(k) = false`, it does
not. This is the same interpretation used for non-extern predicate tags.

The proof-only `masked : Tag → Prop` predicate should keep its current role. In
the current proof stack, `regimeConsistentWithCtxMasked`,
`consistentWithRegimeMasked`, and `valueConsistentWithRegimeMasked` allow a
masked tag as an alternative to proving the ordinary regime-consistency fact.
This relaxes obligations for tags that are deliberately outside the active
regime, with side conditions such as `masked k → ctx.regime.lookup? k = none`
and absence from true `tagEnv` facts. Unlisted extern-output tags may be handled
this way because they cannot drive FR-level de-poisoning.

Selected extern-output tags are different. Once inserted into the active regime,
they should not be treated as masked at the point where their regime fact is
used. The proof will need preservation lemmas saying that inserting a fresh
unmasked extern tag preserves the masked invariants for the old masked set.

The remaining producer-side obligation is how the consistency invariant is
established for a value created by an extern call. Unlike initial
critical-input tags, selected extern tags have no initial runtime value. The
proof must connect the extern-produced value or memory write to `R(k)` at the
point where the predicate is installed.

For the fault-robustness theorem this is a two-run obligation. The two runs
share the same typechecking derivation and therefore the same concrete generated
tag `k`. If the scenario inserts `R(k) = true`, both runs' extern results at
that call site must satisfy the predicate for their returned value or
effect-written cell. If it inserts `R(k) = false`, both runs must fail that
predicate. This is separate from, and in addition to, any agreement obligation
on clean values.

In the current proof stack, this belongs near the
`ExternBoundarySpec.callFR` / call-boundary adapter layer, not in
`consistentRegimeSpec` and not in a new consumer-side value relation. The exact
encoding could be a new regime-aware field on `ExternBoundarySpec` or a
parallel call-boundary contract consumed by the extern application proof.

### 4.5 Proof Impact

Expected proof and implementation changes:

- extend `InputSpec` with `regimeExterns : List ExternId`;
- add a typechecker-visible extern-regime policy, likely as a new field in
  `TypeContext` or as an input threaded alongside it, with executable and proof
  granularities distinguished;
- update extern value/function application typing so selected extern-output
  tags are inserted into `TypeResult.regime'` when they are allocated and
  attached;
- replace uses of `Regime.monotoneStep` with a new regime-evolution relation
  that permits fresh selected extern-output additions, accounts for any
  branch-local regime refinements, and preserves old-tag monotonicity at rule
  boundaries;
- keep old monotonicity as a derived fact for rules that do not introduce
  selected extern-output tags;
- update `ctxMatchesInputSpec` / related hygiene lemmas so fresh extern tags
  cannot be mistaken for initial input tags;
- adjust `consistentRegimeSpec_implies_consistentWithRegime`: when an initial
  context tag is interpreted by `R`, it must still be an initial critical-input
  tag; fresh extern additions cannot occur in the initial context because they
  are above the initial `nextTag`;
- add masked-preservation lemmas for inserting fresh unmasked extern tags;
- add the call-boundary production-side extern obligation that establishes the
  two-run `valueConsistentWithRegime` / `consistentWithRegime` facts for
  selected extern-produced predicates.

The main proof churn is likely around lemmas that currently depend on global
regime monotonicity. The conceptual replacement is narrower but still useful:
old entries can only disappear, newly added entries are fresh selected extern
outputs, and all surviving entries keep their original truth values.

### 4.6 Validation Target

Use an `open`-shaped example as the acceptance target:

```poison
let fd = open path in
if fd >= 0 then fd else 0
```

For the FR scenario that lists the `open` extern id in `s.regimeExterns`, the
extern call allocates the generated concrete return tag `k` and inserts
`k ↦ true` or `k ↦ false` into the active regime according to the scenario. When
the inserted value is `true`, and the extern boundary establishes the required
consistency fact for the returned value, the later guard check sees `R(k) =
true` and the then branch should be able to treat `fd` as clean. The same
mechanism should work for an effect-installed predicate when the listed extern
produces the concrete tag attached to the written memory cell.

If `open` is not listed in `regimeExterns`, no entry is inserted for `k`; the
later guard check may still match syntactically, but `ctx.regime.lookup? k =
none`, so the typechecker takes the conservative path.

### 4.7 Runtime Typechecker Regime

The executable already accepts a concrete regime through the command line:

```text
--regime "100=true,101=false"
```

This remains the low-level concrete interface: it is a map from concrete `Tag`
values to booleans.

In implementation terms, `Main.parseRegimeSpec` parses the command-line map,
`initialTypeContext` installs it into `TypeContext.regime`, and the typechecker
threads that regime through `TypeResult.regime'`.

To match the proposed user-facing proof design, the executable should eventually
accept an extern-id-oriented regime as well, for example an interface shaped
like:

```text
--extern-regime "238=true"
```

The frontend would parse this as an extern-regime policy. When the typechecker
later allocates output tags for extern id `238`, it inserts those generated tags
into the active concrete `Regime` with value `true`. Until that exists, raw
`--regime` is a debugging-only escape hatch that still requires concrete tag
numbers.

This executable interface is a restricted fragment of the proof-side regime
model. The executable policy is naturally id-only:

```lean
externRegimeExec? : ExternId → Option Bool
```

In the proof, a listed extern id contributes all concrete output tags from that
extern to the active regime domain, while the scenario may assign different
booleans to different generated tags through the more precise proof policy. A
CLI shorthand like `--extern-regime "238=true"` assigns one boolean to every
generated output tag for that extern id, which is acceptable for a v1
debugging/user interface.

## 5. Open Questions

- Q1. What is the exact Lean shape of the extern-regime policy? The working
  intuition is an executable id-only policy plus a proof-side per-generated-tag
  policy, but the implementation still needs to decide how those two surfaces
  relate and whether the active typechecker hook belongs directly in
  `TypeContext` or is threaded beside it.
- Q2. What is the exact Lean shape of the regime-evolution relation replacing
  or generalizing `Regime.monotoneStep`? It should preserve old-tag
  monotonicity, permit only fresh selected extern-output additions at rule
  boundaries, account for any branch-local guard refinements, and remain usable
  by existing clean-under/agreement transport lemmas.
- Q3. Should the dynamic active-regime domain bridge be an explicit invariant
  threaded through proofs, or should it be derived from the regime-evolution
  relation when needed? The bridge needs to justify that active tags are
  surviving initial critical-input tags, surviving selected extern-output tags,
  or local branch refinements.
- Q4. What is the exact production-side obligation for extern-created predicates?
  The current direction keeps `valueConsistentWithRegime` as the downstream
  invariant and places production in the call-boundary layer. The remaining
  choice is how to encode the two-run obligation: extend `ExternBoundarySpec`
  with a regime-aware call field, or add a parallel call-boundary contract
  consumed by the extern application proof.
- Q5. What masked-invariant lemmas are needed when a selected extern call inserts a
  fresh selected extern-output tag into the active regime? The intended story is
  that `masked` remains proof-only and cannot drive typechecker de-poisoning,
  but the proof plumbing still needs precise preservation lemmas.
- Q6. Which proof surfaces must change, and can the changes be localized?
  `regimeConsistentWithCtx` and `tagEnvConsistentWithRegime*` thread through
  every `StepFR*` per-operator file. The current direction aims to keep concrete
  `StepFR` mostly unchanged, but this needs a scoping pass before
  implementation.
- Q7. What should the extern-id executable interface do when one selected
  extern id produces multiple output tags or is called multiple times? The
  current v1 interface assigns the same boolean to every generated output tag
  for that extern id. If the executable interface becomes part of an FR/CI
  boundary rather than a debugging aid, it may need occurrence-specific names,
  occurrence syntax, or a concrete-tag escape hatch.
