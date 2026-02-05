## Issue #101: `PredSatLaws` is inconsistent due to tag reuse

Original issue: https://github.com/vzaliva/poison-lang/issues/101

**Dependency:**
[#106 — Extern declarations do not advance `nextTag`, allowing tag collision
with fresh tags](https://github.com/vzaliva/poison-lang/issues/106) must be
resolved first. This proposal assumes that extern declarations advance
`nextTag` past any introduced tag, so that `nextTag` monotonicity guarantees
freshly generated tags cannot collide with extern-supplied tags.

---

## Summary

The counterexample in issue #101 demonstrates that `PredSatLaws` is inconsistent
because `match_iff` relates predicate satisfaction solely to a tag `k`, without
accounting for the predicate body that produced that tag. Since `match_iff` is
universally quantified over all typing environments `σ` and `Γ`, the
counterexample constructs two different environments that both assign the same
tag `k` to different predicate bodies, applies `match_iff` to each, and derives
`predSat k μ v` and `¬ predSat k μ v` simultaneously — a contradiction.

---

## Root Cause

`PredSatLaws.match_iff` is universally quantified over `σ : VarTypeEnv` and
`Γ : MemoryTypeEnv` without any well-formedness constraint on these
environments. The counterexample exploits this by constructing:

- `σTrue` with `guardClosure k "a" (PExpr.bool true) []`
- `σFalse` with `guardClosure k "a" (PExpr.bool false) []`

and applying `match_iff` once with each. Since `predSat` depends only on `k`,
`μ`, and `v` (not on the predicate body), both applications produce
contradictory conclusions about `predSat k μ v`.

The fix must weaken `match_iff` by adding a precondition that rules out
environments where the same tag labels different predicate bodies.

---

## Proposed Solution

### Overview

1. **Define a deep tag-uniqueness predicate `tagUniqueEnvs σ Γ`** that descends
   into captured environments of typing closures. This single predicate is used
   everywhere: as the `match_iff` precondition, as the `StepFR` invariant
   (via a `wfTagUniqueness ctx` wrapper), and at the top-level theorem.

2. **Add `tagUniqueEnvs σ Γ` as a precondition to `match_iff`** in
   `PredSatLaws`, restoring satisfiability.

3. **Make the intended StepFR usage explicit**: in FR proofs, invoke `match_iff`
   only through a wrapper specialised to a fixed `ctx` (same `ctx.memEnv` and
   `ctx.varEnv` for both runs).

4. **Add `wfTagUniqueness` as a premise and conclusion of `StepFR`** (the
   `def StepFR` in `FaultRobustnessProofs.lean`) so the invariant is available
   at each step and preserved across chaining.

5. **At the top level, add `wfTagUniqueness ctx` as a separate premise** of
   `TypeSystemEnforcesFaultRobustness_spec`, alongside the existing
   `ctxMatchesInputSpec` (which is left unchanged).

6. **Enforce tag-compatibility at all extern insertion points** (not only
   `typecheckExternVal`): extern value declarations, extern effect specs, and
   extern return specs during extern function application.

### Why deep checking is needed

`matchGuard` itself only examines top-level predicates in the `σ` and `Γ`
passed to it. One might therefore expect that a shallow uniqueness property
suffices. However, when `applyFnTClosure` processes a `FnTClosure.regular`
closure, it replaces the current `varEnv` with the closure's captured
environment:

```lean
let envMap := VarTypeEnv.ofCaptured env
let env' := VarTypeEnv.update envMap x argQt
let ctx'' := { ctx with ..., memEnv := result2.memEnv', varEnv := env', ... }
```

If the function body invokes `matchGuard`, it operates on `(env',
result2.memEnv')`. A shallow invariant on the outer context's `varEnv` says
nothing about the restored captured environment. A deep invariant that descends
into closures stored in `varEnv` and `memEnv` ensures that any tag in the
captured environment is already constrained pairwise against all other tags in
the deep context — including those in the current `memEnv`.

Since we must prove and propagate the deep property through `StepFR` anyway (to
handle function application), we use the same deep `tagUniqueEnvs` everywhere —
including as the `match_iff` precondition. The deep property is strictly
stronger than a shallow one, so this is sound; and having a single definition
eliminates the need for a bridge lemma.

### Why this matches StepFR usage

In `StepFR`, both runs are checked against the same static typing context `ctx`.
So the two applications of `match_iff` in mode proofs should use the same
`(ctx.memEnv, ctx.varEnv)`. The proposal makes this explicit by introducing a
wrapper lemma for proof scripts, instead of calling the raw field
`hpredlaws.match_iff` directly with arbitrary environments.

---

## Definitions

### Deep membership predicates

```lean
/-- Extract the captured typing environment from closures. -/
def fnCapturedEnv : FnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ _ ρ => ρ

def pfnCapturedEnv : PFnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ ρ => ρ

/-- Deep membership of `qtInner` inside `qtOuter`. -/
inductive QTypInQTyp : QTyp → QTyp → Prop where
  | self (qt : QTyp) :
      QTypInQTyp qt qt

  | in_arrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List FnTClosure)
      (tcl : FnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.arrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ fnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter

  | in_parrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List PFnTClosure)
      (tcl : PFnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.parrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ pfnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter

  | trans (qt₁ qt₂ qt₃ : QTyp) :
      QTypInQTyp qt₁ qt₂ →
      QTypInQTyp qt₂ qt₃ →
      QTypInQTyp qt₁ qt₃
```

Remarks:
- `QTypInQTyp` makes the "deep" aspect explicit and reusable.
- The `trans` constructor makes the definition truly recursive: one can step
  into a captured environment, then into closures inside it, and so on.

### Deep membership in environments

Parameterised by `(σ, Γ)` rather than `TypeContext`, so the same predicate can
serve both as a `match_iff` precondition (which receives `σ` and `Γ` directly)
and as the context-level invariant (via the `wfTagUniqueness` wrapper).

```lean
/-- Deep membership of a QTyp in environments σ and Γ (descending into
    closures). -/
inductive QTypInEnvs : QTyp → VarTypeEnv → MemoryTypeEnv → Prop where
  | inVar (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (x : Name) (qt qtRoot : QTyp) :
      σ.lookup x = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ
  | inMem (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (l : Loc) (qt qtRoot : QTyp) :
      Γ.lookup l = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ
```

### Generic pairwise environment property

```lean
inductive EnvsPairwise (F : QTyp → QTyp → Prop)
    (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Prop where
  | intro :
      (∀ qt₁ qt₂, QTypInEnvs qt₁ σ Γ → QTypInEnvs qt₂ σ Γ → F qt₁ qt₂) →
      EnvsPairwise F σ Γ
```

### Tag uniqueness

```lean
inductive TagCompatible (qt₁ qt₂ : QTyp) : Prop where
  | intro :
      (∀ k arg₁ arg₂ body₁ body₂ ρ₁ ρ₂,
        qt₁.pred = Predicate.guardClosure k arg₁ body₁ ρ₁ →
        qt₂.pred = Predicate.guardClosure k arg₂ body₂ ρ₂ →
        arg₁ = arg₂ ∧ body₁ = body₂ ∧ ρ₁ = ρ₂) →
      TagCompatible qt₁ qt₂

/-- Deep tag uniqueness on environments: all guard closures reachable from σ
    and Γ (including inside captured environments of typing closures) with the
    same tag have identical descriptors (arg, body, capturedEnv). -/
def tagUniqueEnvs (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Prop :=
  EnvsPairwise TagCompatible σ Γ

/-- Context-level wrapper for use in StepFR. -/
def wfTagUniqueness (ctx : TypeContext) : Prop :=
  tagUniqueEnvs ctx.varEnv ctx.memEnv
```

This does not mention `InputSpec` and can be used directly in step-level proofs.

Design note: requiring `ρ₁ = ρ₂` is stronger than the minimal fix for the
inconsistency (which only needs uniqueness of the predicate body for a given
tag). The stronger constraint is justified by how `matchGuard` uses
`PExpr.equalWithEnvs`, which makes the captured environment part of the
matching semantics. If needed, this component can be weakened later.

**Proof complexity note.** The deep relation design (`QTypInQTyp` with
transitive closure + global pairwise `EnvsPairwise`) is expressive but
proof-intensive. Expect the need for inversion and transport lemmas (e.g.
monotonicity of `QTypInEnvs` under environment extension, and preservation
of `EnvsPairwise` under entry insertion) before individual `StepFR` branches
become tractable.

---

## Modification to `PredSatLaws`

Add `tagUniqueEnvs σ Γ` as a precondition to `match_iff`. Since
`tagUniqueEnvs` is the deep predicate (descending into closures), this is
stronger than the minimal fix but matches what we prove and propagate anyway:

```lean
structure PredSatLaws (predSat : PredSat) : Prop where
  match_iff : ∀ (mode : LeanPoison.EvalMode) (condition : Expr)
                  (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
                  (k : Tag) (deps : Deps)
                  (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (addr : Address)
                  (pm : Bool) (cfg : Config) (v : Value) (b : Bool),
    tagUniqueEnvs σ Γ →  -- NEW precondition
    matchGuard condition Γ σ = .ok (k, deps) →
    terminatesTo mode condition
      { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm } cfg
      (Value.bool b) →
    ( (∃ (x : Name) (qt : QTyp), ...) ∨ (∃ ..., ...) ) →
    (b = true ↔ predSat k μ v)

  mem_monotone : ...  -- unchanged
```

Then define a StepFR-oriented wrapper lemma:

```lean
lemma match_iff_in_ctx
    (h_laws : PredSatLaws predSat)
    (ctx : TypeContext)
    (h_wf : wfTagUniqueness ctx)
    ... :
    matchGuard condition ctx.memEnv ctx.varEnv = .ok (k, deps) →
    ...
    (b = true ↔ predSat k μ v) := by
  exact h_laws.match_iff ... h_wf ...
```

This enforces the intended discipline: FR proofs apply `match_iff` against a
single fixed context, rather than independently choosing unrelated `σ`/`Γ`.
Since `wfTagUniqueness ctx` unfolds to `tagUniqueEnvs ctx.varEnv ctx.memEnv`,
the precondition is discharged directly — no bridge lemma is needed.

---

## Integration with Fault-Robustness Theorems

### `StepFR` (in `FaultRobustnessProofs.lean`)

Add `wfTagUniqueness ctx` as both a **premise** and a **conclusion**:

```lean
def StepFR ... : Prop :=
  ...
  wfTagUniqueness ctx →       -- premise: needed to invoke match_iff
  ...
  ∃ ctx', ... ∧
    wfTagUniqueness ctx'       -- conclusion: needed for chaining
```

When step proofs invoke `match_iff`, they use `match_iff_in_ctx` and discharge
`tagUniqueEnvs ctx.varEnv ctx.memEnv` from the `StepFR` premise (which provides
`wfTagUniqueness ctx`). The conclusion re-establishes the invariant for the
post-context, which serves as the premise of the next step.

**Function application.** When `applyFnTClosure` restores a closure's captured
environment, the inner context's tag uniqueness requires that the captured
`varEnv` is tag-compatible with the current `memEnv`. Two cases arise:

- **Pre-existing closures** (already in `ctx.varEnv` or `ctx.memEnv`): their
  captured environments are reachable via `QTypInEnvs` from the outer context
  (through `QTypInQTyp.in_arrow`/`in_parrow` and `trans`), so tag uniqueness
  follows from the outer `wfTagUniqueness ctx`.

- **Closures produced during the current step** (e.g. typing `e1` in
  `app e1 e2` yields a function type with fresh closures): these closures
  capture an internal `varEnv` that may include bindings introduced during
  typing of `e1`, not present in the outer `ctx.varEnv`. Tag uniqueness for the
  inner context cannot be derived from `wfTagUniqueness ctx` alone. To handle
  this, the **typechecker enforces compatibility at closure application time**:
  in `applyFnTClosure` (and `applyPFnTClosure`), after restoring the captured
  environment and before typing the body, check that the restored `varEnv` has
  no tag conflicts with the current `memEnv` (using `tagCompatibleWithEnvs`).
  If a conflict is detected, reject typing.   In `StepFR` proofs, the fact that
  typing succeeded implies the check passed, giving `tagUniqueEnvs restoredEnv
  currentMemEnv` for the inner context directly. No additional changes to
  `StepFR`'s signature are needed beyond the `wfTagUniqueness` premise and
  conclusion already proposed.

This is the same chain used by:
- `StepFR_IH` (induction hypothesis alias),
- `TypeSystemEnforcesFaultRobustness_step_spec`,
- the IO-free proof section `TypeSystemEnforcesFaultRobustness_IOFree_proof`.

The conclusion is necessary because extern declarations (`typecheckExternVal`)
can introduce new `guardClosure` predicates with user-supplied tags into the
context. Preservation holds provided:
- the typechecker enforces the tag-conflict check proposed below (rejecting any
  extern that would introduce a conflicting tag), and
- extern declarations advance `nextTag` past any introduced tag (see
  [#106](https://github.com/vzaliva/poison-lang/issues/106)), so that
  subsequent `generateFreshTag` calls produce tags guaranteed not to collide
  with extern-supplied ones.

If both conditions hold and `wfTagUniqueness ctx` holds before the step, then
`wfTagUniqueness (ctxAfter ctx res)` holds after. The remaining operations
(propagation and degradation to `guardOnly` via `joinPredicates`) trivially
preserve tag uniqueness.

### `FaultRobustnessSpec` (in `FaultRobustness.lean`)

Do **not** rely on `wfInputSpec` alone to derive uniqueness for the whole
context. `ctxMatchesInputSpec` permits extra (non-spec) bindings, so spec-only
uniqueness is insufficient by itself.

Keep `ctxMatchesInputSpec` **unchanged** and add `wfTagUniqueness ctx` as a
**separate premise**. The two properties are orthogonal:

- **Tag hygiene** (existing conjuncts 3 and 4 of `ctxMatchesInputSpec`):
  "non-spec entries cannot reuse spec tags." This is needed for the bridge
  lemma `consistentRegimeSpec_implies_consistentWithRegime`, which must
  identify context entries with regime-interpreted tags as spec entries (to
  transfer spec-level regime consistency to context-level regime consistency).
  Tag uniqueness cannot replace this: `locsRegime` depends on the runtime value
  at a *specific location*, and two entries with the same tag at different
  locations may have different runtime values.

- **Tag uniqueness** (`wfTagUniqueness`): "same tag implies same guard-closure
  descriptor." This is needed for `match_iff` in `PredSatLaws`, preventing the
  counterexample from issue #101.

```lean
def TypeSystemEnforcesFaultRobustness_spec
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :=
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      wfTagUniqueness ctx →  -- NEW separate premise
      wfTypeContext ctx →
      ...
```

Preservation should be handled **inside `StepFR` proofs**, not as a separate
global theorem over `typecheck`.

Concretely, each `StepFR` branch that transforms context (especially extern
insertion branches) must produce the concluding `wfTagUniqueness (ctxAfter ctx
res)` from:
- the incoming `wfTagUniqueness ctx`, and
- local tag-compatibility facts discharged at the insertion point.

The `wfTagUniqueness ctx` premise must also be added to the IO-free mirror
definitions and bridge lemmas:
- `TypeSystemEnforcesFaultRobustness_spec_ioFree` (definition,
  `FaultRobustnessProofs.lean`),
- `TypeSystemEnforcesFaultRobustness_spec_implies_ioFree` (bridge lemma),
- `TypeSystemEnforcesFaultRobustness_impl_IOFree` (impl theorem).

The top-level statement remains `TypeSystemEnforcesFaultRobustness_spec`
(in `FaultRobustness.lean`).

---

## Tag Uniqueness as a Well-Formedness Condition

Tag uniqueness is part of what it means for a programme to be well-typed — not
a defensive check. A programme that reuses the same tag `k` for two different
predicate bodies is *ill-formed*, just as a programme that applies an integer
as a function is ill-typed. The typechecker rejects such programmes as part
of typing.

This gives the standard type-safety structure:
- **Well-formedness**: `wfTagUniqueness ctx` holds for the initial context.
- **Preservation**: if `wfTagUniqueness ctx` holds and
  `typecheckExpr ctx e fuel = .ok res`, then
  `wfTagUniqueness (ctxAfter ctx res)` holds.
- **Usage**: `StepFR` proofs derive `tagUniqueEnvs` from the premise, and the
  typing success guarantees it for the post-context.

The typing rules that make preservation provable are described below.

### Extern declarations

Extern syntax (`externVal`, `externFn`, `externPfn`) can introduce
user-supplied tags via `SyntaxPredicate.guardClosure k arg body`. A programme
that assigns the same tag to different predicate bodies is ill-formed.

When `attachVarEnvToPredicate` produces a
`Predicate.guardClosure k arg body ρ`, the typechecker verifies compatibility
against all tags reachable from the current context. If a conflict is found,
typing fails.

This check must verify compatibility against **all** entries reachable from the
deep context, not only top-level ones. A tag `k` might exist only inside nested
captured environments (e.g. if a variable carrying tag `k` was shadowed after a
closure captured it). In that case a top-level-only scan would pass vacuously
whilst the deep invariant is violated.

Since `VarTypeEnv` and `MemoryTypeEnv` are finite and closures have finite
captured environments, the set of all `(k, arg, body, ρ)` descriptors reachable
from the current context can be computed by recursively descending into closure
types. The check is: extract the tag from the new predicate, collect all
existing descriptors with that tag from the deep context, and verify they agree.

Sketch: define a decidable deep compatibility check.

```lean
/-- Collect all guard-closure descriptors reachable from a QTyp. -/
def collectTagDescriptors (qt : QTyp) : List (Tag × Name × PExpr × CapturedVarEnv)

/-- Collect all guard-closure descriptors reachable from σ and Γ. -/
def collectAllTagDescriptors (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
    : List (Tag × Name × PExpr × CapturedVarEnv)

/-- Check whether a predicate's tag conflicts with any descriptor
    reachable from σ and Γ. Returns true if no conflict. -/
def tagCompatibleWithEnvs (pred : Predicate) (σ : VarTypeEnv)
    (Γ : MemoryTypeEnv) : Bool :=
  match pred with
  | Predicate.guardClosure k arg body ρ =>
      (collectAllTagDescriptors σ Γ).all fun (k', arg', body', ρ') =>
        k != k' || (arg == arg' && body == body' && ρ == ρ')
  | _ => true
```

Required call sites (high-priority):

1. `typecheckExternVal` after `surfaceSpecToQTyp` produces `qt`.
2. `applyFnTClosure` for extern closures:
   - each `effectSpecToQTyp` result before writing to `memEnv`
   - `returnSpecToQTyp` result before returning / applying return effects
3. `applyPFnTClosure` for extern pure closures:
   - `returnSpecToQTyp` result before returning.
4. `applyFnTClosure` / `applyPFnTClosure` for **all** closures (regular and
   extern): after restoring the captured environment, verify that each
   predicate in the restored `varEnv` is compatible with the current `memEnv`.
   A programme where a closure's captured tag conflicts with a tag introduced
   after capture is ill-formed (the tag's meaning is ambiguous at the
   application site).

Note: for call sites 2–3, which process effects in a loop (e.g.
`for effect in effects`), the check must run against the **evolving**
post-insertion `memEnv`, not the original `ctx.memEnv`. Each effect may insert
a new predicate, and subsequent effects must be checked against the state that
includes all prior insertions.

Minimal sketch:

```lean
def ensureTagCompatible (pred : Predicate) (σ : VarTypeEnv)
    (Γ : MemoryTypeEnv) : TypecheckM Unit := do
  if !tagCompatibleWithEnvs pred σ Γ then
    throw s!"Tag conflict: tag already in use with a different predicate body"
  pure ()
```

In `StepFR` proofs, the fact that typing succeeded implies all compatibility
checks passed. Each `StepFR` branch that transforms the context derives
`wfTagUniqueness (ctxAfter ctx res)` from the incoming `wfTagUniqueness ctx`
and the local compatibility facts discharged by the typing rules.

**Note on fresh tags and `nextTag`:**
Once [#106](https://github.com/vzaliva/poison-lang/issues/106) is resolved
(extern declarations advance `nextTag` past any introduced tag), `nextTag`
monotonicity guarantees that freshly generated tags cannot collide with
extern-supplied tags. The `tagCompatibleWithEnvs` check at extern insertion
points serves as defence-in-depth and as the proof-level mechanism by which
`StepFR` establishes `wfTagUniqueness` for the post-context.

---

## Summary of Changes

1. **Define deep membership predicates**:
   - `QTypInQTyp` (a `QTyp` occurs inside another `QTyp`, descending into
     captured environments of typing closures), and
   - `QTypInEnvs` (a `QTyp` occurs in environments `σ`/`Γ`, starting from
     top-level entries and descending recursively via `QTypInQTyp`).

2. **Define a generic pairwise environment property** `EnvsPairwise F σ Γ`,
   which states that `F` holds for any two `QTyp`s picked from the deep
   environments via `QTypInEnvs`.

3. **Instantiate with `TagCompatible`** and define **`tagUniqueEnvs σ Γ`** as
   `EnvsPairwise TagCompatible σ Γ`. This single deep predicate is used
   everywhere.

4. **Define `wfTagUniqueness ctx`** as `tagUniqueEnvs ctx.varEnv ctx.memEnv`
   (a wrapper for use with `TypeContext`).

5. **Add precondition to `match_iff`** in `PredSatLaws`: require
   `tagUniqueEnvs σ Γ`.

6. **Use a `match_iff_in_ctx` wrapper in FR proofs** so calls are tied to a
   fixed `ctx` (same `ctx.memEnv`/`ctx.varEnv` across both runs).

7. **Add `wfTagUniqueness` to `StepFR`** as both a premise and a conclusion.
   This supports invocation and chaining, including across function application
   boundaries.

8. **Add `wfTagUniqueness ctx` as a separate premise** at the top level
   (`TypeSystemEnforcesFaultRobustness_spec`), alongside the unchanged
   `ctxMatchesInputSpec`. Also add to the IO-free mirror
   (`TypeSystemEnforcesFaultRobustness_spec_ioFree`) and its bridge lemmas.
   Propagate through the `StepFR` premise/conclusion chain; do not introduce
   a standalone global `typecheck`-preservation theorem.

9. **Add typechecker enforcement** at all points where tag conflicts could
   arise:
   - extern value declarations (`typecheckExternVal`)
   - extern effect specs and return specs in extern function application
     (`applyFnTClosure`, `applyPFnTClosure`), checking against the evolving
     post-insertion `memEnv`
   - closure application (all closures, not only extern): check restored
     captured environment against current `memEnv` before typing the body
