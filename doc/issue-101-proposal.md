## Issue #101: `PredSatLaws` is inconsistent due to tag reuse

Original issue: https://github.com/vzaliva/poison-lang/issues/101

---

## Summary

The counterexample in issue #101 demonstrates that `PredSatLaws` is inconsistent
because `match_iff` relates predicate satisfaction solely to a tag `k`, without
accounting for the predicate body that produced that tag. Since the system
permits reusing the same tag for different predicate bodies (e.g.,
`guardClosure k "a" (PExpr.bool true) []` and
`guardClosure k "a" (PExpr.bool false) []`), `match_iff` can be applied to two
different conditions that both match the same tag but evaluate to opposite
boolean values. This forces `predSat k μ v` to be both true and false
simultaneously, a contradiction.

---

## Root Cause

The `match_iff` law in `PredSatLaws` states:

```lean
match_iff : ∀ ... (k : Tag) ... (b : Bool),
  matchGuard condition Γ σ = .ok (k, deps) →
  terminatesTo ... condition ... (Value.bool b) →
  (∃ owning value v with guard tag k) →
  (b = true ↔ predSat k μ v)
```

The critical flaw: `predSat` depends only on the tag `k`, the memory `μ`, and
the owning value `v`. It does **not** reference the predicate body.

When the same tag `k` labels two guard closures with different predicate bodies
(e.g., `PExpr.bool true` vs `PExpr.bool false`), `matchGuard` succeeds for both
the condition `Expr.bool true` in one environment and `Expr.bool false` in
another. Applying `match_iff` to each yields:

- From the `true` condition: `predSat k μ v`
- From the `false` condition: `¬ predSat k μ v`

No `predSat` can satisfy both, so `PredSatLaws` is inconsistent.

---

## Proposed Solution: `wfTagUniqueness` Context Invariant

### Intent

Ensure that each tag `k` is associated with **at most one** guard-closure
descriptor across the entire typing context. Concretely, for a fixed tag `k`,
all occurrences of `Predicate.guardClosure k arg body ρ` that can arise from the
context (including those present inside captured environments of typing
closures) must agree on `arg`, `body`, and the captured typing environment `ρ`.
This restores consistency: if `k` has a unique intended guard
predicate, then `predSat k μ v` has a unique intended truth value.

### Approach

Define a well-formedness predicate `wfTagUniqueness` that asserts tag uniqueness
across all `QTyp`s in the context (both in `varEnv` and `memEnv`), including
those nested within function type closures. Add `wfTagUniqueness` as:
- a premise to `FaultRobustnessSpec` (initial well-formedness), and
- both a premise and a conclusion of `StepFR` (to support chaining across steps).

This provides the precondition needed for `match_iff` in `PredSatLaws` without
modifying `PredSatLaws` itself.

---

## Defining `wfTagUniqueness` (Deep Membership + Pairwise Property)

We want an invariant that is (i) strong enough to constrain tags anywhere in
the context, including inside captured closure environments, and (ii)
convenient in proofs, favouring inductive predicates that support inversion.

The most direct way to achieve this is to define:
- a *deep* inductive membership predicate `QTypInCtx qt ctx`, and then
- a generic pairwise context predicate `CtxPairwise F ctx` that quantifies over
  *any* two `QTyp`s picked via `QTypInCtx`.

### Key observation

`matchGuard` compares predicate bodies using `PExpr.equalWithEnvs pred_body ρ
conditionPExpr sCaptured ...`. Therefore, for tag uniqueness we must treat a
`guardClosure` as the full descriptor `(k, arg, body, ρ)` (not just `k` or
`body`).

### Deep membership predicates (inductive)

We first define when a `QTyp` is contained inside another `QTyp` by descending
into captured environments of typing closures.

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

/-- Deep membership of a `QTyp` in the context (`varEnv`/`memEnv` and their closures). -/
inductive QTypInCtx : QTyp → TypeContext → Prop where
  | inVar (ctx : TypeContext) (x : Name) (qt qtRoot : QTyp) :
      ctx.varEnv.lookup x = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInCtx qt ctx
  | inMem (ctx : TypeContext) (l : Loc) (qt qtRoot : QTyp) :
      ctx.memEnv.lookup l = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInCtx qt ctx
```

Remarks:
- `QTypInQTyp` makes the "deep" aspect explicit and re-usable.
- The `trans` constructor is what makes the definition truly recursive (you can
  step into one captured environment, then into closures inside it, and so on).

### Generic pairwise context property (inductive)

Now we can state "all `QTyp`s in the deep context are pairwise related by `F`"
in a single inductive wrapper:

```lean
inductive CtxPairwise (F : QTyp → QTyp → Prop) (ctx : TypeContext) : Prop where
  | intro :
      (∀ qt₁ qt₂, QTypInCtx qt₁ ctx → QTypInCtx qt₂ ctx → F qt₁ qt₂) →
      CtxPairwise F ctx
```

### Tag uniqueness as an instance of `CtxPairwise`

We define an inductive relation expressing compatibility of guard-closure tags:

```lean
inductive TagCompatible (qt₁ qt₂ : QTyp) : Prop where
  | intro :
      (∀ k arg₁ arg₂ body₁ body₂ ρ₁ ρ₂,
        qt₁.pred = Predicate.guardClosure k arg₁ body₁ ρ₁ →
        qt₂.pred = Predicate.guardClosure k arg₂ body₂ ρ₂ →
        arg₁ = arg₂ ∧ body₁ = body₂ ∧ ρ₁ = ρ₂) →
      TagCompatible qt₁ qt₂

inductive wfTagUniqueness (ctx : TypeContext) : Prop where
  | intro :
      CtxPairwise TagCompatible ctx →
      wfTagUniqueness ctx
```

This remains stronger than the minimal requirement (it is *global* across the
deep context), but it is proof-friendly: one typically inverts
`wfTagUniqueness`, then inverts `CtxPairwise` to obtain the usable
two-quantifier lemma.

Design note:
- Requiring `ρ₁ = ρ₂` is stronger than the minimal fix for the inconsistency
  (which only needs uniqueness of the predicate body for a given tag). The
  stronger constraint is justified by how `matchGuard` uses
  `PExpr.equalWithEnvs`, which makes the captured environment part of the
  matching semantics. If needed, this component can be weakened later (e.g., to
  `arg₁ = arg₂ ∧ body₁ = body₂` only), at the cost of having to show that the
  omitted environment information cannot affect applications of `match_iff`.

---

## Integration with Fault-Robustness Theorems

Add `wfTagUniqueness ctx` as a premise to `StepFR` and `FaultRobustnessSpec`.
This ensures the context is well-formed with respect to tag uniqueness, which
implies the precondition needed when applying `PredSatLaws.match_iff`.

```lean
def FaultRobustnessSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec)
    (ctx : TypeContext) (predSat : PredSat) : Prop :=
  ∀ (mode : LeanPoison.EvalMode) (μ₁ μ₂ : Memory) ...,
    ...
    wfTagUniqueness ctx →  -- NEW premise
    ...
    ∃ (θ₁' θ₂' : RealizationMap),
      wfExtendsMap θ₁ θ₁' ∧
      wfExtendsMap θ₂ θ₂' ∧
      observablesEqual obs θ₁' θ₂' cf₁ cf₂ o₁ o₂
```

Similarly for `StepFR`:

```lean
def StepFR ... : Prop :=
  ...
  wfTagUniqueness ctx →
  ...
  ∃ ctx', ... ∧ wfTagUniqueness ctx'
```

When `match_iff` is applied within the step proofs, `wfTagUniqueness ctx`
provides the guarantee that any two `QTyp`s in scope with the same tag have
identical guard-closure descriptors (predicate body *and* captured typing
environment), ruling out the counterexample scenario.

---

## Chaining consideration (why `StepFR` must conclude `wfTagUniqueness`)

To chain a fault-robustness proof across multiple typing/evaluation steps, we
need `wfTagUniqueness` both:
- as a **premise** (to justify uses of `PredSatLaws.match_iff` in the current
  step), and
- as a **conclusion** (to re-establish the invariant for the next step).

With this design, there is no need for a separate standalone lemma such as
`typecheck_preserves_tag_uniqueness`: that proof obligation is subsumed by the
`StepFR` proof itself, at exactly the point where the context is updated.

Even though this proposal does not add an explicit lemma connecting preservation
to `typecheck_nextTag_mono`, the underlying freshness argument remains the same:
typing allocates new guard tags from the `nextTag` supply and monotonicity
ensures that freshly allocated tags do not collide with tags already present in
the (deep) context. In the proposed organisation, this reasoning simply becomes
an internal sub-argument of the `StepFR` proof that produces the concluding
`wfTagUniqueness ctx'`.

---

## Summary of Changes

1. **Define deep membership predicates**:
   - `QTypInQTyp` (a `QTyp` occurs inside another `QTyp`, descending into
     captured environments of typing closures), and
   - `QTypInCtx` (a `QTyp` occurs in the deep context, starting from `varEnv` or
     `memEnv` and descending recursively).

2. **Define a generic pairwise context property** `CtxPairwise F ctx`, which
   states that `F` holds for any two `QTyp`s picked from the deep context via
   `QTypInCtx`.

3. **Instantiate `F` with tag uniqueness** via an inductive relation
   `TagCompatible`, which treats `guardClosure` as the full descriptor
   `(k, arg, body, ρ)` and enforces agreement when tags coincide.

4. **Define `wfTagUniqueness` as an inductive context invariant** by packaging
   `CtxPairwise TagCompatible ctx`.

5. **Integrate into theorems**:
   - add `wfTagUniqueness ctx` as a premise to `FaultRobustnessSpec`;
   - add `wfTagUniqueness` as both a premise and a conclusion of `StepFR` to
     support chaining without a separate preservation lemma.

6. **Establish initial uniqueness**: show the initial context built from
   `wfInputSpec` (or a strengthened variant) satisfies `wfTagUniqueness`.

This restores consistency to `PredSatLaws` by ensuring that within any
well-formed context, `predSat k μ v` has a unique intended meaning for each
tag `k`.
