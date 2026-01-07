## Closure equality issue in fault-robustness proofs

This note documents a specification-level mismatch that blocks the `fn` and `pfn` cases in
`LeanProofs/FaultRobustnessProofs.lean` (currently around the `TypeSystemEnforcesFaultRobustness_stepW` proof).

The core problem is that the current fault-robustness agreement relation treats **clean non-references**
as agreeing only when they are **literally equal**. Since function values are closures (and closures
capture a runtime environment), this forces **syntactic equality of closures**, including equality of
captured environments. That is far stronger than what the step invariant (`agreeOnClean`) provides.


## Where it manifests

In `LeanProofs/FaultRobustnessProofs.lean`, the `StepFRW` post-condition includes:

- preservation of `agreeOnClean` for the post-context, and
- `resultAgreesIfClean … res.qualType o₀ o₁`.

The cases left as `sorry` at the time of writing are the branches:

- `Expr.fn …` and `Expr.pfn …` (closures are values).


## The specification that forces literal closure equality

### Step result agreement when “clean under the regime”

The step theorem requires agreement of the returned values whenever the returned qualified type is
clean-under-\(R\) (schematically):

```lean
def resultAgreesIfClean … (qt : QTyp) (o₀ o₁ : Value) : Prop :=
  qtypCleanUnder R qt → agreeValueUnder predSat R μ₀ μ₁ θ₀ θ₁ qt o₀ o₁
```

### `agreeValueUnder` for clean non-references is literal equality

The inductive definition `agreeValueUnder` contains a clause:

```lean
| clean_eq_nonref
    (hpoison : qt.poison = false)
    (hnotref : ¬ (∃ t ls, qt.etyp = ETyp.ref t ls))
    (hagree : v₁ = v₂) :
    agreeValueUnder … qt v₁ v₂
```

Therefore, for any clean qualified type whose `etyp` is not a reference type, agreement *reduces to*
`v₁ = v₂`.

Since arrow types (`ETyp.arrow …` and `ETyp.parrow …`) are not reference types, **clean functions are
forced to agree by literal equality of values**.


## Why closures make this unprovable with the current invariant

### Operational semantics: closures capture the entire runtime variable environment

In the big-step evaluator (`LeanPoison/BigStep.lean`), function abstraction returns a closure value
that captures `config.varEnv`:

```lean
| Expr.fn x _ body _ =>
  let closure := Value.closure x body config.varEnv
  return .success config closure
| Expr.pfn x _ body _ =>
  let closure := Value.peClosure x body config.varEnv
  return .success config closure
```

So the closure captures the entire current runtime variable environment (as a list of bindings).

### Invariant: `agreeOnClean` does *not* yield full environment equality

The step invariant `agreeOnClean` only requires agreement for **context entries that are clean-under-\(R\)**:

- clean locations in `ctx.memEnv`, and
- clean variables in `ctx.varEnv`.

It deliberately leaves **non-clean** (poisoned / not de-poisoned) entries unconstrained.

Consequently, two runs may legally differ on poisoned variables (and their values). Nonetheless, the
operational semantics *captures those variables into the closure environment*.

Therefore, the two closure values returned by evaluating `fn`/`pfn` need not be propositionally equal,
because closure equality in Lean is structural and includes equality of the captured environment list.

This is the fundamental mismatch:

- the spec demands **closure equality** when the function result is clean,
- but the available hypotheses only provide **agreement on clean context entries**, not full equality of
  the runtime environments captured into closures.


## Why `LeanProofs/Equality.lean` does not (yet) resolve the proof

`LeanProofs/Equality.lean` provides `LawfulBEq` and `DecidableEq` instances, including for `Value`.
For closures, boolean equality (`beqValue`) is *structural*:

- same parameter name,
- same body expression, and
- same captured runtime environment list (structurally).

The file proves soundness: `(v₁ == v₂) = true → v₁ = v₂`.

This is useful infrastructure, but it does not address the fault-robustness mismatch:

- The fault-robustness spec requires **propositional equality** (`v₁ = v₂`) for clean non-references.
  Having a `BEq` instance does not weaken that requirement.
- Moreover, we do not have premises that yield `(v₁ == v₂) = true` for closures, and even if we did,
  the boolean comparison still demands full captured-environment equality. That is precisely what
  `agreeOnClean` does not provide.

Separately, `Equality.lean` also documents an important design choice at the type level:
`beqETypSignature` is a **special-purpose** comparison used by the type checker. It deliberately ignores
closure contents when comparing arrow/parrow types, because full structural equality of closure lists is
too strict for type-checking, and (by design) it is not a sound notion of equality for function types.
Accordingly, `beqETypSignature` should not be changed or repurposed to support fault-robustness proofs.
Any additional equality/relational structure needed for closures should be introduced as a *new* definition
(for example, by adding arrow/parrow cases to `agreeValueUnder`, or by defining a separate closure-agreement
predicate), rather than by strengthening `beqETypSignature`.


## Proposed fix: make StepFRW the core of closure agreement

The specification-level fix is to stop treating arrow/parrow values as “just another non-reference” in `agreeValueUnder`.
Instead, we introduce a dedicated closure-agreement predicate `closuresAgreeUnder` and make it **use `StepFRW` as the
engine** for reasoning about closure bodies.

This is more principled than trying to compare closures directly, because `StepFRW` already encapsulates exactly what the
fault-robustness development is built to prove: a two-run property of evaluation that preserves `agreeOnClean` and forces
agreement of clean results.

### Mutual recursion (fuel-indexed) to avoid circularity

There is an unavoidable dependency cycle:

- `StepFRW` concludes return-value agreement via `agreeValueUnder`.
- For arrow/parrow types, `agreeValueUnder` should delegate to `closuresAgreeUnder` (rather than demanding `v₀ = v₁`).
- `closuresAgreeUnder` wants to justify behavioural agreement of closures by invoking `StepFRW` on the closure body.

To make this acceptable to Lean, we use a **fuel index** as a step index and make the *step theorem itself* fuel-indexed.
Concretely, within `LeanProofs/FaultRobustnessProofs.lean` we do not maintain a separate “indexed copy” alongside an unindexed `StepFRW`:
we refactor the existing (local) `StepFRW` into an indexed form `StepFRW k` (where \(k\) is the **type-checking fuel**),
and define the corresponding fuel-indexed agreement relations it depends on.

In other words, the mutually recursive core becomes:

- `StepFRW k` (a world-indexed step theorem parameterised by type-checking fuel \(k\)),
- `agreeValueUnder k`, and
- `closuresAgreeUnder k`,

with the invariant that recursive calls always go to a strictly smaller index. This aligns with the implementation:
typing a closure body at application time consumes fuel, so body typing naturally happens at a smaller fuel than the outer
typing call.

**Fuel alignment note:** the index \(k\) here is the *type-checking* fuel (the `fuel` argument passed to `typecheck`).
The evaluator’s fuel is existential inside `terminatesToW`; we do not need to index on evaluation fuel to break the
definitional cycle between `StepFRW` and closure agreement.

### From fuel-indexed `StepFRW` to the exported step theorem (`StepFR`)

`StepFRW` is only used as an intermediate lemma in this file: it is immediately converted to the non-world step theorem
`StepFR` (and then to the top-level fault-robustness statement). After refactoring `StepFRW` to be fuel-indexed, we simply
generalise that one conversion lemma to accept an explicit fuel parameter:

- `StepFR_of_StepFRW (k : Nat) : StepFRW k ctx R e res predSat → StepFR ctx R e res predSat`.

No wrapper is needed. In `TypeSystemEnforcesFaultRobustness_step`, the `fuel` argument is already in scope (from the typing
premise `typecheck ctx e fuel = .ok res`), so we instantiate `k := fuel` and apply the same erasure argument as before.

### Sketch: `agreeValueUnder k` delegates arrow/parrow to `closuresAgreeUnder k`

Keep the existing cases of `agreeValueUnder` for base types and references.
Replace the “clean non-reference implies equality” behaviour for arrow/parrow results with an arrow/parrow case that requires
`closuresAgreeUnder k`.

In practice, this also requires ensuring that the existing `clean_eq_nonref` case does **not** continue to apply to
arrow/parrow types (since arrows are non-references). One can enforce this by strengthening its side condition so that it
excludes function types, or by otherwise arranging that the arrow/parrow case is the one used for function results.

Intuitively:

- for non-function, non-reference types: clean results still force literal equality;
- for references: agreement remains via realisation maps and locsets (as in the current development);
- for functions: agreement is **behavioural**, defined by `closuresAgreeUnder k`.

Here “behavioural” means: two closure values agree not because their captured environments are literally equal, but because
whenever they are applied to *related arguments*, their bodies can be shown to produce related outcomes under the existing
two-run step theorem.

The word “related” is **regime-dependent**: the minimal requirement is that if the argument’s qualified type is
clean-under-\(R\) (i.e. `qtypCleanUnder R qt_arg` holds), then the two argument values satisfy `agreeValueUnder k_arg` at
`qt_arg` for some strictly smaller index \(k_{arg} < k\). If `qt_arg` is not clean-under-\(R\), then no equality
obligation is imposed by the step invariant, and the argument values may be unconstrained.

From there, `StepFRW k` yields return agreement in the same style: it provides `agreeValueUnder k` for the body’s return value
whenever the inferred return qualified type is clean-under-\(R\). For base (non-reference, non-function) return types,
`agreeValueUnder` reduces to literal equality by inversion (via the `clean_eq_nonref` constructor); for reference returns,
it yields the appropriate locset/realisation agreement; and for functional returns it recurses via `closuresAgreeUnder k`.

### Sketch: invoking `StepFRW` from `closuresAgreeUnder`

Fix a regime `R` and predicate-satisfaction relation `predSat`. Closure agreement is always *relative to the same* `R`:
the regime is a run-level parameter that models which input guard tags are true/false, so it does not change when we
enter a closure body.

#### Runtime closures versus typing closures (and why both appear)

It is important to keep two distinct notions separate:

- **Runtime closures** are values produced by evaluation, of the form `Value.closure x body ρcap` or `Value.peClosure x body ρcap`,
  where `ρcap : VarEnv` is a list of *runtime* bindings `(Name × Value)`.
- **Typing closures** are a type-system device stored inside arrow/parrow enriched types (the closure list in `ETyp.arrow` / `ETyp.parrow`),
  of the form `FnTClosure.regular x body σcap` or `PFnTClosure.regular x body σcap`, where `σcap : VarTypeEnv` (captured) is a list of
  *typing* bindings `(Name × QTyp)`.

The **problem** diagnosed earlier is purely about runtime closures (they capture the whole runtime environment, but `agreeOnClean` only constrains
clean entries). Typing closures are not the source of the mismatch; they are needed in the *fix* because `StepFRW` is a statement about evaluating an
expression under a typing context, so to invoke it on a closure body we must supply the appropriate typing context at application time.

For the `fn` / `pfn` branches specifically, the typing-closure list introduced by `typecheckFn` / `typecheckPfn` has **exactly one element**. More generally,
arrow/parrow types may carry typing-closure lists of any length (for example, after control-flow joins); the proposal below therefore treats the list generically.
This is always a statement about the *type-level* typing-closure list inside `ETyp.arrow` / `ETyp.parrow`, not about runtime values: at runtime, evaluation
produces a single closure value.

For an impure function value, the runtime closure has the shape:

- `v₀ = Value.closure x₀ body ρcap₀`
- `v₁ = Value.closure x₁ body ρcap₁`

In the `fn`/`pfn` step cases, both runs evaluate the same syntactic abstraction, so the binders coincide
(\(x₀ = x₁\)) and the stored bodies coincide as well. The distinction only matters when generalising closure agreement
beyond those cases.

and its *type* is an arrow whose typing-closure list contains at least one typing closure whose binder/body match the runtime closure, providing a captured typing
environment for the body:

- `tcl = FnTClosure.regular x body σcap` with `tcl ∈ tcls`

In the `fn` / `pfn` cases, `tcls` has exactly one element, so this witness is unique. When `tcls` is non-singleton, the witness is not an arbitrary “choice”:
it must match the actual runtime closure (binder/body), and is therefore determined by the runtime value (up to benign ambiguity if multiple typing closures have the
same binder/body).

Define `closuresAgreeUnder k … qt_fun v₀ v₁` so that, when the closures are “used”, we first select such a typing-closure witness from the list and then
**instantiate** `StepFRW` for the (matched) body:

1. **Handle the argument**: quantify over an argument qualified type `qt_arg` and runtime values `arg₀ arg₁`.
   Require the standard interface condition (as in the type checker) that `isSubtype st1 qt_arg` holds, and require:
   if `qtypCleanUnder R qt_arg`, then `agreeValueUnder k_arg … qt_arg arg₀ arg₁` at some strictly smaller index \(k_{arg} < k\).
   (This matches exactly what is needed to establish `agreeOnClean` for the closure body’s typing context.)
2. **Replace the runtime environment by the captured one**: to evaluate the body, we use exactly the operational
   mechanism of closure application: extend the captured environments with the parameter binding:

   - `ρ₀' := VarEnv.update ρcap₀ x₀ arg₀`
   - `ρ₁' := VarEnv.update ρcap₁ x₁ arg₁`

3. **Select a typing-closure witness and build the typing context**: choose `tcl ∈ tcls` of the form `FnTClosure.regular x body σcap` whose binder and body
   match the two runtime closures (since both runs evaluate the same `fn`/`pfn`, we have \(x = x₀ = x₁\) and bodies are syntactically equal). Let `ctx_body` be the context under which the body is
   type-checked at application time. Its variable typing environment is the captured one `σcap` extended with the parameter binding (as constructed by the type checker);
   its memory and tag environments come from the call site typing state.
4. **Invoke `StepFRW`**: choose some fuel `k_body < k` such that `typecheck ctx_body body k_body = .ok res_body`,
   and apply `StepFRW k_body ctx_body R body res_body predSat` to the two evaluations of `body` starting from
   var-envs `ρ₀'` and `ρ₁'` (and whatever memories/realisation maps the caller supplies, subject to the standard
   `StepFRW` premises such as `runtimeInstantiatesCtx` and `agreeOnClean` for `ctx_body`).

At this point the key “bridge” obligation becomes explicit:

- to invoke `StepFRW k_body ctx_body …`, we must establish `agreeOnClean predSat R ctx_body μ₀ ρ₀' θ₀ μ₁ ρ₁' θ₁`.

This splits cleanly:

- **Parameter binding**: the only new variable entry in `ctx_body.varEnv` is the parameter binder (`x`, with \(x = x₀ = x₁\) in the `fn`/`pfn` cases)
  bound to (a variant of) `qt_arg`.
  If that parameter binding is clean-under-\(R\), the required agreement is exactly the assumption from step (1).
- **Captured variables**: for every captured variable `(y, qt_y)` in `σcap`, if `qt_y` is clean-under-\(R\), then the required
  runtime agreement between `ρcap₀.lookup y` and `ρcap₁.lookup y` is inherited from the *outer* `agreeOnClean` at function-definition
  time. For poisoned variables, the values in `ρcap₀` and `ρcap₁` may differ — this is expected and does not violate `agreeOnClean`,
  which imposes no constraint on non-clean entries.
- **Memory/tag environments**: `ctx_body.memEnv` and `ctx_body.tagEnv` come from the call site; the caller supplies the corresponding
  `agreeOnClean` and instantiation premises for those components when `closuresAgreeUnder k` is used to justify an application.

For readability, one can summarise the intended quantifier structure as the following schematic (not a final Lean definition):

```text
closuresAgreeUnder k … qt_fun v₀ v₁ :=
  ∃ tcl ∈ tcls, tcl = FnTClosure.regular x body σcap ∧ (binder/body match v₀ and v₁),
    ∀ qt_arg arg₀ arg₁,
      isSubtype st1 qt_arg →
      (qtypCleanUnder R qt_arg → agreeValueUnder k_arg … qt_arg arg₀ arg₁) →
      let ρ₀' := VarEnv.update ρcap₀ x₀ arg₀
      let ρ₁' := VarEnv.update ρcap₁ x₁ arg₁
      … (premises to build ctx_body from σcap, runtimeInstantiatesCtx, agreeOnClean) … →
      StepFRW k_body ctx_body R body res_body predSat …
```

The conclusion obtained from `StepFRW` is exactly what closure agreement needs:

- post-state preservation of `agreeOnClean` (in the `ctxAfter` post-context), and
- return-value agreement whenever the inferred return type is clean-under-\(R\), stated using `agreeValueUnder k_body`.

The `pfn` case is analogous, with `Value.peClosure` and `ETyp.parrow`. Pure bodies cannot perform I/O in the operational semantics,
so they do not introduce any additional world-desynchronisation concern beyond what `StepFRW` already handles.

**Scope notes:**

- **Non-singleton typing-closure lists:** although runtime values never carry "closure sets", arrow/parrow *types* may carry typing-closure lists with multiple
  elements. In this proposal, `closuresAgreeUnder` handles such lists by **witness selection**: it requires the existence of a typing closure in the list whose
  binder/body match the runtime closure, and then uses the corresponding captured typing environment to invoke `StepFRW` for that body.
  
  This is sound because the witness is constrained by the runtime value: we are not guessing which alternative the program “should have” taken; rather, we pick an
  alternative that matches the closure that was actually produced at runtime. In the clean-under-\(R\) situations where closure agreement is required, the two-run
  reasoning typically forces both executions to follow the same control-flow for clean tests, so both runs produce matching runtime closures and hence share (at least)
  one common witness in the typing-closure list.
- **Extern typing closures:** the type system can construct `FnTClosure.extern` / `PFnTClosure.extern`, but the operational semantics does
  not evaluate extern expressions to runtime closures (extern expressions do not terminate). The closure-agreement problem discussed in this
  note concerns runtime `Value.closure` / `Value.peClosure` produced by `fn`/`pfn`.

### How this discharges the `fn` / `pfn` step cases

In the `fn` and `pfn` branches, evaluation returns closure values capturing the current runtime environment.
To satisfy `resultAgreesIfClean`, we must show `agreeValueUnder k` at the returned arrow/parrow qualified type (for the
current step index \(k\), instantiated from the typing fuel in the step proof).
By construction, that reduces to showing `closuresAgreeUnder k` for the produced closures, which is proved by unfolding
`closuresAgreeUnder k` and appealing (at smaller fuel) to `StepFRW` for the closure body.


---

## Implementation plan

This section provides a staged implementation plan. Per the agreed scope, the new machinery (fuel-indexed `StepFRW`,
behavioural closure agreement, and the fuel-indexed value-agreement relation) does not need to be exposed outside
`LeanProofs/FaultRobustnessProofs.lean`. Accordingly, the plan below keeps all new definitions `private` within that file.

Each stage is intended to end in a state where **the project builds** (i.e. `lake build` succeeds). It is acceptable for
intermediate stages to contain `sorry` (feature-branch iteration), as long as the build succeeds.

After each stage:

- run `lake build`,
- review the diff, and
- **suggest** (but do not automatically perform) a commit with the message listed for that stage.

### Stage 1: Shared `ETyp` classifiers (no semantic changes)

Add small classifiers for function types to `LeanPoison/Syntax.lean`, since they are generic and likely useful beyond the
fault-robustness development. Proofs can then refer to these shared helpers rather than duplicating ad-hoc pattern matches.

- [ ] **1.1** In `LeanPoison/Syntax.lean`, add:
  ```lean
  def ETyp.isArrow : ETyp → Bool
    | .arrow _ _ _ _ => true
    | _ => false

  def ETyp.isParrow : ETyp → Bool
    | .parrow _ _ _ _ => true
    | _ => false

  def ETyp.isFunctionType (t : ETyp) : Bool :=
    t.isArrow || t.isParrow
  ```
- [ ] **1.2** Run `lake build` to confirm the project still compiles.
- [ ] **1.3** Suggested commit message: *"LeanPoison: add ETyp.isArrow/isParrow/isFunctionType helpers"*

### Stage 2: Fuel-indexed refactor (skeleton + plumbing; closure agreement remains a stub)

Refactor the world-indexed step theorem and its value-agreement dependency to be indexed by the **type-checking fuel**.
In practice this cannot be split meaningfully into two separate stages: once `StepFRW` and `agreeValueUnder` are made fuel-indexed,
all dependent helper lemmas in `LeanProofs/FaultRobustnessProofs.lean` must be updated to mention the fuel parameter, otherwise the
file will not compile.

At the end of this stage, the project should compile, but **behavioural closure agreement is still a stub**: `closuresAgreeUnder` need
not call `StepFRW` yet, and the `fn`/`pfn` proof branches may remain `sorry`.

- [ ] **2.1** In `LeanProofs/FaultRobustnessProofs.lean`, introduce a `mutual` block (all `private`) containing:
  - `StepFRW (k : Nat) …` (fuel-indexed),
  - `agreeValueUnder (k : Nat) …` (fuel-indexed), and
  - `closuresAgreeUnder (k : Nat) …` (fuel-indexed).

  At this stage, it is fine for `closuresAgreeUnder` to be a `sorry` stub. In particular, it does **not** need to invoke `StepFRW`
  on the closure body yet.
- [ ] **2.2** Refactor `resultAgreesIfClean` and the conclusion of `StepFRW` to use `agreeValueUnder k` (rather than an unindexed relation).
- [ ] **2.3** Update all local helper lemmas in `LeanProofs/FaultRobustnessProofs.lean` that mention `agreeValueUnder` so that they take an explicit
  fuel parameter `k` (or are otherwise stated in terms of the new indexed relation). This includes, for example:
  - lemmas extracting equality for clean non-reference results, and
  - lemmas transporting/lifting agreement across context/realisation-map changes.
- [ ] **2.4** Update the conversion lemma that erases worlds to accept the fuel parameter:
  - `StepFR_of_StepFRW (k : Nat) : StepFRW k ctx R e res predSat → StepFR ctx R e res predSat`.
  Then update `TypeSystemEnforcesFaultRobustness_step` to instantiate `k := fuel` and apply this lemma as before.
- [ ] **2.5** Ensure the `fn`/`pfn` branches in `TypeSystemEnforcesFaultRobustness_stepW` remain blocked only by the intended `sorry`
  (and not by type errors stemming from the refactor).
- [ ] **2.6** Run `lake build` to confirm the project compiles.
- [ ] **2.7** Suggested commit message: *"LeanProofs: fuel-index StepFRW and agreement lemmas (closure agreement stub)"*

### Stage 3: Implement `closuresAgreeUnder` (replace stub; existential witness over typing-closure lists)

Implement behavioural closure agreement for arrow/parrow values, using the generic witness-based approach (no singleton special-casing):

- [ ] **3.1** Define (proof-local) match predicates that relate a runtime closure to a typing closure **by binder and body only**:
  - for impure: `Value.closure x body ρcap` matches `FnTClosure.regular x body σcap`;
  - for pure: `Value.peClosure x pbody ρcap` matches `PFnTClosure.regular x pbody σcap`.

  Captured runtime environments are deliberately **not** compared.
- [ ] **3.2** Define `closuresAgreeUnder` so that it requires:
  - an existential typing-closure witness `tcl ∈ tcls` matching both runtime closures, and
  - a universal property over arguments: for “related” arguments (regime-dependent, i.e. required only when the argument type is clean-under-\(R\)),
    applying the two runtime closures yields results related by `agreeValueUnder` via an invocation of `StepFRW` on the closure body
    (at a strictly smaller fuel index).
- [ ] **3.3** In the proof obligations produced by the `StepFRW` call, discharge the `agreeOnClean` premise for the body context by
  combining:
  - inherited agreement for captured variables (from the outer `agreeOnClean`), and
  - the argument-relatedness premise for the binder introduced by `VarEnv.update`.
- [ ] **3.4** Run `lake build` to confirm the project compiles.
- [ ] **3.5** Suggested commit message: *"LeanProofs: implement closuresAgreeUnder (existential witness over typing-closure lists)"*

### Stage 4: Discharge the `fn` / `pfn` branches in `TypeSystemEnforcesFaultRobustness_stepW`

Use the new local machinery to eliminate the `sorry` blocks for `Expr.fn` and `Expr.pfn`.

- [ ] **4.1** In the `Expr.fn` branch, show:
  - the two runs return runtime closures with the same binder and body (captured environments may differ), and
  - `agreeValueUnder` holds for the arrow qualified type by applying the arrow/parrow case (delegating to `closuresAgreeUnder`).
  The existential witness for the typing closure is obtained from the typing-closure list produced by `typecheckFn` (a singleton in this case),
  but the definition and the proof principle remain the generic “∃ witness in the list” form.
- [ ] **4.2** Similarly discharge `Expr.pfn` using the parrow variant.
- [ ] **4.3** Run `lake build` to confirm the project compiles.
- [ ] **4.4** Suggested commit message: *"LeanProofs: discharge fn/pfn cases using behavioural closure agreement"*

### Stage 5: Consolidate helper lemmas (as needed)

Add narrowly-scoped helper lemmas when they prevent repeated low-level reasoning. Prefer generic, list-based lemmas over singleton-only lemmas, since the closure-list
design is already non-singleton in other parts of the development.

- [ ] **5.1** List/witness lemmas (e.g. extracting a `FnTClosure.regular …` witness from membership, reasoning about binder/body match).
- [ ] **5.2** `agreeOnClean` “body-context bridge” lemmas (captured environment + argument binding).
- [ ] **5.3** Any runtime-instantiation lemmas needed to invoke the indexed `StepFRW` on the body.
- [ ] **5.4** After each coherent batch of helper lemmas, run `lake build` to confirm the project compiles.
- [ ] **5.5** Suggested commit message (per batch): *"LeanProofs: add helper lemmas for behavioural closure agreement"*

### Stage 6: Documentation update (last)

Update the prose documentation to reflect the closure-agreement design used by the fault-robustness proof.

- [ ] **6.1** Update `doc/poison-lang-description.tex` (Fault Robustness / Formal Properties section) to describe:
  - that function values are runtime closures that capture environments, so agreement for clean functions cannot be stated as literal closure equality; and
  - that the proof uses behavioural (extensional) closure agreement, defined via the (fuel-indexed) world-threaded step theorem on closure bodies.
- [ ] **6.2** Run `make -C doc` to confirm the documentation still builds.
- [ ] **6.3** Suggested commit message: *"Doc: describe behavioural closure agreement in fault-robustness proof"*
