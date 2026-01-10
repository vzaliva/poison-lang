## Closure equality issue in fault-robustness proofs

This note documents a specification-level mismatch that blocks the `fn` and `pfn` cases in
`LeanProofs/FaultRobustnessProofs.lean` (currently around the `TypeSystemEnforcesFaultRobustness_stepW` proof),
and proposes a fix using structural closure agreement.

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

### Step result agreement when "clean under the regime"

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


## Why `LeanProofs/Equality.lean` does not resolve the proof

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


---

## Proposed fix: structural closure agreement

The specification-level fix is to stop treating arrow/parrow values as "just another non-reference" in
`agreeValueUnder`. Instead, we define closure agreement **structurally**: two closures agree if they have
the same binder and body, and their captured environments agree on clean entries.

### Structural agreement for closures

Two closure values `v₁` and `v₂` agree structurally (under regime \(R\)) if:

1. **Same binder and body**: the parameter names and body expressions are syntactically equal.
2. **Captured environments agree**: for each variable `x` in the captured environment:
   - if the variable's type is clean-under-\(R\), the captured values must agree (recursively);
   - if the variable's type is not clean-under-\(R\), the captured values may differ.

This definition is **recursively well-founded**: captured environments may contain other closures, but
those closures are strictly smaller (they were created earlier in the evaluation). No fuel indexing is
required.

### Runtime closures versus typing closures

It is important to keep two distinct notions separate:

- **Runtime closures** are values produced by evaluation, of the form `Value.closure x body ρcap` or
  `Value.peClosure x body ρcap`, where `ρcap : VarEnv` is a list of *runtime* bindings `(Name × Value)`.
- **Typing closures** are a type-system device stored inside arrow/parrow enriched types (the closure
  list in `ETyp.arrow` / `ETyp.parrow`), of the form `FnTClosure.regular x body σcap` or
  `PFnTClosure.regular x body σcap`, where `σcap : CapturedVarEnv` (i.e. `List (Name × QTyp)`) is a list of
  *typing* bindings.

The **problem** diagnosed earlier is purely about runtime closures (they capture the whole runtime
environment, but `agreeOnClean` only constrains clean entries). Typing closures provide the **type
information** needed to determine which captured variables are clean-under-\(R\).

**Important structural differences:**

1. **Multiple typing closures**: Arrow types can carry *lists* of typing closures (from control-flow
   joins). A runtime closure must be matched to one typing closure in the list via binder/body comparison.

2. **List structure mismatch**: `σcap : CapturedVarEnv` in the typing closure may have different
   structure than runtime `ρcap : VarEnv` (a cons-list that may have duplicates from `VarEnv.update`).
   Positional list recursion will not work; agreement must be defined **extensionally** using
   `CapturedVarEnv.lookup` and `VarEnv.lookup`.

3. **Pure closure body types**: `PFnTClosure.regular` stores a `PExpr` body, but `Value.peClosure`
   stores an `Expr` body. Matching binder/body requires a bridge (e.g. comparing via `Expr.toPExpr`
   or storing compatible representations).

### Structural agreement definition

The structural approach requires:

1. **Typing closure witness selection**: For arrow types with multiple typing closures (from joins),
   we require an existential witness `tcl ∈ tcls` whose binder and body match the runtime closure.

2. **Extensional captured-environment agreement**: Since `σcap` and `ρcap` have different list
   structures (sorted/unique vs cons-list with duplicates), agreement is defined by **name lookup**
   rather than positional list recursion.

### When arrow/parrow constructors should fire

Arrow types should not have predicates (invariant: `guardClosure` is never applied to arrows), but
they can have guard tags which, if set true in the regime, de-poison them. The new arrow/parrow
constructors must **not** fire unconditionally — they should only fire when there is a
clean-under-\(R\) reason. Otherwise, we would silently enlarge `agreeValueUnder` for poisoned/no-tag
functions, weakening the specification beyond "clean-under-\(R\) ⇒ agree".

The constructors mirror the existing split for non-function types:

1. **`clean_arrow`/`clean_parrow`**: Fire when `qt.poison = false` (clean via poison-false path).
2. **`guardOnly_true_arrow`/`guardOnly_true_parrow`**: Fire when `qtypGuardTag qt = some k` and
   `R.lookup? k = some true` (de-poison via guard tag path).

The existing "equality-for-nonrefs" constructors (`clean_eq_nonref`, `withPred_true_eq`,
`poisoned_noPred_eq_nonref`, etc.) must continue to **exclude function types** via
`qt.etyp.isFunctionType = false`.

Schematically:

```lean
inductive agreeValueUnder (predSat : PredSat) (R : Regime)
    (μ₁ : Memory) (θ₁ : RealizationMap) (μ₂ : Memory) (θ₂ : RealizationMap)
    : QTyp → Value → Value → Prop where
  | int (n : Int) : agreeValueUnder ... qt (.int n) (.int n)
  | bool (b : Bool) : agreeValueUnder ... qt (.bool b) (.bool b)
  | unit : agreeValueUnder ... qt .unit .unit
  | loc ... : agreeValueUnder ... qt (.loc l₁) (.loc l₂)

  -- Clean arrow (qt.poison = false at QTyp level)
  | clean_arrow
      (hclean : qt.poison = false)                        -- QTyp-level poison
      (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)       -- deconstruct etyp (p is arrow-internal)
      (htcl : tcl ∈ tcls)
      (hmatch_binder : tcl.binder = x)
      (hmatch_body : tcl.body = body)
      (hcap : agreeCapturedEnv ... tcl.σcap ρcap₁ ρcap₂)
      : agreeValueUnder ... qt (.closure x body ρcap₁) (.closure x body ρcap₂)

  -- Guard-only true arrow (de-poison via guard tag)
  | guardOnly_true_arrow
      (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)       -- deconstruct etyp
      (htag : qtypGuardTag qt = some k)
      (hregime : R.lookup? k = some true)
      (htcl : tcl ∈ tcls)
      (hmatch_binder : tcl.binder = x)
      (hmatch_body : tcl.body = body)
      (hcap : agreeCapturedEnv ... tcl.σcap ρcap₁ ρcap₂)
      : agreeValueUnder ... qt (.closure x body ρcap₁) (.closure x body ρcap₂)

  -- Similar for parrow (with PExpr/Expr bridge for body)
  | clean_parrow
      (hclean : qt.poison = false)
      (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
      ...
  | guardOnly_true_parrow
      (hetyp : qt.etyp = ETyp.parrow st1 st2 p tcls)
      (htag : qtypGuardTag qt = some k)
      (hregime : R.lookup? k = some true)
      ...

-- Lookup-based agreement: for each name in σcap, lookup in ρcap agrees
def agreeCapturedEnv (predSat : PredSat) (R : Regime)
    (μ₁ : Memory) (θ₁ : RealizationMap) (μ₂ : Memory) (θ₂ : RealizationMap)
    (σcap : CapturedVarEnv) (ρcap₁ ρcap₂ : VarEnv) : Prop :=
  ∀ x qt, σcap.lookup x = some qt →
    match ρcap₁.lookup x, ρcap₂.lookup x with
    | some v₁, some v₂ =>
        qtypCleanUnder R qt → agreeValueUnder ... qt v₁ v₂
    | _, _ => True  -- variable not in runtime env (shouldn't happen if well-typed)
```

**Note on mutual recursion**: The extensional definition uses `∀` with `agreeValueUnder` in the body.
If this causes Lean kernel issues (similar to the behavioural approach), we may need to:
- Define `agreeCapturedEnv` inductively over the domain `σcap` (a finite list), or
- Use a well-founded recursion on value structure (captured values are subterms).

The key difference from the behavioural approach is that we do not invoke `StepFR` — we only recurse
on strictly smaller values (those in the captured environment).

### Typing closure witness selection

For arrow types, the typing closure list `tcls` may contain multiple entries (from control-flow joins).
The `arrow` constructor requires:

1. A witness `tcl ∈ tcls` that matches the runtime closure by binder and body.
2. The captured typing environment `tcl.σcap` is then used for `agreeCapturedEnv`.

This is well-defined because in contexts where closure agreement matters (clean-under-\(R\)), both
runs evaluate the same syntactic `fn`/`pfn`, producing closures with the same binder and body. The
witness is therefore determined by the runtime value.

**⚠️ Open issue: non-unique witness selection**

After control-flow joins, `tcls` may contain multiple typing closures with the **same binder and body**
but **different captured typing environments** `σcap`. In this case, binder/body matching does not
uniquely identify the typing closure.

Possible resolutions:

1. **Uniqueness property**: Prove that `tcls` never contains duplicates with same binder/body but
   different `σcap`. This seems unlikely given how joins work.

2. **Separate witnesses per side**: Allow each run to select its own witness `tcl₁ ∈ tcls` and
   `tcl₂ ∈ tcls` (both matching the runtime closure by binder/body), and require that their
   captured typing environments are "compatible" in the sense that `agreeCapturedEnv` can
   be established using either.

3. **Weaker witness requirement**: Require only that *some* `tcl ∈ tcls` with matching binder/body
   has a `σcap` for which `agreeCapturedEnv` holds. The proof obligation then becomes showing
   such a witness exists.

**Status**: To be resolved before Stage 2 implementation. May require examining how `mergeFnTClosures`
constructs `tcls` after joins and what invariants hold.

### Pure closure body bridge

For `parrow` types, `PFnTClosure.regular` stores a `PExpr` body while `Value.peClosure` stores an
`Expr` body. Use the pure conversion `Expr.toPExpr?` (not the monadic `Expr.toPExpr`):

```lean
-- Body match for parrow: convert runtime Expr to PExpr and compare
hmatch_body : body.toPExpr? = some pbody ∧ tcl.body = pbody
```

This requires a bridge lemma showing that if a `pfn` expression type-checks, then `body.toPExpr?`
succeeds and produces the same `PExpr` stored in the typing closure. The lemma should be
established in Stage 2 before implementing the `parrow` case.


---

## How this discharges the `fn` / `pfn` step cases

In the `fn` and `pfn` branches, evaluation returns closure values capturing the current runtime
environment. To satisfy `resultAgreesIfClean`, we must show `agreeValueUnder` at the returned
arrow/parrow qualified type.

The closures produced have:
- **Same binder**: both runs evaluate the same syntactic `fn x ...` or `pfn x ...`, so `x₁ = x₂`.
- **Same body**: both runs store the same body expression.
- **Captured environments that agree on clean entries**: from `agreeOnClean` at function-definition
  time, clean variables have agreeing values. The structural definition explicitly allows poisoned
  entries to differ.

The typing closure `σcap` is obtained from the arrow type produced by `typecheckFn` / `typecheckPfn`.
It records the types of all captured variables, enabling the `agreeCapturedEnv` predicate to
distinguish clean from poisoned entries.


---

## How `app` (function application) is handled

When proving fault-robustness for `Expr.app f arg`:

1. The induction hypothesis gives us `agreeValueUnder` for the closure values (from evaluating `f`).
   By inversion on the `closure` constructor, we obtain:
   - same binder and body,
   - `agreeCapturedEnv` for the captured environments.

2. The induction hypothesis gives us `agreeValueUnder` for the argument values (from evaluating `arg`).

3. We must show that evaluating the two closure bodies produces agreeing results.

The key insight is that the **main fault-robustness theorem** (`TypeSystemEnforcesFaultRobustness_stepW`)
is proved by induction on evaluation. When we reach the `app` case:

- The closure body is evaluated with:
  - runtime environments `ρ₀' := VarEnv.update ρcap₀ x arg₀` and `ρ₁' := VarEnv.update ρcap₁ x arg₁`
  - the same body expression
  - the typing context built from the captured typing environment extended with the parameter binding

- The `agreeOnClean` precondition for the body evaluation is established from:
  - `agreeCapturedEnv` for the captured variables (from closure agreement), and
  - `agreeValueUnder` for the argument (from the argument evaluation).

- The induction hypothesis (applied to the body evaluation) then yields the required post-condition:
  `agreeOnClean` preservation and return-value agreement.

This reasoning happens in the **proof** of the main theorem, not in the definition of `agreeValueUnder`.
The structural definition simply records that closures have the same structure; the behavioural
consequence (that applying them produces agreeing results) follows from the induction.


---

## Summary

| Aspect | Original (literal equality) | Structural agreement |
|--------|---------------------------|---------------------|
| Closure agreement | `v₁ = v₂` (full equality) | Same binder/body + captured envs agree on clean |
| Poisoned captured vars | Must be equal (unprovable) | May differ |
| Lean encoding | Blocked (unprovable premise) | Simple mutual induction, no fuel |
| `fn`/`pfn` cases | Blocked | Provable from `agreeOnClean` |
| `app` case | Blocked | Uses main theorem's induction hypothesis |

The structural approach is stronger than strictly necessary (structurally agreeing closures certainly
behave the same), but it is provable from the available hypotheses and avoids the Lean kernel
limitations that block alternative encodings.


---

## Implementation Notes

### Observable returns and function types

At the moment, `observablesEqual` treats any **non-reference** return value as
observable via **literal equality** (`o₁ = o₂`). Since function values are
runtime closures that capture a `VarEnv`, this would force *structural closure
equality* (including equality of captured environments), reintroducing the exact
mismatch described in this note: the step invariant (`agreeOnClean`) only
provides agreement on **clean-under-\(R\)** context entries, not full
environment equality.

The implementation therefore adds a *temporary restriction* on observable specs:
`wfObsSpec` requires that an observed return type is **not** a function type
(`ETyp.arrow` / `ETyp.parrow`). The intent is that this restriction applies only
to the **top-level** FR theorem: it is used when converting the step theorem’s
return-value agreement postcondition into the `observablesEqual` return clause.
The step theorems themselves do not depend on `wfObsSpec`, so
evaluation/typechecking of subexpressions may still produce function values;
they are just not treated as observable *final* return values in the current
top-level statement.

**Potential future fix (more principled):** redefine return/memory observability in terms of the
existing agreement relations:

- Use `agreeLocUnder` to compare each observed location in `obs.locs`.
- Use `agreeValueUnder` to compare the observed return value (with the appropriate `QTyp`).

This would allow observing **clean function returns** via the arrow/parrow
agreement cases rather than requiring literal closure equality. Implementing
this likely requires threading `predSat` and the regime `R` (and a `QTyp` for
each observed type, e.g. from the typechecker result) into the definition of
`observablesEqual`, or introducing a separate `observablesEqualUnder` predicate.
However this is left as known design limitation.

### Captured environments and duplicate keys

Both runtime environments (`VarEnv`) and captured typing environments (`CapturedVarEnv`) are
association lists.

- Duplicates in a runtime `VarEnv` are handled: lookup is left-biased (the most recent binding wins).
- Duplicates in a captured typing environment are *not* handled by the current `agreeCapturedEnv`
  definition (which is structural over the full list): if duplicate keys were present, agreement
  obligations would apply to each occurrence rather than only the most recent one.
- In practice, the captured typing environments used in closures are produced via
  `VarTypeEnv.toCaptured` (from an `ExtTreeMap`), so duplicate keys do not occur by construction.

### Captured environment agreement vs typing

The current `agreeCapturedEnv` predicate is intentionally *agreement-only*: in the clean case it
requires that the looked-up values exist in both captured runtime environments and satisfy
`agreeValueUnder … qt v₁ v₂`, but it does **not** additionally record that `v₁`/`v₂` have enriched type
`qt.etyp`. When needed, those typing facts are obtained separately from `runtimeInstantiatesCtx` (plus
the fact that `σcap` comes from `ctx.varEnv` via `VarTypeEnv.toCaptured`), keeping agreement and typing
obligations modular.

## Implementation plan

This section provides a staged implementation plan. Each stage ends in a state where the project
builds (i.e. `lake build` succeeds), allowing incremental commits.

**Important**: `agreeValueUnder` is defined in `LeanProofs/FaultRobustness.lean`, not privately in
`FaultRobustnessProofs.lean`. Changes to its definition will affect dependent lemmas throughout the
proof development.

### Architectural note: module separation

The proof development maintains a separation between:

- **`LeanProofs/SemanticsProperties.lean`**: High-level definitions and theorems about evaluation
  semantics (`terminatesTo`, `terminatesToW`, `wfConfig`, etc.), independent of fault-robustness
  specifics.

- **`LeanProofs/FaultRobustness.lean`**: Fault-robustness specification (top-level theorem statements,
  `agreeValueUnder`, `agreeOnClean`, `Regime`, etc.).

- **`LeanProofs/FaultRobustnessProofs.lean`**: Implementation of fault-robustness proofs, including
  world-indexed step-based reasoning (`StepFRW`, `resultAgreesIfClean`, etc.).

**Guideline**: World-indexing and step-based proof machinery should remain in `FaultRobustnessProofs.lean`
and not leak into `SemanticsProperties.lean`. The new structural agreement definitions (`agreeCapturedEnv`,
arrow/parrow cases) belong in `FaultRobustness.lean` (specification level) since `agreeValueUnder` is
already defined there.

### Stage 1: Add gated arrow/parrow cases to `agreeValueUnder` with stubs

Extend `agreeValueUnder` in `LeanProofs/FaultRobustness.lean` with new **gated** constructors for
function types (clean via `qt.poison = false` or guard-tag de-poison), using stub predicates initially.

- [x] **1.1** In `LeanProofs/FaultRobustness.lean`, add new constructors to `agreeValueUnder`:
  ```lean
  -- Clean arrow (qt.poison = false)
  | clean_arrow
      (hclean : qt.poison = false)
      (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
      (htcl : tcl ∈ tcls)
      (hmatch : True)  -- stub: binder/body match
      (hcap : True)    -- stub: captured env agreement
      : agreeValueUnder ... qt (.closure x body ρcap₁) (.closure x body ρcap₂)

  -- Guard-only true arrow (de-poison via guard tag)
  | guardOnly_true_arrow
      (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
      (htag : qtypGuardTag qt = some k)
      (hregime : R.lookup? k = some true)
      (htcl : tcl ∈ tcls)
      (hmatch : True)  -- stub
      (hcap : True)    -- stub
      : agreeValueUnder ... qt (.closure x body ρcap₁) (.closure x body ρcap₂)

  -- Similar for parrow (clean_parrow, guardOnly_true_parrow)
  ...
  ```
- [x] **1.2** Update **all** cases that imply literal equality for non-references to exclude function
  types. This includes not just `clean_eq_nonref` but any case like `withPred_true_eq` or similar
  that could fire for clean function types. Add side condition `qt.etyp.isFunctionType = false`.
- [x] **1.3** Update helper lemmas in `FaultRobustness.lean` and `FaultRobustnessProofs.lean` that
  depend on `agreeValueUnder` to handle the new cases (may require additional pattern matches).
- [x] **1.4** Run `lake build` to confirm the project compiles.
- [x] **1.5** Suggested commit message: *"FaultRobustness: add gated arrow/parrow cases to agreeValueUnder (stubs)"*

### Stage 2: Implement captured environment agreement

Define the extensional (lookup-based) captured environment agreement predicate and wire it into the
arrow/parrow cases.

- [x] **2.1** Define `agreeCapturedEnv` over `CapturedVarEnv`.
  Implemented as an inductive predicate over the finite list `σcap` (to avoid mutual recursion issues):
  `agreeCapturedEnv.nil`, `agreeCapturedEnv.cons_clean`, `agreeCapturedEnv.cons_dirty`.
- [x] **2.2** Update the `arrow` case to use `agreeCapturedEnv` with proper binder/body matching:
  - `htcl : tcl ∈ tcls` (witness selection)
  - implemented as `hmatch : tcl = FnTClosure.regular x body σcap`
  - `hcap : agreeCapturedEnv ... tcl.σcap ρcap₁ ρcap₂`
- [x] **2.3** For `parrow`, handle the `PExpr`/`Expr` body mismatch using `Expr.toPExpr?`:
  - use `hmatch : Expr.toPExpr? body = some pbody ∧ tcl = PFnTClosure.regular x pbody σcap`
  - bridge lemmas (in `LeanProofs/FaultRobustnessProofs.lean`):
    - `Expr_toPExpr?_eq_some_of_toPExpr_ok`
    - `typecheckPfn_ok_body_toPExpr?`
- [x] **2.4** Add helper lemmas for `agreeCapturedEnv`:
  - relating to `agreeOnClean`: `agreeCapturedEnv_of_agreeOnClean` (and `agreeCapturedEnv_of_agreeOnClean_aux`)
  - transport across realisation-map extensions: `agreeCapturedEnv_clean_extends` (and `agreeValueUnder_clean_extends`)
- [x] **2.5** Run `lake build` to confirm the project compiles.
- [x] **2.6** Suggested commit message: *"FaultRobustness: implement extensional captured env agreement"*

### Stage 3: Discharge `fn` / `pfn` cases in `TypeSystemEnforcesFaultRobustness_stepW`

Use the structural agreement predicates to eliminate the `sorry` blocks for `Expr.fn` and `Expr.pfn`.

- [ ] **3.1** In the `Expr.fn` branch, show:
  - the typing closure list has a witness matching the runtime closure (from `typecheckFn`),
  - the binder and body match (syntactic, from same source expression),
  - `agreeCapturedEnv` holds using `agreeOnClean` at function-definition time.
- [ ] **3.2** Similarly discharge `Expr.pfn`, handling the `PExpr`/`Expr` bridge.
- [ ] **3.3** Add bridge lemmas connecting `agreeOnClean` to `agreeCapturedEnv`:
  - For each `(x, qt) ∈ σcap`, if `qtypCleanUnder R qt`, then `agreeOnClean` provides agreement
    for the values at `ρ₁.lookup x` and `ρ₂.lookup x`.
- [ ] **3.4** Run `lake build` to confirm the project compiles with no `sorry` in `fn`/`pfn` cases.
- [ ] **3.5** Suggested commit message: *"FaultRobustnessProofs: discharge fn/pfn cases using structural closure agreement"*

### Stage 4: Documentation update

Update the prose documentation to reflect the structural closure agreement design.

- [ ] **4.1** Update `doc/poison-lang-description.tex` (Fault Robustness / Formal Properties section)
  to describe:
  - that function values are runtime closures that capture environments, so agreement for clean
    functions cannot be stated as literal closure equality; and
  - that the proof uses structural closure agreement, comparing binder/body and checking that
    captured environments agree on clean entries.
- [ ] **4.2** Run `make -C doc` to confirm the documentation builds.
- [ ] **4.3** Suggested commit message: *"Doc: describe structural closure agreement in fault-robustness proof"*

### Future work: `app` case

The `app` case (function application) will be addressed separately. It requires showing that
applying structurally agreeing closures to agreeing arguments produces agreeing results. This
follows from the main theorem's induction hypothesis applied to the closure body evaluation.
