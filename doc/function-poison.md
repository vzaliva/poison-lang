# Function poison: intended semantics and design options

This note records the current ambiguity around *function poison* in Poison, and
proposes concrete design directions. The aim is to converge on a stable
interpretation before further proof engineering (notably, the `app` case of the
fault-robustness step theorem).

## Background: two “poison carriers” for functions

In the current formalism (Ott + Lean), function values carry poison information
in two places:

- **Outer poison (qualified type)**: the `p` in `QTyp` / `Q` (`T :> p {P}`).
  This is the generic poison flag for “the result may be corrupted / not
  specification-relevant”.

- **Inner poison (arrow type)**: the `p` in arrow/parrow types (`ST1 -> ST2 # p …`).
  This is a function-specific poison component that propagates through
  application typing via the body’s `pc` (Ott: `join p join p1 pc`).

### Why the design has two components

The working notes (`doc/poison-lang-description.tex`) motivate two orthogonal
poison flags for closures/variables and, for functions in particular, tie the
inner arrow poison to *deferred* body typechecking:

- **Definition-time control taint**: the arrow’s internal poison `# p` records the
  program-counter poison at the function’s definition site. This information must
  be stored in the type because the body is not fully analysed “once and for all”
  at definition time; instead it is re-typechecked at application time against the
  actual argument’s qualified type and the current logical environment.

- **Call-site provenance taint**: the outer qualified-type poison (`Q.poison`)
  tracks the reliability of the *function value as an expression result* (for
  example, selection under poisoned control flow or tainted storage). In the
  application rule, this outer poison also contributes to the poison context
  under which the body is re-typechecked (via a join with the ambient `pc`),
  reflecting that the *choice of function* may itself be control-dependent on
  faults.

This separation is conceptually useful, but it is exactly what makes the current
fault-robustness `app` case sensitive to the intended meaning of “dirty
functions”.

The design question is: *which of these should govern the semantic and proof
obligations for closures, in particular agreement of captured environments and
world/IO behaviour?*

## Intuition: what “dirty function” should mean

We use “dirty function” to mean: a closure value whose *provenance* makes it
unreliable as a specification-level value (e.g. selected under poisoned control
flow). Importantly, this is an epistemic notion:

- **Still well-formed**: it remains a syntactically valid closure with a
  well-formed captured environment (no stuckness implied).
- **Relational guarantees may weaken**: cross-run agreement about the chosen
  closure (and its captured environment) may not hold without additional
  hypotheses.

## Practical scenarios that produce dirty functions

From the perspective of program semantics, dirtiness arises in typical ways:

- **Poisoned control flow**: selecting between closures under a poisoned
  condition (e.g. `if` with a corrupted test). The resulting value is a valid
  closure, but it may differ across runs.

- **Tainted storage**: assigning a closure into a variable under poisoned `pc`,
  and reading it later. The closure is well-formed but may not match the
  programmer’s intended one.

- **Higher-order propagation**: returning functions from computations influenced
  by poisoned inputs (including conditionals and calls that join closure
  alternatives).

These scenarios suggest that “dirty” should *not* invalidate the closure’s
captured environment, but can invalidate assumptions about agreement across
runs.

## The immediate proof pressure (fault-robustness `app`)

The step theorem used by fault-robustness requires (among other things):

- preservation of agreement on clean state (`agreeOnClean …`), and
- equality of world tokens (`w₀' = w₁'`),

for application as well.

In the current `app` proof attempt, “dirty functions” create two distinct (and
logically independent) obstacles:

1. **World synchronisation (`w₀' = w₁'`)**: even under the IO axioms, world
   evolution is sensitive to the *trace shape* (which IO actions occur, and how
   many), not to IO arguments. If two runs can take different IO-bearing control
   paths in the function body, `w₀' = w₁'` can fail.

2. **`agreeOnClean` for the body context**: to apply the IH to the function body
   in the two-run setting, we need `agreeOnClean …` for the body’s typing
   context. Operationally this amounts to requiring agreement of the two
   captured runtime environments on those captured entries whose qualified types
   are clean-under-\(R\). For dirty functions, the current proof infrastructure
   does not justify this agreement premise.

The rest of this note discusses design options to address (1) and (2). These
options can be combined: addressing (2) does not automatically fix (1), and vice
versa.

### At a glance

- **Direction A** is primarily about **(1) world synchronisation**: what the
  step theorem should require about `w₀' = w₁'` (and, if desired, related
  postconditions) when the computation is not clean-under-\(R\).
- **Direction B** is primarily about **(2) `agreeOnClean` / captured-environment
  agreement**: how to gate closure-value agreement (and hence the IH premises
  for the body) using the internal arrow poison rather than the outer
  qualified-type poison.

In other words, A and B are best read as *orthogonal axes*: one chooses a policy
for (1) and a (possibly independent) policy for (2), then combines them.

## Design direction A (Lean-first): keep outer poison for functions, refine observables

**Core idea**: keep the current meaning of outer poison for functions, and make
the step theorem’s obligations conditional on what is considered observable.

- **A (world synchronisation only when clean)**: require `w₀' = w₁'` only when the
  relevant computation is clean-under-\(R\). In the current development, the IO
  axioms make world evolution insensitive to *arguments* (e.g. what is printed,
  or the bound passed to `rand`), but not insensitive to *control flow*: if two
  runs perform different numbers or sequences of IO actions (e.g. because a
  poisoned condition selects different branches), the successor worlds need not
  coincide. This is therefore only relevant as a deliberate choice to treat such
  world/IO divergence as non-observable when the computation is not clean-under-\(R\).

**Pros**:
- Minimal disruption to the type system.
- Clean separation between “dirty may behave unpredictably” and “clean must
  agree”.

**Cons**:
- Requires refining the specification of the step theorem (and hence the proof
  statements).

### Lean sketch for direction A

The aim of direction A is to change *what the step theorem promises* when the
computation is not clean-under-\(R\). Starting from the current `StepFRW`
definition, the minimal change is to relax the **world-equality** part of the
conclusion so that it is only required when the inferred result type is
clean-under-\(R\).

Below is a schematic (non-compiling) sketch in the style of the current
development.

#### Sketch (conditional world equality and conditional agreement)

```lean
-- Sketch only: names and fields should be aligned with the existing development.
--
-- Representative shape: the only change from `StepFRW` is that `w₀' = w₁'` is
-- replaced by an implication from cleanliness.
private def StepFRW_A
  (ctx : TypeContext) (R : Regime) (e : Expr) (res : TypeResult) (predSat : PredSat) : Prop :=
    ∀ (w : Void IO.RealWorld)
      (μ₀ μ₁ : Memory) (ρ₀ ρ₁ : VarEnv) (θ₀ θ₁ : RealizationMap)
      (cf₀ cf₁ : Config) (o₀ o₁ : Value),
      -- ... same hypotheses as StepFRW ...
      ∀ (a₀ a₁ : Address) (pm₀ pm₁ : Bool),
        ∀ (w₀' w₁' : Void IO.RealWorld),
          terminatesToW w w₀' e { memory := μ₀, varEnv := ρ₀, nextAddr := a₀, pureMode := pm₀ } cf₀ o₀ →
          terminatesToW w w₁' e { memory := μ₁, varEnv := ρ₁, nextAddr := a₁, pureMode := pm₁ } cf₁ o₁ →
          ∃ (θ₀' θ₁' : RealizationMap),
            -- CHANGED (relative to `StepFRW`):
            --   `StepFRW` requires: `w₀' = w₁'`
            --   `StepFRW_A` requires: `qtypCleanUnder R res.qualType → w₀' = w₁'`
            (qtypCleanUnder R res.qualType → w₀' = w₁') ∧
            -- END CHANGED
            -- ... remaining `StepFRW` conjuncts unchanged ...
            resultAgreesIfClean predSat R cf₀.memory cf₁.memory θ₀' θ₁' res.qualType o₀ o₁
```

This formulation makes explicit that, under A, *dirty computations are permitted
to desynchronise worlds* (by taking different IO traces) and are not required to
establish the `agreeOnClean` facts that the current `app` proof needs.

## Design direction B (function-special): outer-clean closures, internal poison governs reliability

**Core idea**: treat closure values as always outer-clean (`Q.poison = clean`
for arrow/parrow), and track their reliability solely via the arrow’s internal
poison field (`# p`). Informally, the closure is always a well-formed object,
but the internal poison controls what we may conclude about its behaviour.

Concretely, this means:

- **Closure values**: outer-clean does *not* mean “fully relationally reliable”.
  Instead, the closure agreement predicate is made sensitive to the internal
  poison of the arrow/parrow type.
- **Closure applications**: when internal poison is not clean-under-\(R\), we do
  not require relational agreement of application results (and, depending on the
  chosen observable model, we may also need to weaken requirements about IO trace
  shape / world equality for such calls).

This requires a principled replacement for “clean-under-\(R\)” for function-typed
values:

- either redefine cleanliness for function types to depend on the *internal*
  poison `p` (and guard tags), or
- modify agreement predicates so that closure agreement (including captured
  environment agreement) is gated by the internal poison, not by `Q.poison`.

**Pros**:
- Matches the intuition that “the closure object exists and is well-formed even
  when unreliable”.
- Gives a single place (the internal poison) to control relational obligations
  for closures.

**Cons**:
- Non-trivial changes to typing rules and to the proof-layer definitions that
  currently inspect outer poison (`qtypCleanUnder`, `resultAgreesIfClean`).
- The main pitfall is an *incorrect* interpretation of “outer-clean” as implying
  unconditional closure agreement. Under poisoned control flow one can obtain
  different closure bodies across runs; therefore, any obligation that forces
  “same closure” (same body) must be gated by internal reliability, not by
  outer-cleanliness alone.

## Consequences for Lean (two concrete implementation sketches)

### Lean sketch B1: redefine cleanliness for function types

Keep `QTyp.poison` always `false` for `arrow/parrow`, but redefine:

- `qtypCleanUnder` (or a function-specific predicate) so that for
  `qt.etyp = arrow/parrow … p …`, cleanliness is determined by the *internal*
  poison `p` (and guard tags), not by `qt.poison`.

This keeps the existing “clean gating” pattern but moves the gate.

### Lean sketch B2: keep `qtypCleanUnder`, refine agreement predicates for closures

Leave `qtypCleanUnder` as a generic predicate, but change:

- the closure cases of `agreeValueUnder`, and/or
- the interface `resultAgreesIfClean`,

so that, for function values:

- **If internal poison is clean-under-\(R\)**: closure agreement requires (at
  least) *same body* and agreement of captured environments on those captured
  entries whose qualified types are clean-under-\(R\).
- **If internal poison is not clean-under-\(R\)**: closure agreement imposes no
  such constraints (intentionally allowing different bodies and/or captured
  environments across runs), and application-result agreement is not required.

This is often more explicit but touches more proof plumbing.

**Scope**: direction B is primarily aimed at obstacle (2) (making the captured
environment agreement obligations line up with when we consider a function
relationally reliable). Direction B does *not* by itself decide what should
happen to obstacle (1): if internally-unreliable functions may still perform
different IO traces across runs, one must either relax world equality for such
calls (an A-style choice) or adopt a different observable model for worlds/IO.

## Consequences for Ott rules (high-level edits)

Under direction B (outer-clean closures), the Ott typing rules must be updated
in the places where they currently set outer poison to `pc` (or to joins that
include `pc`) for function-typed results:

- **`fn_abs` / `pfn_abs`**:
  - currently: `… # pc … :> pc { no_pred }`
  - proposed: `… # pc … :> clean { no_pred }` (outer poison forced to clean),
    keeping internal `# pc`.

- **Conditional rules producing functions** (`if_*_fn`, `if_*_pfn`):
  - currently: return poison includes outer joins of branch poisons (and
    possibly guard poison).
  - proposed: for function-typed conclusions, outer `:>` becomes `clean`, while
    internal arrow poison is still joined (`p = join p' p''`), and closure sets
    are merged as before.

- **Application rules producing functions** (`app_*_arrow` / `app_*_parrow`):
  - currently: outer poison includes `join pc p3` (or similar).
  - proposed: for function-typed results, outer `:>` becomes `clean`, and the
    internal arrow poison accounts for reliability.

Any such Ott changes must be reflected in the Lean typechecker (`typecheckFn`,
`typecheckPfn`, `typecheckIf`, `typecheckApp`, `joinTypeResults`) and in the
documentation that mirrors the Ott spec.

## Open decisions (to settle before implementation)

- **What is the intended observable model for world/IO?**
  - Is IO/world equality required unconditionally, or only for clean computations?

- **What is the intended relational guarantee for dirty closures?**
  - Must captured environments agree on clean entries even when the closure is
    dirty, or is that intentionally not required?

- **Which poison carrier is authoritative for function reliability?**
  - Outer `Q.poison`, internal arrow poison `# p`, or a combination?

Once these are fixed, we can implement the corresponding Lean/Ott changes and
finish the `app` proof accordingly.

