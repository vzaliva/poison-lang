# Function poison: intended semantics and design options

This note records the current ambiguity around *function poison* in Poison, and
proposes concrete design directions. The aim is to converge on a stable
interpretation before further proof engineering (notably, the `app` case of the
fault-robustness step theorem). In line with the I/O-free proof plan, this note
focuses only on relational obligations for closures and their captured
environments.

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
obligations for closures, in particular agreement of captured environments?*

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

for application as well.

In the current `app` proof attempt, “dirty functions” create an obstacle:

**`agreeOnClean` for the body context**: to apply the IH to the function body in
the two-run setting, we need `agreeOnClean …` for the body’s typing context.
Operationally this amounts to requiring agreement of the two captured runtime
environments on those captured entries whose qualified types are
clean-under-\(R\). For dirty functions, the current proof infrastructure does
not justify this agreement premise.

The rest of this note discusses design options to address it.

## Design direction (function-special): outer-clean closures, internal poison governs reliability

**Core idea**: treat closure values as always outer-clean (`Q.poison = clean`
for arrow/parrow), and track their reliability solely via the arrow’s internal
poison field (`# p`). Informally, the closure is always a well-formed object,
but the internal poison controls what we may conclude about its behaviour.

Concretely, this means:

- **Closure values**: outer-clean does *not* mean “fully relationally reliable”.
  Instead, the closure agreement predicate is made sensitive to the internal
  poison of the arrow/parrow type.
- **Closure applications**: when internal poison is not clean-under-\(R\), we do
  not require relational agreement of application results.

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

### Lean sketch 1: redefine cleanliness for function types

Keep `QTyp.poison` always `false` for `arrow/parrow`, but redefine:

- `qtypCleanUnder` (or a function-specific predicate) so that for
  `qt.etyp = arrow/parrow … p …`, cleanliness is determined by the *internal*
  poison `p` (and guard tags), not by `qt.poison`.

This keeps the existing “clean gating” pattern but moves the gate.

### Lean sketch 2: keep `qtypCleanUnder`, refine agreement predicates for closures

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

**Scope**: this direction is aimed at obstacle (2) (making the captured
environment agreement obligations line up with when we consider a function
relationally reliable).

## Consequences for Ott rules (high-level edits)

Under this direction (outer-clean closures), the Ott typing rules must be updated
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

- **What is the intended relational guarantee for dirty closures?**
  - Must captured environments agree on clean entries even when the closure is
    dirty, or is that intentionally not required?

- **Which poison carrier is authoritative for function reliability?**
  - Outer `Q.poison`, internal arrow poison `# p`, or a combination?

Once these are fixed, we can implement the corresponding Lean/Ott changes and
finish the `app` proof accordingly.

