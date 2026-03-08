# Current `stepFR_app` Framing / Unary Witness Blocker

This note isolates the current framing blocker on the path to finishing
`stepFR_app`.

Status:

- this is a live technical memo, not a history log
- the active execution plan is in `doc/app-proof-plan.md`
- discarded routes and checkpoint history are in `doc/app-proof-history.md`
- keep this file focused on the current blocker and theorem-design implications, not a
  step-by-step execution checklist

Scope:

- in scope: the different-body `arrow` / `parrow` fallback subproofs inside
  `stepFR_app`
- in scope: the unary theorem surface needed by those subproofs
- out of scope: unrelated `stepFR_app` cleanup, all `stepFR_ite_*` proof work, and all
  `kwhile` proof work

Constraint from outside this workstream:

- there is a separate known type-system / regime-handling blocker that currently prevents
  `stepFR_ite_*` from being proved
- that work is tracked in GitHub issue `#128`
- that issue is being worked on in another branch
- this app work must therefore avoid taking `ite` proofs as a prerequisite
- but it should also avoid app-specific theorem shapes that would make a later `ite`
  proof harder once that external blocker is fixed

Practical implication:

- because closure bodies are general `Expr` / `PExpr`, the app route cannot literally
  erase `ite` from the theorem domain
- the realistic near-term goal is narrower: avoid any *new* `ite` proof work on this
  branch, while keeping the theorem shape reusable for later completion under issue
  `#128`

## 1. Exact Remaining Obligation

The remaining `stepFR_app` location blocker is no longer local branch plumbing.

Inside the different-body fallback branches, the proof must eventually establish the
locations half of `agreeOnClean` for the final app result. After the recent narrowing,
the only hard situation is:

- a final location `l` is clean in the joined app result
- `l` is inherited from the pre-body memory typing environment
- the two runs executed different bodies, so there is no shared body witness to reuse

For such an inherited final-clean location, the proof needs the chosen post-body
realization maps `θ₀_body` and `θ₁_body` to preserve enough runtime information to
finish `agreeLocUnder`:

- if `l` was unrealized before the body, both post-body maps must still leave it
  unrealized, or
- if `l` was realized before the body, both post-body maps must preserve the same
  realized address and integer

This is exactly what
`PreservesInheritedFinalCleanLocsOneRun`
encodes for one run.

Important structural fact:

- closure bodies are general `Expr` / `PExpr` terms in this language
- both syntactic categories include `ite`
- so the app route cannot rely on a claim that fallback bodies are "never `ite`"
- excluding `ite` from the app dependency cone therefore has to come from theorem-boundary
  design, not from body syntax

## 2. What Is Already Solved

Several earlier subproblems are now closed and should not be reopened.

### 2.1. Typing-side origin is solved

The theorem
`typecheckExpr_clean_lookup_origin_of_pc_true`
already gives the static half of the story:

- if a body is typed under `ctx.pc = true`
- and the final typed memory still contains a clean location `l`
- then `l` already existed in the input memory typing environment, with a clean
  pre-body type under the input regime

So the remaining problem is not "where did the final clean location come from?" at the
typechecker level.

### 2.2. Poisoned-control write semantics were already strengthened

The language semantics were changed so that writes under poisoned control strip stored
predicates.

Effect:

- poisoned control no longer allows the previous "write a guarded value, keep the guard,
  later look clean-under-regime" route
- this removed the earlier typing-level obstruction in the `arrow` case

That change validated the basic direction of the framing plan: under `pc = true`, final
clean locations should behave like inherited preserved locations, not newly cleaned-up
writes.

### 2.3. Local app packaging is solved

The narrowed `arrow` and `parrow` fallback branches in `StepFRApp.lean` are no longer
blocked on ad hoc local reasoning about fresh versus inherited locations.

What remains is upstream:

- obtain the right one-run witness for each executed body
- with the right preservation fact on that same witness

## 3. Why The Current Unary Interfaces Still Do Not Finish It

### 3.1. `StepFR_single_run_core` is too weak

`StepFR_single_run_core` extracts a sound one-run witness from `StepFR`:

- a post-run `θ'`
- value typing / regime / runtime-instantiation facts for the result

But it does not constrain `θ'` with the inherited-final-clean preservation property
needed by the different-body app branches.

That missing fact cannot be recovered afterward from an arbitrary witness:

- `wfExtendsMap` preserves existing `some` realizations, but not `none`
- `runtimeInstantiatesCtx` permits realizing old typed locations
- so "this final-clean inherited location stayed unrealized/preserved" must hold for the
  same chosen `θ'`, not for some unrelated post hoc witness

### 3.2. The old direct `StepFR_single_run` route is obsolete

The current `StepFR_single_run` wrapper still ends in `sorry`, but that is not the right
fix path anymore.

Two earlier ideas are now ruled out:

- the original input-clean statement was too strong for impure bodies
- the output-conditioned replacement still cannot be recovered as a thin wrapper over
  `StepFR_single_run_core`, because witness choice matters

So the remaining app blocker is not "finish the old wrapper".

### 3.3. `StepFRSingleRunFinalCleanPcTrue` is shaped too broadly

The current induction-side theorem
`StepFRSingleRunFinalCleanPcTrue`
is closer to the right idea: it aims to produce a one-run witness under `ctx.pc = true`
together with `PreservesInheritedFinalCleanLocsOneRun`.

The problem is its payload shape.

Right now it still asks for the full post-context witness package, essentially mirroring
`StepFR_single_run_core`:

- `wfTagMeaningCtx`
- `wfTypeContext`
- `wfConfig`
- `runtimeInstantiatesCtx`
- `regimeConsistentWithCtx`
- `consistentWithRegime`
- `valueConsistentWithRegime`
- plus the preservation fact

That is manageable for straight-line cases and local writes such as `assign`, but it
overreaches for conservative `ite` modes:

- runtime executes only one branch
- typing produces a conservative join of both branches
- the app fallback only needs the chosen executed-run witness and preservation fact
- the extra joined-post-context obligations dominate the proof while adding little or no
  value to `stepFR_app`

This matters operationally, not just aesthetically:

- proving `stepFR_ite_*` is out of scope for the app effort
- that work is already owned elsewhere
- there is also a separate known type-system / regime blocker on the `ite` side
  (GitHub issue `#128`)

So any app route that still requires us to finish `ite` cases upstream is the wrong
route and should be rejected, not merely deprioritized.

At the same time, "reject the route" does **not** mean "special-case around `ite`
forever". The app theorem boundary should be narrowed just enough to avoid the current
external blocker, while staying semantically natural enough that `ite` can later consume
the same unary infrastructure after its own blocker is fixed.

So the active blocker is now:

- not the preservation statement itself
- not the branch-clean transport itself
- but the theorem surface that packages too much around the witness

## 4. What The App Proof Actually Needs

The app fallback branches need an app-focused one-run theorem for bodies typed under
`pc = true`.

Implementation choice:

- replace `StepFRSingleRunFinalCleanPcTrue` in place with this narrower statement,
  rather than introducing a second theorem name alongside it

At minimum, it needs to return a chosen `θ'` with the facts that `stepFR_app` actually
consumes for the executed body result:

```lean
∃ θ',
  wfExtendsMap θ θ' ∧
  valueHasETyp θ' o res.qualType.etyp ∧
  runtimeInstantiatesCtx (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
  consistentWithRegime predSat (ctxAfter ctx res).regime
    (ctxAfter ctx res) cf.memory cf.varEnv θ' ∧
  valueConsistentWithRegime predSat (ctxAfter ctx res).regime
    res.qualType cf.memory θ' o ∧
  PreservesInheritedFinalCleanLocsOneRun ctx res μ cf.memory θ θ'
```

Two design constraints matter here:

- the preservation fact must be attached to that same `θ'`
- the theorem should not force joined-post-context obligations that the app fallback does
  not consume

If additional fields are convenient later, they should be added only when a downstream
consumer actually uses them, or layered via a separate wrapper.

## 5. Remaining Technical Work

These are theorem-design implications of the blocker, not the execution checklist. The
concrete work order lives in `doc/app-proof-plan.md`.

### 5.1. Cut `ite` out of the dependency cone

This is the highest-risk design task.

Success criterion:

- the theorem used by `stepFR_app` no longer requires proving conservative `ite` cases on
  this branch
- `ite` should be treated as a reason to refactor the theorem boundary, not as a
  constructor we plan to finish ourselves
- this must hold even though closure bodies may themselves be `ite`

### 5.2. `deref`

Once the dependency cone is narrowed, `deref` is the most relevant remaining constructor
on the app path because it can read guarded values and interacts with the final-clean
origin theorem.

Expected route:

- use `typecheckExpr_clean_lookup_origin_of_pc_true` for the subexpression as needed
- transport the executed-run witness without introducing any new write-specific behavior

### 5.3. `vlet`

This is mainly a composition case, but it must compose the preservation fact on the same
chosen witness. The existing helper
`PreservesInheritedFinalCleanLocsOneRun.compose`
is the intended tool here.

### 5.4. `kwhile`

Out of scope permanently.

The app theorem surface should be structured so `stepFR_app` does not depend on a theorem
that still drags a `kwhile` branch through the dependency cone. In practice, that means
the narrowed unary theorem and any app-consumed clean-origin theorem may need app-relevant
variants that exclude `kwhile` rather than reusing broader theorems unchanged.

## 6. Suggested Ways Forward

### Way 1. Narrow the unary theorem surface first

Recommended first move:

- split or prioritize an app-focused theorem surface for bodies typed under `pc = true`
- do that refactor in place, replacing the abandoned broad route instead of preserving it
  in a separate legacy file
- make the preservation-focused witness its primary output
- keep the stronger full-witness theorem, if needed at all, as a later wrapper or
  extension

Reason:

- this directly attacks the current highest-risk obstruction
- it avoids paying the conservative-`ite` cost for facts the app proof does not use
- more importantly, it avoids routing the app proof through `ite` work that is explicitly
  out of scope
- git history is sufficient for recovering discarded proof fragments if needed later
- the narrowing should still be principled, so the later `ite` proof can reuse or wrap
  the same theorem family instead of being boxed out by an app-only hack

### Way 1a. Concrete near-term assembly strategy

Use the current induction-side route, but change its role:

- replace `StepFRSingleRunFinalCleanPcTrue` in place with the narrowed payload
- reuse the existing strong-induction/IH scaffolding around that theorem
- retarget the already proved non-`ite` case lemmas to the narrowed statement
- do not expand the deferred `ite` or `kwhile` branches on this branch

This does not "solve `ite`". It only ensures that:

- the theorem boundary used by `stepFR_app` is the right one
- `stepFR_app` stops depending on the wrong broad payload
- future `ite` work can later fill the remaining branches against the same theorem shape

### Way 2. Refuse any theorem route that still requires `ite`

Recommended decision rule:

- if a proposed unary theorem still needs conservative `ite` cases, stop and refactor the
  theorem boundary
- do not continue proving upstream constructors on that route

Reason:

- `ite` is not just "hard"; it is off-limits for this workstream
- so theorem design must accommodate that constraint directly

### Way 3. Finish only the app-relevant remaining constructors

Recommended order:

1. `deref`
2. `vlet`

Reason:

- once `ite` is excluded from the route, these are the remaining constructors that matter
  on the app path

### Way 4. Rewire `stepFR_app` as soon as the narrow theorem is usable

Do not wait to finish a broader theorem first.

Once the narrowed unary theorem covers the body shapes that appear in the app fallback:

- switch the different-body `arrow` / `parrow` sites away from `StepFR_single_run`
- consume the new one-run witness directly

That is the point where the real benefit lands for `stepFR_app`.

### Way 5. Keep `StepFR` itself unchanged unless this route collapses

Widening `StepFR` remains the wrong default move:

- it would spread app-specific witness work across many unrelated `stepFR_*` proofs
- it increases blast radius before the app-focused unary route has actually failed

## 7. Non-Directions

Do not spend more time on these routes unless the current app-focused unary route fails
for a specific reason:

- do not try to revive the original direct strengthening of `StepFR_single_run`
- do not try to derive the needed preservation fact after the fact from an arbitrary
  `StepFR_single_run_core` witness
- do not widen `StepFR` preemptively
- do not accept a route that makes `stepFR_app` depend on proving `stepFR_ite_*`
- do not use an app-specific workaround that would make a future `ite` proof strictly
  harder once the separate regime/type-system blocker is removed
- do not invest proof work in `kwhile`

## 8. Practical Success Condition

This framing issue is resolved for `stepFR_app` when all of the following are true:

- the different-body `arrow` / `parrow` fallback branches no longer depend on the current
  `StepFR_single_run` wrapper
- they consume a one-run witness produced specifically for bodies typed under `pc = true`
- that witness carries `PreservesInheritedFinalCleanLocsOneRun`
- the theorem providing that witness does not make `stepFR_app` depend on any `ite`
  proof work
