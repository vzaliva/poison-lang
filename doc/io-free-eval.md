## IO-free evaluation mode: motivation and impact

### Problem statement

Two proof obligations rely on the premise that an expression is syntactically I/O-free (via `IOFree : Expr → Prop`), and attempt to conclude that evaluation is “pure” (or at least that it does not perform I/O). This reasoning fails in the presence of higher-order functions stored in runtime environments.

The core issue is that `IOFree` is a *syntactic* predicate over the surface expression. It does not constrain the bodies of closures that may be retrieved dynamically from `cfg.varEnv` during evaluation.

In particular, an application `Expr.app e1 e2` can evaluate `e1` to a closure `Value.closure x body env` obtained from the runtime variable environment (e.g. when `e1 = Expr.var f`). Even if `IOFree e1` holds, there is no guarantee that the retrieved closure body `body` is syntactically `IOFree`.

### Two concrete occurrences

- **`LeanProofs/SemanticsProperties.lean` (`beval_IOFree_eq_pure`, application case)**:
  - The intended statement informally reads: “if `IOFree e`, then `beval` is observationally equal to a pure computation”.
  - For `e = Expr.app e1 e2`, evaluation may proceed into a closure body that is not syntactically `IOFree`, because the closure can come from `cfg.varEnv`.
  - As a result, an `IOFree` premise about the *syntax* of `e` is insufficient to exclude I/O effects triggered by the closure body.

- **`LeanProofs/FaultRobustnessProofs.lean` (`stepFR_app`)**:
  - The step theorem’s induction hypothesis `StepFR_IH` requires `IOFree` to apply recursively.
  - In the application case, the proof strategy requires a recursive appeal to the IH on the *closure body*.
  - However, the closure body is not a syntactic subexpression of the original program term in the case where the closure is retrieved from `cfg.varEnv`. Consequently, `IOFree` cannot be recovered for the body from `IOFree e1`.

These two failures are instances of the same underlying mismatch: syntactic I/O-freeness does not propagate through dynamically retrieved function bodies.

### Proposed solution: runtime IO-free mode

A possible resolution is to introduce an explicit *runtime* evaluation mode that rejects I/O operations whenever an I/O primitive is encountered. The key point is that this restriction is semantic (about the executed run), rather than syntactic (about the source term).

#### Informal semantics

Extend evaluation with a flag (or mode) indicating whether I/O is permitted:

- In **normal mode**, evaluation behaves as usual.
- In **IO-free mode**, any attempt to execute:
  - `rand`, `frand`,
  - `printInt`, `printString`,
  - `externVal`, `externFn`, `externPfn`,
  results in a distinguished “I/O forbidden” outcome.

The key property becomes semantic rather than syntactic:

- **If evaluation in IO-free mode terminates successfully**, then the run did not perform I/O (because any I/O attempt would have produced an error).

This directly addresses the closure-body issue: even if a closure body is not syntactically `IOFree`, it cannot produce a successful result in IO-free mode if it tries to execute I/O.

### Potential implementation approach (Lean)

#### Result-type extension: distinguish “I/O forbidden”

To support crisp lemmas, it is useful to distinguish “I/O was attempted in IO-free mode” from ordinary runtime errors (stuckness).

Concretely, extend `LeanPoison.EvalResult` with an additional constructor, for example:

- `| ioForbidden : EvalResult`

In IO-free mode, the I/O primitives return `ioForbidden` rather than reusing `runtimeError _`.

This does not change the success/divergence story, but it makes it easy to formulate and prove lemmas that classify failures precisely.

#### Minimal API change: add a mode parameter

Introduce a small mode type and thread it through the evaluator:

- Add:
  - `inductive EvalMode where | normal | ioFree`
- Modify:
  - `LeanPoison.beval : Nat → Config → Expr → Bool → IO EvalResult`
  to:
  - `LeanPoison.beval : EvalMode → Nat → Config → Expr → Bool → IO EvalResult`

Then, in the cases for I/O primitives (`rand`, `frand`, printing, externs), branch on `mode`:

- If `mode = ioFree`, return `.ioForbidden` immediately.
- If `mode = normal`, preserve current behaviour.

`bevalFunctionBody` should pass the mode through unchanged; the mode is orthogonal to `pureMode` (which tracks “pure closure body” behaviour).

#### Compatibility with existing code

- The interpreter entry point can continue to run in `normal` mode.
- Proof developments can selectively run in `ioFree` mode.

### Proof impact and expected refactor

The main benefit is that several lemmas can be re-stated in a way that avoids the problematic reliance on syntactic `IOFree`.

#### Suggested helper lemmas

The following lemmas (stated informally) are particularly helpful for proof engineering:

- **Mode monotonicity (success transfers to normal mode)**:
  - If `beval ioFree … = .success c v`, then `beval normal … = .success c v`.
  - Intuition: IO-free mode is stricter; it can only turn potential I/O steps into `ioForbidden`.

- **Success excludes I/O attempts**:
  - If `beval ioFree … = .success …`, then evaluation did not return `ioForbidden` at any point (by construction).
  - This is the semantic replacement for “`IOFree e` excludes I/O”.

- **World irrelevance for successful IO-free runs (optional, if keeping world-indexed proofs)**:
  - If `beval ioFree …` succeeds, the result is world-insensitive (no `IO` was executed), enabling conversions between world-indexed and world-free relations on the success fragment.

These lemmas are exactly what is needed to address the application/closure problem: latent I/O inside dynamically retrieved closures becomes impossible in the success case, without requiring closure bodies to be syntactically `IOFree`.

#### For `SemanticsProperties`

Rather than proving “`IOFree e → beval = pure …`”, one can aim for:

- a lemma that relates world-indexed and world-free notions *under IO-free mode* (or shows world irrelevance for successful runs in IO-free mode), and
- a lemma that successful evaluation in IO-free mode implies a world-insensitive/pure characterisation.

This avoids needing to show that closure bodies are syntactically `IOFree`.

#### For `FaultRobustnessProofs`

There are two plausible refactor directions:

- **Replace the syntactic `IOFree` premise with a semantic premise**: proofs proceed by assuming successful evaluation occurs in IO-free mode.
- **Retain `IOFree` as an optional restriction on source terms**, but do not rely on it to control effects in application; instead, use IO-free mode to ensure that any latent I/O in retrieved closures prevents success, making the corresponding success case unreachable.

In both cases, the application proof (`stepFR_app`) no longer needs an `IOFree` hypothesis for the dynamically retrieved closure body in order to justify “no I/O happened”.

### Trade-offs and risks

- **Semantic shift**: IO-freeness becomes a runtime property (“successful under IO-free mode”) rather than a purely syntactic fragment restriction. This is often acceptable, but it changes the statements and proof architecture.
- **Error vs divergence distinctions**: rejecting I/O by returning `runtimeError` changes which runs count as “terminating” versus “stuck”. Proof statements phrased purely in terms of successful termination must account for this.
- **Engineering cost**: threading a mode parameter through `beval` and related helpers requires updating callers, lemmas, and potentially existing proof scripts that pattern-match on `beval`’s definition.

