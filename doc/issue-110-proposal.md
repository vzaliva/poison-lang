## Issue #110: Strengthening `valueHasETyp` for closure typing

Original issue: https://github.com/vzaliva/poison-lang/issues/110

**Summary.** The `valueHasETyp.closure` (and `.peClosure`) constructors accept
any closure as having any arrow type without constraint. This permits a
runtime context in which a closure `fun x => true` is typed as `int → int`,
breaking preservation.

**Related issues.** Implementing this proposal resolves blockers 1 and 3 of
[#93](https://github.com/vzaliva/poison-lang/issues/93).

---

## Root Cause

The constructors in question (`TypeSafety.lean`, lines 307–310):

```lean
  | closure (x e env st1 st2 p tcl):
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure (x pe env st1 st2 p tcl):
      valueHasETyp θ (Value.peClosure x pe env) (ETyp.parrow st1 st2 p tcl)
```

impose no relationship between the runtime closure `(x, e, env)` and the arrow
type `ETyp.arrow st1 st2 p tcl`. The parameters are universally quantified
and entirely unconstrained.

Meanwhile, the arrow type already carries the relevant information for
establishing this link: `ETyp.arrow st1 st2 p tcl` includes a list of
`FnTClosure` entries, each of the form
`FnTClosure.regular x_i e_i tenv_i`, recording the parameter name, body
expression, and captured variable types from the point of closure creation
(`Typecheck.lean`, line 751 for `fn`; line 767 for `pfn`).
The fix should require the runtime closure to be consistent with this
recorded information.

---

## Proposed Solution

### Strengthened constructors

Replace the unconstrained constructors with versions that demand:

1. **Syntactic matching**: the closure's parameter name and body match
   some entry in the typing closure list `tcl` (existential witness).

2. **Recursive environment typing via lookup**: the closure's captured
   runtime environment `env` is well-typed according to the captured type
   environment `tenv` recorded in that entry, using first-match `lookup`
   semantics (not list membership) and `valueHasETyp` recursively.

#### Impure closures

```lean
  | closure {x e env st1 st2 p tcl} {θ}
      {tenv : CapturedVarEnv}
      (htcl : FnTClosure.regular x e tenv ∈ tcl)
      (henv : ∀ y qt, tenv.lookup y = some qt →
         ∃ v, env.lookup y = some v ∧ valueHasETyp θ v qt.etyp) :
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
```

#### Pure closures

`Value.peClosure` stores the body as `Expr`, whilst `PFnTClosure.regular`
stores it as `PExpr`. The syntactic matching must bridge this type mismatch
via `Expr.toPExpr?`, following the pattern already established in
`agreeValueUnder.clean_internal_parrow` (`FaultRobustness.lean`, line 589):

```lean
  | peClosure {x body env st1 st2 p tcl} {θ}
      {pbody : PExpr} {tenv : CapturedVarEnv}
      (hpure : Expr.toPExpr? body = some pbody)
      (htcl : PFnTClosure.regular x pbody tenv ∈ tcl)
      (henv : ∀ y qt, tenv.lookup y = some qt →
         ∃ v, env.lookup y = some v ∧ valueHasETyp θ v qt.etyp) :
      valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p tcl)
```

### Why lookup rather than list membership

Runtime variable semantics use first-match lookup on association lists:
`VarEnv.lookup` calls `List.lookup` which returns the first match
(`Runtime.lean`, line 38), and `VarEnv.update` prepends new bindings
(`Runtime.lean`, line 45). The captured type environment `CapturedVarEnv`
follows the same convention (`Syntax.lean`, line 554).

Using list membership `(y, qt) ∈ tenv` would allow "typed somewhere in the
list" whilst the runtime `env.lookup y` may return a *different* head
binding. This mismatch would render the invariant unsound. The
`agreeCapturedEnv` relation in `FaultRobustness.lean` (lines 652–653)
already uses `ρcap.lookup x = some v`, providing a precedent for
lookup-based environment typing.

### Why syntactic matching is necessary

Without linking the runtime body to the body recorded in the typing closure,
the counterexample from issue #110 remains valid: nothing prevents claiming a
closure with body `true` has type `int → int`. Syntactic matching forces
the runtime body to be one of the bodies the type checker has seen and
recorded.

### Why recursion via `valueHasETyp` is necessary

The captured environment `env : VarEnv` may contain closure values. These
closures must themselves satisfy the strengthened invariant. The `henv`
premise references `valueHasETyp θ v qt.etyp` recursively: if `v` is a
closure and `qt.etyp` is an arrow type, Lean demands `htcl` and `henv`
evidence for it, and so on down to base values. No mutual inductive or
auxiliary fixpoint is required.

This is well-founded because each recursive step descends into a value
structurally contained within another value's captured environment. Lean
accepts the definition because `valueHasETyp` appears in the `henv` premise
in a strictly positive position (under `∀ → ∃ → ∧`).

### Why existential (not universal) matching over `tcl`

The matching is **existential** ("any"): the runtime closure must match
**some** entry in `tcl`, not every entry.

Closure sets are merged by union/dedup at join points: conditionals with
function-typed results union the branch closure lists
(`Typecheck.lean`, line 1688; `Syntax.lean`, line 795), and multi-closure
application joins result closure lists (`Typecheck.lean`, line 375). At
runtime, only one branch executes, producing a single closure whose `(x, e)`
came from one branch and generally differs syntactically from entries in the
other branch's list. Universal matching with syntactic body matching is
therefore too strong to survive closure-list union.

This choice is consistent with the existing `agreeValueUnder` relation,
which already uses existential witnesses for closure agreement:
`htcl : tcl ∈ tcls` (`FaultRobustness.lean`, line 570). Existing lemmas
`mem_mergeFnTClosures_left` and `mem_mergeFnTClosures_right`
(`TypeSafety.lean`, lines 6450–6466) support weakening through merged
closure sets.

### How extern typing closures are handled

Arrow types may contain `FnTClosure.extern` (or `PFnTClosure.extern`) entries
alongside `FnTClosure.regular` entries. However, runtime successful
evaluation never produces extern closures as `Value.closure` or
`Value.peClosure` values — extern functions are handled by dedicated
evaluation paths. Consequently, the existential witness `htcl` always
targets a `FnTClosure.regular` (or `PFnTClosure.regular`) entry. Extern
entries in `tcl` are simply not selected by the witness and impose no
additional obligations on the runtime closure.

---

## Impact on Existing Proofs

### Proofs that construct `valueHasETyp.closure` / `.peClosure`

These must now provide `htcl` and `henv` (and `hpure` for `peClosure`).
Affected sites:

1. **`preservation_fn`** (`PreservationProofs.lean`, line 1442).
   Currently uses bare `constructor`. After the change, the proof must supply:
   - `htcl`: membership in the singleton list
     `[FnTClosure.regular x body (VarTypeEnv.toCaptured ctx.varEnv)]` —
     trivially `List.Mem.head _`.
   - `henv`: for each `y` with `tenv.lookup y = some qt`, the runtime
     environment `config.varEnv` satisfies `env.lookup y = some v` with
     `valueHasETyp θ v qt.etyp`. This follows from the
     `runtimeInstantiatesCtx` hypothesis, which already states that every
     variable in `ctx.varEnv` has a corresponding well-typed runtime value.

   A bridge lemma linking `runtimeInstantiatesCtx` to the `henv` form
   over `VarTypeEnv.toCaptured` may be needed.

2. **`preservation_pfn`** (`PreservationProofs.lean`, line 1491).
   Analogous to `preservation_fn`, with the additional requirement of
   providing `hpure : Expr.toPExpr? body = some pbody`. This fact is
   already available in the proof context: the type checker calls
   `body.toPExpr` and succeeds (the `split` on line 1473 handles the
   failure case).

3. **`valueHasETyp_extends`** (`FaultRobustnessProofs.lean`, line 1942).
   This lemma shows `valueHasETyp` is monotone in the realisation map `θ`.
   The closure case currently re-applies the constructor with no premises.
   After the change, it must thread `htcl` (unchanged), `hpure` (unchanged,
   for pure closures), and provide an updated `henv` where each
   `valueHasETyp θ₀ v qt.etyp` is replaced by `valueHasETyp θ₁ v qt.etyp`
   using a recursive appeal to the same `valueHasETyp_extends` lemma.

   This recursive structure means `valueHasETyp_extends` can no longer be
   proved by simple `cases` on the top-level constructor. It will need
   structural induction on the `valueHasETyp` derivation (or well-founded
   induction on values).

### Proofs that pattern-match on `valueHasETyp.closure` / `.peClosure`

These gain access to `htcl`, `henv` (and `hpure`) as additional hypotheses,
which is strictly more information. No breakage is expected; some proofs may
become easier.

### `preservation_app` (currently `sorry`)

This is the primary beneficiary. With the strengthened invariant, the proof
sketch is:

1. By IH on `e1`: evaluation produces `closure(x, e, env)` with
   `valueHasETyp θ v (arrow st1 st2 p tcl)`.
2. Extract `htcl`: `FnTClosure.regular x e tenv ∈ tcl`.
3. Extract `henv`: the captured environment `env` is well-typed w.r.t.
   `tenv` (via lookup).
4. By IH on `e2`: the argument `v2` has the expected type.
5. The type checker processed entry `(x, e, tenv)` (among others in `tcl`
   via `List.mapM` at `Typecheck.lean`, line 1545): it typechecked body `e`
   in context `tenv[x ↦ argType]` and obtained some result type. By IH on
   the body (using `henv` to establish `runtimeInstantiatesCtx` for the
   closure's context), the runtime result has this type.
6. The overall result type (from joining all entries) subsumes the specific
   entry's result.

### Preservation for conditionals with arrow-typed results

When the type checker produces `arrow st1 st2 p (tcls2 ∪ tcls3)` by joining
the then- and else-branches, and only one branch executes at runtime, the
preservation proof must show that the branch-specific `valueHasETyp` lifts to
the joined type. A **weakening lemma** is needed:

```lean
lemma valueHasETyp_closure_weaken_tcl
    (h : valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p₁ tcls₁))
    (hsub : ∀ tc, tc ∈ tcls₁ → tc ∈ tcls₂) :
    valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p₂ tcls₂)
```

The pure analogue must thread `hpure`:

```lean
lemma valueHasETyp_peClosure_weaken_tcl
    (h : valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₁ tcls₁))
    (hsub : ∀ tc, tc ∈ tcls₁ → tc ∈ tcls₂) :
    valueHasETyp θ (Value.peClosure x body env) (ETyp.parrow st1 st2 p₂ tcls₂)
```

With existential matching, both follow immediately from subset inclusion on
the witness `htcl` (and preservation of `hpure` for the pure case). The
existing `mem_mergeFnTClosures_left`, `mem_mergeFnTClosures_right`,
`mem_mergePFnTClosures_left`, and `mem_mergePFnTClosures_right` lemmas
(`TypeSafety.lean`, lines 6450–6480) provide the subset facts for merged
closure sets.

---

## Summary of Required Changes

1. **`TypeSafety.lean`**: replace the `closure` and `peClosure` constructors
   of `valueHasETyp` with the strengthened versions above (lookup-based
   `henv`, `toPExpr?`-bridged `peClosure`).

2. **`PreservationProofs.lean`**: update `preservation_fn` and
   `preservation_pfn` to provide `htcl`, `henv`, and (for `pfn`) `hpure`.
   Add a bridge lemma from `runtimeInstantiatesCtx` to the lookup-based
   `henv` form over `VarTypeEnv.toCaptured`.

3. **`FaultRobustnessProofs.lean`**: update `valueHasETyp_extends` to handle
   the recursive `henv` premise (structural induction on `valueHasETyp`
   derivation).

4. **`TypeSafety.lean`**: add the weakening lemmas
   `valueHasETyp_closure_weaken_tcl` and `valueHasETyp_peClosure_weaken_tcl`
   for use in conditional preservation proofs. The pure analogue must
   thread/preserve `hpure`.

5. **`PreservationProofs.lean`**: the `preservation_app` proof (`sorry`)
   should become provable using the strengthened invariant.
