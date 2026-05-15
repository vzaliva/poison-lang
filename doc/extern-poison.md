# Extern poison handling — design discussion

Status: **analysis / brainstorming**. This document captures the problem,
the design space we have explored, and the open questions. It is not yet
an implementation plan. We update it as the discussion progresses.

## 1. Background and motivation

The FR roadmap (`doc/ffi-axioms.md`) reached a wall on its first concrete
builtin: `abs` (`@12`). The example declaration is

```
extern pfn @12 x : (int) -> ((int :> clean {}))
```

which advertises a clean integer output for any integer input. The direct
boundary validation attempt (`LeanProofs/ExternProofs.lean`) ended with
`builtinAbs_cleanPost_obstruction` — a Lean proof that the post-shape
demanded by `ExternBoundarySpec` is unsatisfiable for this declaration:
the implementation produces `1` from `-1` and `2` from `2`, which cannot
satisfy clean integer agreement.

The current annotation system cannot honestly express the conditions
under which an extern's output is provably clean. This document
brainstorms what an honest model would look like.

## 2. What the current annotation system actually allows

Per the tree-sitter grammar (`parser/tree-sitter-poison/grammar.js`) and
the Ott application rules:

- **Extern argument** is `paren_type` — a bare surface `Typ`. No `:>`, no
  poison flag, no predicate. `(int)` is the only thing you can write.
- **Extern return** is `qtyp` — full qualified type. `(int :> clean {})`,
  `(int :> poisoned { p(x) })`, etc. The predicate body can reference the
  argument name.

The Ott application rule `app_extern_fn_simple_*` computes the result
poison as `join pc (join p1 (join p p3))` where `p3` is the **declared**
return poison. The argument's poison `p2` is **not** joined into the
result poison flag; it only enters the predicate-resolution context as
the binding `x |-> T1 :> join pc p2 { P2 }`.

Consequence: the declared return poison overrides the caller's argument
poison in the type-level result. That is the exact source of the `abs`
dishonesty.

## 3. Design exploration

### 3.1 Initial three modes

We initially considered three modes for how output cleanness could be
justified:

| Mode | Output cleanness from | Proof shape |
|---|---|---|
| A — polymorphic | Input cleanness, propagated structurally | Automatic |
| B — predicate-guarded | Input predicate + manual proof | Per-extern Lean proof |
| C — unconditional clean | Input-insensitive implementation | Per-extern Lean proof |

### 3.2 Collapse to a single mode

After discussion:

- **Mode A rejected.** The relation between input poison and output
  poison is governed by the extern's internal control flow and can
  branch on values. Consider a two-argument function where one argument
  is clean and the other is dirty: which one contributes to the output
  depends on runtime logic the annotation cannot see (the function may
  compare values, take one branch on the dirty input's value and a
  different branch otherwise, mix the two via arithmetic that may or
  may not cancel the dirty bits, etc.). Expressing output cleanness
  purely as a function of input cleanness is infeasible without
  effectively re-encoding the implementation in the annotation. A
  conservative over-approximation (e.g., "output poison = OR of input
  poisons") sidesteps the implementation but produces a result so
  pessimistic that downstream consumers must still depoison via
  predicates — there is no genuine cleanness payoff for the FR
  statement.

- **B and C merge.** C is B with a trivial (always-true) precondition.
  One proof shape, parameterized by a (possibly trivial) precondition.

Unified model:

> An extern is **trusted** for FR iff its author can supply a Lean proof
> (or, if we choose to take the author at their word, an axiom) that,
> under some statable precondition on the inputs (possibly trivial), the
> output honors its declared `QTyp` — i.e., FR-clean when declared
> clean, or poisoned with the declared latent predicate when declared
> poisoned. Otherwise the extern stays out of the trusted registry.
> Programs using untrusted externs typecheck but do not get FR.

### 3.3 Triage rule at declaration time

- **Trusted**: a precondition `P` exists such that for inputs satisfying
  `P`, the output honors its declared `QTyp` (FR-clean if declared
  clean, poisoned-with-declared-predicate if declared poisoned). The
  extern is paired with a Lean proof witnessing this, or — when we
  choose to take the author's word — with an axiom of the same shape.
- **Untrusted**: no such precondition exists, or none has been supplied.
  The extern can still be used by programs; FR is not derived for
  programs that use it.

## 4. Current-builtin status under this model

- **`abs`** — untrusted as declared. It reads its argument value
  directly, so the only precondition that yields clean output is "input
  is clean," which is already handled by standard typing and adds no
  value as a predicate annotation. There is no honest *interesting*
  precondition. The declaration should be removed, rewritten, or marked
  untrusted.

- **`max`** — same diagnosis. Output depends on both arguments.

- **`sqrt`-style externs** — candidate for the unified model with input
  precondition `x >= 0`. Implementation `if x >= 0 then Lean.sqrt x else 0`
  has a defensive runtime branch, but the FR cleanness comes from the
  input precondition (which constrains the inputs across two runs to
  agree by depoisoning), not from the runtime branch. **Currently not
  expressible** in the grammar (extern argument is bare `Typ`).

## 5. Analysis

### 5.1 Runtime / proof-time gap, and the "precondition" framing

At typecheck time, the call site knows the full `QTyp` of each argument
(including any predicates the caller has attached). The boundary proof,
however, is constructed *before* and *independent of* specific call
sites. It must commit up-front to which argument typings it covers.

This is where the "precondition" language comes from. A precondition
declares: "this proof handles calls whose argument typing satisfies *P*."
Callers whose argument typings do not satisfy *P* do not get the FR
guarantee for that call.

The proof's quantification is therefore not "for all values" but "for
all values whose typing satisfies the precondition."

### 5.2 What language for preconditions?

Preconditions could in principle be arbitrary logical formulas over
input values and captured environment values. We do **not** want to
build a general formula language.

Working compromise: preconditions are **predicates** — reusing the
language's existing `Predicate` machinery (`guardClosure`, `guardOnly`,
`noPred`). This rides on the existing tag-meaning / regime
infrastructure and keeps the typechecker uniform.

### 5.3 Where do preconditions live syntactically?

Two options for placing the precondition on an extern declaration:

- **Argument-side grammar extension.** Allow `arg_type: qtyp` for
  externs, mirroring how native `fn` / `pfn` definitions already accept
  `QTyp` arguments. Example: `extern pfn @N x : (int :> clean { x >= 0 })
  -> (int :> clean {})`.
- **Return-side encoding.** The current return-side predicate can
  reference the argument name. We could *interpret* a return predicate
  `clean { p(x) }` as "output is clean iff `p(x)` holds at the call
  site." This is close to the current semantics, just systematically
  under-exploited.

Trade-offs:
- Argument-side is more *natural*: the precondition is anchored where it
  is conceptually true.
- Return-side is *cheaper* (no grammar change) but mixes two distinct
  ideas — what the caller must establish vs. what the output guarantees.

### 5.4 What does a predicate on a return value mean?

A return-spec predicate `(int :> poisoned { P(x) })` is read as a
**latent depoisoning marker**: the return is poisoned at the boundary
and carries `P(x)` as a witness available for downstream depoisoning.
When downstream typechecking encounters a value-level check that
syntactically matches `P(x)`, the standard depoisoning machinery
treats the value as clean from that point on.

This reading aligns predicates on extern returns with the role
depoisoning predicates already play elsewhere in the language, and
matches the existing Ott / FR semantics without modification.

### 5.5 Predicates on output memory cells

An impure extern that writes to memory (e.g. `set_err` updating `errno`)
or any extern that allocates new ref-typed return values is effectively
producing **multiple outputs**: the immediate return value and the
memory cells it writes or creates. These cells should be treated by the
same model as the return value — each carries its own poison/predicate
post-state, and the trusted-extern proof obligation must cover them
under the precondition by the same shape as the return value.

### 5.6 Captured environment and input memory

All Poison functions take one immediate argument but can close over a
captured environment (e.g. `max @11` reads captured `a` plus argument
`b`). Captured-env values are conceptually **additional inputs** to the
extern, on the same footing as the immediate argument. The precondition
language must therefore admit predicates over both captured values and
the immediate argument; the proof obligation likewise quantifies over
captured-env typings.

This raises an adjacent question about **input memory**. Extern
dispatch can also read memory: pure externs may dereference ref-typed
arguments, and impure externs additionally read driver-allocated cells
(`errno` and similar). There is currently no annotation that declares
which memory cells an extern *reads* — only the ones it writes (via the
effects block on impure externs). Read-side memory is therefore
implicitly "any cell the extern chooses to look at," which an FR proof
must cover by quantifying over the entire memory under the regime.

Adding read-side memory annotations (e.g., a `reads:` clause mirroring
the effects clause) would let the extern's proof commit to a narrower
read set, simplifying the obligation. But it is a substantial
grammar/typechecker/proof extension.

### 5.7 Shape of the cleanness obligation

The cleanness obligation matches what FR already implements; this
section pins down the framing, not new semantics.

- A return declared **clean** must be FR-clean: outputs agree across
  pairs of runs whose inputs are `agreeOnClean`-equivalent (the
  standard FR agreement relation).
- A return declared **poisoned { P }** is poisoned at the boundary;
  the predicate `P` is a depoisoning marker (see §5.4) that downstream
  code can later match via a value-level check, triggering depoisoning
  in the standard FR way.
- The proof obligation tracks the declaration. Under the precondition,
  the implementation produces an output that honors its declared
  poison/predicate annotation — clean if so declared, poisoned-with-
  the-declared-predicate if so declared. The trusted-extern proof does
  not weaken or relax the declared semantics.

This is exactly the current FR semantics (e.g. `agreeValueUnder`'s
`withPred_true_eq` constructor for the depoisoned case). We do not
touch it.

### 5.8 Trusted-registry membership and the public FR theorem

Two distinct registries are involved and must not be conflated:

- **Runtime registry** (`ExternRegistry` in code): the map from extern
  ids to runtime implementations consulted by the evaluator at dispatch
  time. Its content determines whether a call evaluates successfully or
  raises a runtime error.
- **Trusted registry** (`TrustedRegistry` in code): the FR-side map from
  extern ids to (declaration, implementation, boundary-proof) triples,
  consulted only by the FR theorem. The two are linked: the trusted
  registry projects to a runtime registry via
  `TrustedRegistry.toRuntimeRegistry`.

If a program uses an extern absent from the **trusted registry**, the
public FR statement remains meaningful but weaker: FR holds relative to
the trusted entries that *are* present. The current bridge
(`doc/ffi-axioms.md`) allows the trusted registry to be partial.

An extern absent from the **runtime registry** is a different story:
dispatch fails at runtime, no successful boundary event occurs, and
there is no output to compare across runs, so FR is vacuous on those
paths. Under the unified model, programs that use externs which are
present in the runtime registry but **absent from the trusted
registry** typecheck and may even run successfully, but their FR
derivation is gated by whichever trusted entries cover the externs
they actually invoke. This needs a clear public-API statement.

### 5.9 Regime as FR theorem parameter

The guard regime `R` (per `doc/poison-lang-description.tex`,
"Guard Regime" definition at line 1116) is **not runtime state and
not source-level state**. It is a *universally quantified parameter
of the FR theorem*: the FR claim is "for every well-formed `R`, two
runs that conform to `R` produce agreeing outputs."

`R` is defined exactly on `K_S` — the set of guard tags that occur in
predicates attached to entries of the critical-input specification
`S`. Tags allocated *during* typechecking (e.g., for an extern's
output predicate) are not in `K_S` and not in `R`'s domain. The
"exactly on" is mechanized as a bidirectional constraint:
`LeanProofs/FaultRobustness.lean:71` (`wfRegime`) requires
`dom(R) ⊆ K_S` *and* `K_S ⊆ dom(R)`, and the FR theorem takes
`wfRegime` as a premise. The typechecker only ever shrinks `R`
(via `invalidateRegimeDeps` / `joinRegimes`); it never inserts.

**Two modes for the typechecker** (description doc lines 1143-1147):

- Source execution: `R = ∅`. Conservative. No depoisoning fires.
- FR reasoning: `R` instantiated for the two-run scenario. The if-
  rule's `R(k) = some true / some false` branches become reachable;
  the typechecker exploits regime-deterministic guard outcomes.

**Extern boundaries are quantified by the same R.** The extern trust
contract should be universally quantified over `R`, paralleling the
FR theorem's outer quantifier:

> For every well-formed `R`, for inputs whose typing is regime-
> consistent with `R`, the extern's implementation produces an output
> that honors its declared `QTyp` under `R`.

This parametrization gives the extern proof leverage on the **input
side** of the boundary: when a critical input flows into the extern,
the proof can assume `R(k)` determines whether the input is
agreement-clean. Under `R(k) = true`, the input is depoisoned and
agrees across runs; the deterministic implementation then produces
an agreeing output.

**A significant limitation.** Predicates allocated on the **output
side** of an extern get fresh tags that are not in `K_S` and so not
in `R`'s domain. Downstream code cannot use `R` to depoison such
outputs. Empirically: the if-rule's regime lookup returns `none` for
these tags and falls through to the conservative `if_std` joining
path, so the predicate is dropped at the join and the result stays
poisoned.

In effect: **extern functions cannot currently return results that
carry a predicate intended for later depoisoning**. This is a
substantial limitation. It means the latent-marker reading (§5.4) is
FR-decorative for extern outputs given the current regime mechanism;
the predicate annotation is type-level information that the FR
machinery does not act on.

**Design alternative left open: extend `R`'s domain.** One way to
lift the limitation is to allow `R` to constrain tags beyond `K_S` —
e.g., freshly-allocated tags from extern outputs. This would
require revising regime well-formedness to admit the larger domain,
defining regime consistency for the new tags (a value-level condition
that the extern's implementation establishes), and reworking the FR
theorem's quantification and the extern trust contract to thread the
extended `R`. This is a real and substantial design change, parked
for further consideration (§7.5).

**Alternative rejected: tag-sharing between extern outputs and
critical inputs.** See §6.2.

## 6. Resolved positions and rejected alternatives

### 6.1 Resolved

- The current `abs` declaration is **dishonest** — formally proved by
  `ExternProofs.builtinAbs_cleanPost_obstruction`.
- Modes B and C **collapse** to a single proof shape with a possibly
  trivial precondition.
- Externs without a statable precondition under which the output
  honors its declared `QTyp` are **not trusted** (i.e., absent from the
  trusted registry); their use does not block typechecking but does
  block FR.
- The cleanness obligation matches existing FR semantics: clean-
  declared outputs must be FR-clean; poisoned-declared outputs carry
  the declared predicate as a depoisoning marker for downstream code.
  The trusted-extern proof does not weaken or relax the declared
  semantics.
- A return-spec predicate is interpreted as a **latent depoisoning
  marker**.

### 6.2 Rejected alternatives

- **Mode A — purely structural poison polymorphism.** Output cleanness
  computed from input cleanness without a per-extern proof. The
  relation between input poison and output poison is governed by
  implementation-internal control flow that can branch on values; a
  structural annotation cannot capture this without re-encoding the
  implementation. The conservative over-approximation ("output dirty
  if any input dirty") gives no FR-useful clean output.
- **Return-value predicate as a "caller depoisoning gate."** The
  caller establishes `P(x)` to consume the value as clean. Logically
  consistent with the Ott rules but abuses the depoisoning predicate's
  intent — predicates are meant to match a runtime poison-condition
  check syntactically, not encode arbitrary caller-side preconditions.
- **Return-value predicate as an "output guarantee."** The extern
  asserts `P(x)` holds of the returned value. Stretches the
  depoisoning marker into a general post-condition.
- **Unconditional value-level cleanness (Y1).** Output agreement
  across any pair of runs regardless of inputs. Only constant-
  effective externs satisfy this; offers no design space.
- **Tag-sharing between extern outputs and critical inputs.** An
  extern's output predicate sharing its (freshly-allocated) tag with
  a critical-input predicate's tag, so the same `R(k)` would drive
  both. Rejected for multiple structural reasons: externs allocate
  fresh symbolic tags at each call site; tag identity is a
  typechecker-internal concern, not a source-level one; and tying an
  extern declaration's output to a program-side critical-input tag
  would muddy the trust boundary between declarations and the program
  that uses them.

## 7. Open questions

### 7.1 Predicate language expressiveness  *(from §5.2)*

Are existing `Predicate` types (`guardClosure`, `guardOnly`, `noPred`)
expressive enough for the cases we care about (sqrt-style, bounded
indexing, divmod with nonzero divisor)? Or do they need extension?

### 7.2 Syntactic placement of preconditions  *(from §5.3)*

Argument-side grammar extension (allow `arg_type: qtyp` for externs)
vs. return-side encoding (use the existing return-side predicate as
the precondition). Trade-offs analyzed in §5.3.

### 7.3 Concrete latent-marker example  *(from §5.4)*

Construct a concrete extern returning a value alongside a depoisoning
predicate, with downstream code performing the matching check. The
example should pin down whether existing `Predicate` machinery is
expressive enough, or expose the narrower-than-expected applicability
of the latent-marker reading.

### 7.4 Read-side memory annotations  *(from §5.6)*

Do we postpone read-side memory annotations, or treat them as a
parallel design strand to be specified now? At minimum, the
precondition language for read-side memory must be analyzed alongside
the argument/captured-env case so we do not commit to a precondition
shape that cannot extend to memory.

### 7.5 Extending `R`'s domain to internal tags  *(from §5.9)*

Should the guard regime `R` be allowed to constrain tags allocated
during typechecking (e.g., extern output predicate tags) in addition
to the current `K_S`-only domain? Without this extension, extern
outputs cannot carry FR-effective latent depoisoning markers — a
substantial limitation. The cost of the extension is revising regime
well-formedness, regime consistency (so it says something meaningful
about internally-allocated tags), and the FR theorem's quantification
structure. Parked for further consideration; not committed to.

## 8. Next steps (analysis-level)

1. Resolve §7.2 (precondition placement).
2. Resolve §7.4 (read-side memory annotations).
3. Resolve §7.1 (predicate language expressiveness).
4. Construct §7.3 (latent-marker example) to validate the
   interpretation against existing predicate machinery.
5. Sketch the proof obligation in Lean terms once §7.2 is pinned.
6. Identify or construct a concrete `sqrt`-style example in
   `examples/` to drive the design.
7. Decide what to do operationally with `abs` and `max`: leave declared
   but untrusted (i.e., not added to the trusted registry), remove from
   examples, or rewrite.
8. Update `doc/ffi-axioms.md` once the model is firm, replacing the
   current §1/§2 roadmap items with a target consistent with this
   document.
