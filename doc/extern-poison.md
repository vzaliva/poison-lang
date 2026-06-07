# Extern poison handling — design note

Status: **regime and argument-condition implementation complete**. The
extern-produced regime-tag mechanism is implemented and proven: extern ids can
be selected in the fault-robustness scenario, selected extern return/effect tags
are inserted into the active regime at call sites, the proof stack uses extended
regime evolution, and the executable supports `--extern-regime`. Argument-side
extern preconditions are also implemented: extern callable arguments accept
qualified annotations, the typechecker rejects calls that do not satisfy the
declared argument condition, curried extern levels are checked uniformly, and
the proof stack threads the clean/poison part of the condition through trusted
boundary reachability. Concrete trusted specs exist for `abs` and the curried
`max` pair. The active read-dependency work lives on the
`extern-env-deps` branch: guarded `captures:` are complete at the
typecheck/trusted-call-boundary level, memory-read `!r` captures are complete
for the representative explicit-reference-argument path, and branch-join capture
conjunction merging is complete.
The broader remaining design work is predicate-language validation,
latent-marker examples, and concrete validation of the remaining live trusted
extern specs.

Related documents:

- `doc/ffi-proposal.md` is the authoritative FFI status and roadmap document.
- `doc/ffi-axioms.md` is the proof-boundary reference for trusted extern
  evidence and the FR theorem interface.
- `doc/extern-env-deps.md` specifies `captures:` for environment and memory
  read dependencies; this file treats that as the selected read-side dependency
  model.
- `doc/extern-env-deps-plan.md` tracks the active implementation branch for
  `captures:` until it merges to `ffi`.

## 1. Purpose and scope

Extern declarations are FR contracts. A trusted extern that advertises a clean
result must also state enough input conditions for the trusted proof to show
clean agreement across paired runs. For example, this declaration is not a valid
trusted clean-output contract:

```poison
extern pfn @12 x : (int) -> ((int :> clean {}))
```

It advertises a clean integer output for any integer input. That is too strong:
two dirty integer inputs need not agree, and `abs (-1) = 1` while `abs 2 = 2`.
A trusted clean-output declaration for `abs` therefore uses a clean argument
condition:

```poison
extern pfn @12 x : (int :> clean {}) -> ((int :> clean {}))
```

This document describes the current source-language contract for extern
argument conditions, return/effect poison meaning, regimes, and trust triage.
The proof-boundary packaging lives in `doc/ffi-axioms.md`; read dependencies
over captured environment and memory live in `doc/extern-env-deps.md`.

## 2. Annotation surface

Per the tree-sitter grammar (`parser/tree-sitter-poison/grammar.js`) and
the Ott application rules:

- **Extern argument** is a qualified type annotation. The surface syntax mirrors
  native function arguments, e.g. `(int :> clean {})` or
  `(int :> clean { 1, v => v >= 0 })`. The parser/AST keeps the surface pieces
  (`Typ`, clean/poison flag, syntax predicate); typechecking resolves them to a
  concrete `QTyp` stored on the extern closure summary used at application.
- **Extern return** is `qtyp` — full qualified type. `(int :> clean {})`,
  `(int :> poisoned { p(x) })`, etc. Return semantics are unchanged: the
  predicate body can reference the argument name and is a latent depoisoning
  marker on the produced value.

At an extern call, the typechecker compares the actual argument `QTyp` with the
declared extern argument condition. The relation is deliberately structural:
base/runtime types must match; a declared-clean argument requires the actual
argument to be clean under the current regime; a declared `noPred` imposes no
predicate check; and a declared predicate requires the actual argument to carry
the same predicate shape. There is no general logical implication engine.

If the condition is not satisfied, the call is rejected at typecheck time. If it
is satisfied, the declared return `QTyp` is used as the output contract. This
keeps caller-side obligations on the argument and producer-side promises on the
return.

## 3. Design

### 3.1 Trust model

> An extern is **trusted** for FR iff its author can supply a Lean proof
> (or, if we choose to take the author at their word, an axiom) that,
> under some statable precondition on the inputs (possibly trivial), the
> output honors its declared `QTyp` — i.e., FR-clean when declared
> clean, or poisoned with the declared latent predicate when declared
> poisoned. Otherwise the extern stays out of the trusted registry.
> Programs using untrusted externs typecheck but do not get FR.

The relation between input poison and output poison is governed by the
extern's implementation, including implementation-internal control flow.
The annotation therefore states the input condition under which the
trusted proof applies; it does not try to compute output cleanness
structurally from input cleanness alone.

### 3.2 Triage rule at declaration time

- **Trusted**: a precondition `P` exists such that for inputs satisfying
  `P`, the output honors its declared `QTyp` (FR-clean if declared
  clean, poisoned-with-declared-predicate if declared poisoned). The
  extern is paired with a Lean proof witnessing this, or — when we
  choose to take the author's word — with an axiom of the same shape.
- **Untrusted**: no such precondition exists, or none has been supplied.
  The extern can still be used by programs; FR is not derived for
  programs that use it.

## 4. Current-builtin status under this model

- **`abs`** — executable examples declare a clean argument and clean return,
  which is the trusted surface contract for successful calls. It has a concrete
  trusted boundary spec (`builtinAbsSpec`) and validates the pure-unary clean-int
  path.

- **`max`** — executable examples declare clean arguments at both curried levels
  and a clean return. The output depends on both the captured outer argument and
  the immediate inner argument. The curried pair has concrete trusted specs and
  program-level FR artifacts for the unguarded captured-env path. Guarded
  captured dependencies are implemented at the typecheck gate and proved at the
  trusted call boundary. Memory-read `!r` dependencies are implemented/proved
  for the representative explicit-reference-argument path. Branch-join capture
  conjunction merging is also implemented/proved
  (`LeanProofs/CaptureJoinConjunction.lean`).

- **`sqrt`-style externs** — candidate for the unified model with input
  precondition `x >= 0`. Implementation `if x >= 0 then Lean.sqrt x else 0`
  has a defensive runtime branch, but the FR cleanness comes from the
  input precondition (which constrains the inputs across two runs to
  agree by depoisoning), not from the runtime branch. The executable
  `extern_arg_precond_sqrt` example validates the argument-condition mechanism;
  a separate trusted spec would still be needed to make `@19` a live trusted
  entry.

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

### 5.3 Argument-side precondition syntax

Extern parameters use full qualified annotations, mirroring native `fn` / `pfn`
parameters. The argument `QTyp` is the extern's declared precondition: the
trusted boundary proof applies only to calls whose argument typing satisfies
that qualified type.

The implementation stores the source argument annotation as the surface triple
`Typ + clean/poison flag + SyntaxPredicate`, resolves it to a concrete `QTyp` at
typecheck time, and records that concrete condition on `FnTClosure.extern` /
`PFnTClosure.extern`. Proof-side declarations faithfully carry the clean/poison
flag used for the trusted-entry match; the surface predicate is intentionally
not recovered at every proof reachability site, so predicate-shape checking
remains an executable typechecker condition.

The key separation is that argument `QTyp` records what the caller must
establish, while return `QTyp` remains the output contract. Return
predicates are latent depoisoning markers on produced values; they are
not caller-side preconditions.

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

This raises an adjacent question about **input memory**. Extern dispatch can
also read memory: pure externs may dereference ref-typed arguments, and impure
externs additionally read driver-allocated cells (`errno` and similar). The
selected read-side annotation path is `captures:` with bang targets such as
`!r :> QTyp`, not a separate `reads:` clause. `effects:` remains memory-write
only.

The call-time rule is intentional: a memory read dependency is checked when the
extern is about to rely on it, because memory may have changed since the
callable was created. The `extern-env-deps` branch validates this end-to-end for
the representative explicit-reference-argument path, including a trusted spec /
program-FR artifact.

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

The guard regime `R` is a universally quantified parameter of the FR
theorem, not runtime state or source-level state. Extern trust contracts
should be stated relative to the same `R`: for every well-formed regime,
inputs that are regime-consistent should produce outputs that honor the
extern's declared `QTyp`.

The regime can also cover tags allocated by extern return/effect
predicates. The implemented design selects externs by id in
`InputSpec.regimeExterns`; when the typechecker allocates fresh output
tags for a selected extern, `TypeContext.externRegime` and
`applyExternRegimePolicy` insert those tags into the active regime with
the scenario's chosen boolean. Unselected externs keep the conservative
behavior: their generated tags are not in the regime, so downstream
predicate matches do not de-poison for FR.

Regime evolution is extension-aware (`Regime.monotoneStepExt`): pre-existing
tags are preserved or dropped as usual, while selected extern calls may add
fresh output tags. The public FR theorem is shaped around a per-context
registry-trust premise plus an `ExternRegimeMatchesInputSpec` bridge, so the
theorem is instantiable for non-empty trusted registries. The executable
counterpart is the `--extern-regime "id=bool"` CLI option;
`examples/extern-regime-open.poison` demonstrates a selected extern-produced
predicate de-poisoning under the executable typechecker.

## 6. Current positions

- A clean-output `abs` declaration must require a clean argument. The concrete
  trusted `abs` spec uses that contract.
- Extern trust uses a single proof shape with a possibly trivial
  precondition.
- Extern preconditions live on argument-side `QTyp` annotations. Return `QTyp`
  annotations remain output contracts.
- Externs without a statable precondition under which the output
  honors its declared `QTyp` are **not trusted** (i.e., absent from the
  trusted registry); their use does not block typechecking but does
  block FR.
- Unsatisfied argument preconditions are rejected at typecheck time; there is no
  conservative fallback typing rule.
- Nested/curried extern preconditions are enforced at every extern application
  level.
- The cleanness obligation matches existing FR semantics: clean-
  declared outputs must be FR-clean; poisoned-declared outputs carry
  the declared predicate as a depoisoning marker for downstream code.
  The trusted-extern proof does not weaken or relax the declared
  semantics.
- A return-spec predicate is interpreted as a **latent depoisoning
  marker**.
- Extern-produced return/effect tags are regime-visible when their extern
  id is selected by the FR scenario. This is a domain statement, not a
  trust statement: it lets downstream checks use the generated tags under
  the regime, while boundary trust still comes from the trusted registry.
- Read-side environment and memory dependencies are expressed with
  `captures:`. They are checked at the extern call boundary under the active
  regime, not at declaration time.

## 7. Open questions

### 7.1 Predicate language expressiveness  *(from §5.2)*

Are existing `Predicate` types (`guardClosure`, `guardOnly`, `noPred`)
expressive enough for the cases we care about (sqrt-style, bounded
indexing, divmod with nonzero divisor)? Or do they need extension?

### 7.2 Concrete latent-marker example  *(from §5.4)*

Construct a concrete extern returning a value alongside a depoisoning
predicate, with downstream code performing the matching check. The
example should pin down whether existing `Predicate` machinery is
expressive enough, or expose the narrower-than-expected applicability
of the latent-marker reading.

### 7.3 Read-side memory captures  *(from §5.6)*

The syntax and model are selected: use bang targets in `captures:`. The open
work is implementation/proof completion on `extern-env-deps`, including an
end-to-end trusted example for memory reads and the corresponding accepted /
rejected tests.

### 7.4 Remaining live trusted extern specs

The proof stack has concrete trusted specs for `abs`, the curried `max` entries,
the memory-read `@23`, and the impure-identity `@13` (`builtinImpureIdSpec`, the
first `kind = .fn` entry). Remaining interpreter builtins such as `@19`, `@20`,
`@21`, and `@22` still need explicit trusted-registry instantiations before they
contribute to the public FR theorem as live trusted entries.

## 8. Next steps

1. `doc/extern-env-deps.md` is complete on the `extern-env-deps` branch:
   branch-join capture conjunction merging was the last pfn-side read-dependency
   item, now implemented/proved.
2. Merge `extern-env-deps` into `ffi` once the standard gates are green and no
   new `sorry`/axioms are introduced.
3. Resolve §7.1 (predicate language expressiveness).
4. Construct §7.2 (latent-marker example) to validate the interpretation
   against existing predicate machinery.
5. Add trusted specs for remaining live builtins (`@19`, `@20`, `@21`, `@22`) as
   separate FFI coverage work.
