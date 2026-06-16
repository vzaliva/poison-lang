# LeanProofs Refactoring Plan

Refactoring opportunities for the `LeanProofs/` package, organized into
independent, ordered tasks. The goal is a package that is (1) **better
organized** (smaller modules, fewer dependencies), (2) **less redundant**
(shared helpers instead of copy-paste), and (3) **shorter / simpler**
(decomposed and golfed proofs) — **without changing what is proved**.

## How to read this document

- Tasks are labelled `T14`–`T17` — the remaining work. `T1`–`T13` are
  **complete** (see git history) and have been removed from this plan.
- Each task is **independent** unless a `Depends on:` line names a prerequisite;
  the only named prerequisites (`T6`, `T9`) are themselves complete.
- Every task records **Benefit**, **Risk**, **Effort**, and a **Verification**
  note for which claims were confirmed against the source at planning time.
- Line and reference counts are heuristic (ripgrep-based) and should be
  re-confirmed at execution time.

## Invariants every task must preserve

These are non-negotiable. A task that cannot honour all of them should be
abandoned, not forced.

1. **0-sorry / 0-axiom.** The package currently contains **no `sorry` and no
   `axiom`**. No refactor may introduce one, or weaken any theorem statement.
   Every "simplification" must derive the original statement (as a corollary or
   a same-signature wrapper).
2. **Per-operator independence.** The `StepFR{App,Assign,Ite,Deref,NewRef,Seq,`
   `Vlet,Literal,Var,Op,FnPfn}.lean` files MUST NOT import each other. Shared
   helpers go only to `StepFR.lean` (general step machinery) or
   `JoinMemberTransport.lean` (join-member transport), or a *new* module that
   sits below the per-operator layer.
3. **`private` discipline.** Declarations used only within their file stay
   `private`.
4. **Sequential builds.** `lake` builds all transitive dependencies, so files
   sharing a dependency cannot be built concurrently. Authoring of independent
   leaf files may be parallelized, but `lake build` runs serially. Tasks
   touching `StepFR.lean` or `TypeSafety.lean` force a wide rebuild and are
   inherently serial.

## Snapshot

| Metric | Value |
| --- | --- |
| Modules | 38 |
| Total lines | ~101,000 |
| `sorry` / `axiom` | 0 / 0 |
| Largest | `StepFRApp` 21.3k, `TypeSafety` 18.9k, `TypecheckInduction` 7.1k |

The organization, redundancy, and simplification problems that motivated this
plan were resolved by `T1`–`T13`: verified dead-code / `private` / import
cleanup; the `fn`/`pfn`, `Side0`/`Side1`, and `arrow`/`parrow` mirror collapses;
the shared induction-scaffold factoring; and the `StepFR` hub split into
`ExternTagMeaning`, `TypecheckInduction`, `StepFRClosureApply`, and
`ExternCallBoundarySides`. The remaining, concentrated targets:

- **`ExternProofs` monolith (T14)** — a flat concatenation of seven
  self-contained trusted entries with near-zero cross-builtin coupling, ripe for
  a per-builtin split sharing a small base.
- **`FaultRobustnessProofs` inlined `ite` arm (T15)** — ~1.4k lines inlined
  where every other operator delegates out in ~15 lines; `StepFRIte` is the
  only operator exporting zero single-run lemma.
- **`JoinMemberTransport` scope (T16)** — several public lemmas are
  single-consumer despite the module's `StepFRApp`∩`StepFRIte` justification.
- **Grab-bag golf (T17)** — small self-contained simplifications across
  otherwise-clean files.

## Task index

Effort: S = small, M = medium, L = large. Theme is shown per-task below.

| ID | Task | Risk | Eff | Depends on |
| --- | --- | --- | --- | --- |
| T14 | Split ExternProofs per builtin | med | L | T6 |
| T15 | Factor inlined ite arm + boilerplate | med | L | — |
| T16 | Trim JoinMemberTransport | high | L | T9 |
| T17 | Low-risk proof golf (grab-bag) | low | M | — |

## Recommended ordering

`T1`–`T13` are complete. The four remaining tasks are largely independent —
their only prerequisites (`T6` for `T14`, `T9` for `T16`) are already done — so
they can be scheduled opportunistically:

```mermaid
graph LR
  T14[T14: split ExternProofs]
  T15[T15: FaultRobustnessProofs ite arm]
  T16[T16: trim JoinMemberTransport]
  T17[T17: golf, anytime]
```

- **T14** (`ExternProofs` per-builtin split) is a disjoint subtree; its
  prerequisite T6 (shared `pfn`-decl / operational helpers) is done.
- **T15** (`FaultRobustnessProofs` `ite` arm → `StepFRIte`) is independent.
- **T16** (`JoinMemberTransport` trim) follows the completed T9; **high risk**
  via a shared `guardClosure` base that must stay in `JoinMemberTransport`.
- **T17** (golf grab-bag) is per-file and schedulable any time.

`T15` and `T16` touch per-operator / shared modules, so honour the
**per-operator independence** invariant and serialize `lake` builds.

---

## Remaining tasks

### T14 — Split `ExternProofs` along the per-builtin seam

**Theme:** organization · **Risk:** medium · **Effort:** large · **Deps:** T6

**Motivation.** `ExternProofs` is a flat 6.2k-line concatenation of seven
self-contained trusted entries under one namespace; cross-builtin coupling is
near-zero (Max10 and MemDeref reference no other-builtin helper; only Max11Guarded
reuses Max11Captures defs); downstream consumers import only per-entry
`Spec`/`Decl`/`Impl` names. SetErr alone is ~1,777 lines.

**Steps.**

- After T6 has extracted the shared `pfn`-decl and operational helpers, place those
  helpers in one small base module the per-entry files import.
- Carve per-entry files (`ExternProofsAbs`, `ExternProofsMax` keeping the
  curried-max pair together, `ExternProofsMemDeref`, `ExternProofsSetErr`,
  `ExternProofsErrno`), reproducing the `ExternProofs` namespace and the
  `ExternRefDecl` sub-namespace; repoint the downstream imports (`MaxCurriedFR`,
  `ExternRegimeInt`, `GuardedCapturesFR`, `MemReadCapturesFR`); consolidate the
  split `ExternRefDecl` namespace. Preserve all `Spec`/`Decl`/`Impl` names.

**Benefit.** Turns a 6.2k-line monolith into focused per-entry modules sharing a
small base, improving the module-API read and isolating the 1.8k-line SetErr entry.

**Risk.** Mechanically low-risk (the blocks are independent) but touches the import
graph: the `ExternProofs` namespace and `ExternRefDecl` sub-namespace must be
reproduced and downstream imports repointed. Pure relocation preserves
0-sorry/0-axiom. Disjoint from the `StepFR` hub block (separate subtree), so
schedulable around it.

### T15 — Factor the inlined `ite` arm and boilerplate in `FaultRobustnessProofs`

**Theme:** organization · **Risk:** medium · **Effort:** large · **Deps:** —

**Motivation.** `FaultRobustnessProofs` inlines the entire ~1,400-line `ite` arm
of the masked single-run proof, while every other operator delegates in ~15 lines
to a `stepFRSingleRunFinalCleanPcTrue…maskedReg` lemma in its own `StepFR*` file;
`StepFRIte` is the only operator exporting **zero** such lemma. Secondary: a
~95-line contracts hypothesis preamble copy-pasted across 3 theorems; the 4
literal arms are ~27-line near-clones; the 4 extern-declaration arms are a
~28-line near-identical family.

**Steps.**

- Extract the inlined `ite` body into a new
  `stepFRSingleRunFinalCleanPcTrue_ite_maskedReg_with_expr_proof` in
  `StepFRIte.lean` (which imports only `StepFR` and `JoinMemberTransport` — both
  permitted), threading the closed-over locals as explicit parameters; replace the
  inlined arm with a ~20-line delegating arm mirroring the `op`/`seq` arms.
- Bundle the contracts preamble into a `private structure FRCtxContracts` (+ an
  `FRStepContracts` extension) so the 3 theorems project fields; collapse the 4
  literal arms and the 4 extern-declaration arms into one `private` helper each.

**Benefit.** Relocates ~1,380 lines into the topic-appropriate `StepFRIte`
(`FaultRobustnessProofs` ~3,507 → ~2,150 lines; a uniform masked single-run across
all operators) and removes ~250+ lines of preamble/arm boilerplate.

**Risk.** Pure relocation + boilerplate factoring; no statement weakens. The
`ite`-arm extraction closes over many locals that must become explicit parameters
(a signature mismatch fails the build, but the blast radius is `StepFRIte` + the
one call site). The contracts-structure change must reproduce implicit-binder field
types exactly. Independent of the hub block.

### T16 — Trim `JoinMemberTransport` to genuinely-shared lemmas

**Theme:** organization · **Risk:** high · **Effort:** large · **Deps:** T9

**Motivation.** `JoinMemberTransport` exists for lemmas shared by **both**
`StepFRApp` and `StepFRIte`, but 7 of its 12 public lemmas violate that (5
App-only, 2 Ite-only), and several `private` helpers are reachable only from
App-only roots. Some `private` bases are genuinely shared between an App path and
an Ite path and must stay.

**Steps.**

- Move App-only `agreeValueUnder_clean_monotoneRegime_ext` (10 App uses, no
  JMT-private deps) into `StepFRApp` and mark `private`. Move the App-exclusive
  `consistentWithRegime` and masked-transport trio plus their App-only `private`
  helpers into `StepFRApp` — **but keep the `guardClosure` private base in JMT**
  because it is also used by an Ite path; the App-side wrapper imports it.
- Optionally move the two Ite-only public wrappers
  (`joinMemEnvsStrong_lookup_guardClosure_implies_left`/`_right`) to `StepFRIte`
  and privatize, leaving JMT exporting only the shared base.

**Benefit.** Refocuses `JoinMemberTransport` on genuinely-shared transport,
removing ~460 App-exclusive lines from a module justified as App∩Ite shared.

**Risk.** Relocation crosses a shared base: the `guardClosure` private base is
consumed by both an App-only and an Ite-only path, so it must stay in JMT — and
per-operator independence forbids `StepFRApp` importing `StepFRIte`, so any helper
Ite also needs must remain in JMT. Do this only **after** T9 so merged (not
duplicated) lemmas are relocated. High risk due to the shared-base entanglement.

### T17 — Low-risk proof golf and shared-helper extraction (grab-bag)

**Theme:** simplification · **Risk:** low · **Effort:** medium · **Deps:** —

**Motivation.** Several small, self-contained golf opportunities across
otherwise-clean files.

**Steps.**

- **`RegimeConsistency`:** add `private tagEnv_get_insert_of_ne` for the 6 inline
  blocks; consider deriving the non-masked `tagEnv`-insert lemmas from the
  masked ones via the existing unmask bridge; merge the three `lookup_qtyp`
  lemmas; optionally parametrize the four `QTypInQTyp…root_or_self` over closure
  shape (keep the two extern names **public** — `StepFR` consumes them).
- **`FaultRobustness`:** factor the `varsRegime`/`locsRegime` monotone trio's
  shared `withPred_ok` reasoning.
- **`ExternBoundary`:** rewrite the 19 `ExternDeclarationReachableFromExpr`
  navigation theorems as term-mode one-liners (keep `id_eq`).
- **`ExternRegimeInt`:** introduce `emptyCtx_FR_of_agreesWithProgram` and delete
  the four `hagrees` glue theorems.
- **`ExternTypingAssumptions`:** extract the `buildBatchTm` fold-invariant helper.
- **`Equality`:** add a header note that `deriving DecidableEq` is infeasible
  because of the `LocSet`/`ExtTreeSet` field and the `Expr`/`Value` mutual
  recursion (prevents future wasted effort).

**Benefit.** Removes several hundred lines of boilerplate across already-clean
files, documents an infeasible refactor, and tightens trivial proofs behind
preserved public signatures.

**Risk.** Mostly same-file golf with preserved statements, so 0-sorry/0-axiom
holds and consumers are unaffected. The `QTypInQTyp` parametrization and
`buildBatchTm` fold-invariant carry moderate proof-engineering risk; fall back to
the lighter helper extractions if a clean abstraction does not emerge. **Avoid**
the `EffectTarget`/`CaptureTarget` `DecidableEq` change that touches `Syntax.lean`
(a root) unless treated purely additively. Schedulable opportunistically;
splittable per file.

---

## Dropped — explicitly not recommended

These were considered and rejected; recording them prevents re-litigation.

- **Bundle `TypeSafety`'s giant main inductions into conjunctions**
  (`combined_main` style): high risk of case-discharge interactions in the
  structural core feeding the whole FR stack, for modest savings. The leaf-arm and
  step-lemma golf in T10 captures most of the value.
- **Full `fn`/`pfn` unification of the `applyTClosureAtCursor` reachability twins
  and the `StepFRApp` `arrow`/`parrow` lemma families:** rooted in two distinct
  interpreter inductives (`FnTClosure`, `PFnTClosure`) and four separate `apply`
  defs in `LeanPoison` — out of scope for a `LeanProofs`-only refactor, and risks
  breaking definitional reduction (and thus 0-axiom). Only narrow shared-skeleton
  extractions are worth it (folded into T9 and T17).
- **Merge the `var` masked/unmasked consistency lemmas (or any masked/unmasked
  predicate parametrization):** the masked predicate adds a `maskedTag`
  constructor (a distinct inductive family), so a shared abstraction may not exist
  without a generalization rippling through `RegimeConsistency` and every
  consumer. Speculative, high-effort, likely net-negative.
- **Split `TypeSafety`'s 9.3k-line extern-closure structural block / relocate its
  container helpers to `Aux`:** high risk (`TypeSafety` is imported by `StepFR`
  plus 4 others, and the extern lemmas are interleaved with the preservation
  proofs), all-or-nothing rebuild, and the placement is not actively painful.
  Deferred.
- **Merge the three FR capstone files (`MaxCurriedFR`, `MemReadCapturesFR`,
  `GuardedCapturesFR`) into one module:** mutually exclusive with the T3
  sibling-decoupling direction; the per-file documentation has standalone value.
  Decoupled siblings (T3) are preferred.
- **Delete `Semantics.wfValue_loc_of_RegistryReservedBelow` without
  confirmation:** project memory marks it a deliberately-kept provability witness
  for a planned val-clause bridge. Gated on user approval inside T1, not an
  automatic deletion.
- **Split `ExternBoundaryProofs`' reachability engine from the trusted-registry
  resolvers:** the resolvers depend on the engine, so the split must respect that
  direction and yields small net import savings. Lower value than the
  dead-code/private/golf wins already captured.

## Execution notes

- Build **one module at a time** (`make lean-build-file FILE=…`), never
  concurrently across shared-dependency files.
- After each task, confirm the package is still **0-sorry / 0-axiom** and
  **warning-clean** (CLAUDE.md: prefix unused binders with `_`).
- Commit only at green, compiling checkpoints, and only with user approval.
- The per-file golf in T17 is safe to **author** in parallel sub-agents (the
  files are mutually independent), but `lake` builds must still be serialized.
