# AGENTS.md

This file provides guidance to AI agents when working with code in this repository.

## Project Overview

The Poison Language is a research implementation of a simple imperative programming language with built-in fault tracking via a type system that models data corruption as "poison" propagation. This Lean 4 project combines:

1. **Core implementation** (`LeanPoison/`) - operational semantics, type system, parser integration
2. **Formal proofs** (`LeanProofs/`) - fault-robustness of the type system (which subsumes preservation) and its supporting properties; the progress property is stated but not proved
3. **Parser** (`parser/`) - tree-sitter grammar for `.poison` files
4. **Formal specification** (`poison-lang-spec/`) - Ott specification with LaTeX documentation

## General Coding Standards

- **Indentation**: Use spaces only, never tabs
- **Compilation**: Always leave code in compilable state at checkpoints (no build errors)
- **Warnings**: Avoid compilation warnings (except `sorry`-related warnings in proofs)
- **Unused binders**: Prefix unused variables and parameters with `_` so the tree stays warning-clean (warnings can fail CI or tests)
- **Build verification**: Run `lake build` to check compilation before committing
- **No parallel builds**: Do not run concurrent builds (including via parallel sub-agents) for files that share dependencies; `lake` builds all transitive dependencies, so concurrent builds of interdependent files will conflict and produce spurious errors
- **CLI tools**: fd (fdfind), ripgrep, jq, rename, shellcheck, sd, delta, gh, difftastic (`difft` on some installs), scc, yq, hyperfine, comby, tree-sitter, ast-grep, dtrx; fzf, bat (navigation/preview), just (task runner), entr, watchexec (rebuild on change), parallel (gnu parallel; independent per-file checks).

## Build Commands

```bash
# Initial setup and build
make                                   # Build everything: spec, docs, parser, Lean code
make lean-build                        # Build Lean libraries and executables
make lean-build-file FILE=LeanProofs/FaultRobustness.lean  # Build one module (path or dotted name, e.g. LeanProofs.FaultRobustness)
make axioms                            # Print the axioms the main theorem and the extern-call witnesses depend on (expect propext, Classical.choice, Quot.sound)

# Running interpreter
make run POISON=FILE.poison              # Run a .poison file
make run-verbose POISON=FILE.poison      # Run with verbose output

# Testing (applies to LeanPoison implementation only, not proofs)
make test                              # Build and run all tests
./scripts/run_tests.sh                 # Compare outputs against .output/.fail files
./scripts/update-tests.sh              # Regenerate .output/.fail from current interpreter

# Documentation and parser
make poison-lang-spec                  # Generate PDF from Ott specification
make doc                               # Build documentation pdf from tex files
make parser                            # Build tree-sitter parser

# Cleaning (WARNING: invalidates mathlib cache - avoid; ask user permission if it is absolutely necessary)
make clean                             # Clean build artifacts
# After cleaning, run: lake exe cache get

# Lean cache (mathlib); `lean-build` already depends on `cache`
make cache                             # Download precompiled caches if needed
make cache-refresh                     # Force fresh cache (use after toolchain/mathlib bumps)
```

## Architecture

### LeanPoison/ - Core Implementation

The executable language implementation. **Tests apply to this package.**

- `Syntax.lean` - AST definitions, types (Typ, QTyp), expressions (Expr), operators, values, runtime state (Config, Memory, VarEnv); captured environments, whose entries carry a qualified type and a binding number, and the merge of closure sets (`mergeFnTClosures`, `mergePFnTClosures`)
- `BigStep.lean` - Big-step operational semantics (`beval` with fuel-based evaluation)
- `Typecheck.lean` - Type checking with typing contexts (MemoryTypeEnv, TagEnv, BindEnv, TypeContext); guard matching (`matchGuard`, `guardScopeAgrees`)
- `Parser.lean` - Tree-sitter parser integration, XML-to-AST conversion
- `Pretty.lean` - `Repr`/`Format` pretty-printing for values, configs, and related structures
- `Runtime.lean` - Runtime support functions
- `Misc.lean` - Utilities

**Key patterns:**
- Fuel-based evaluation (default 1000) ensures termination
- `EvalResult` has three cases: `success`, `outOfFuel`, `runtimeError`
- Type checker maintains `MemoryTypeEnv` (Γ), `TagEnv` (ℒ), and `TypeContext`
- Every typing of a binder gives the bound name a fresh binding number (`TypeContext.nextBind`, recorded in `BindEnv` and in captured environments; 0 is no number). `matchGuard` selects a guard that reads a clean variable of a base type only when the variable has the same number where the guard is made and at the test. A merge of closure sets sets to 0 the number of a captured entry on which members with the same parameter and body disagree (in number or in qualified type), and every number inside the type of such an entry

### LeanProofs/ - Formal Proofs

Formal correctness proofs establishing type safety and semantic properties. **No tests for this package.**

**Core definitions:**
- `Semantics.lean` - Low-level semantic definitions: `terminatesTo`, `stuck`, `wfValue`, `wfVarEnv`, `wfConfig`, `nextAddr_not_in_memory`. Foundational module imported by `ExternRuntime.lean` and `SemanticsProperties.lean`.
- `TypeSafety.lean` - Typing contexts, realisation maps, value typing, runtime context instantiation. Also the relation between a member of a closure set and its copy in a merged set, whose captured entries are kept or have their binding numbers set to 0 (`CapEntryZeroedFrom`, `CapEnvZeroedFrom`, `FnTClosure.ZeroedFrom`, `PFnTClosure.ZeroedFrom`), with `mem_mergeFnTClosures_inv` / `mem_mergePFnTClosures_inv` (every member of a merged set is such a copy of a member of one of the two sets) and the invariance of value typing under it (`valueHasETyp_zeroETyp`, `valueHasETyp_of_zeroETyp`)
- `SemanticsProperties.lean` - Structural inversion lemmas, `bevalApp_structure` / `BevalAppSuccess`, `nextAddr` monotonicity (`beval_nextAddr_mono`, `terminatesTo_nextAddr_mono`), and `wfConfig_preserved`. These three lemmas take `(hOp : RegistryOperationalSafe cfg₀.registry)` as a hypothesis discharged at the orchestration layer via `TrustedRegistry.operationalSafe`.

**Extern boundary stack (FFI trust):**
- `ExternRuntime.lean` - Runtime extern event predicates living below the FR proof stack: `ExternDeclaration`, `ExternDeclBoundaryRun`, `ExternCallEntry`, `ExternCallBoundaryRun`, `ExternBoundaryWFRun`, and the operational safety contracts `ExternOperationalSafe` (per trusted entry, per-kind shape) and `RegistryOperationalSafe` (per runtime registry, consumed by `SemanticsProperties.lean`).
- `ExternBoundary.lean` - Theorem-facing FR boundary contract layer (small, readable API): `BodyEntryInputsAgree`, `ExternBoundarySpec` (with `declFR`, `callFR`, `declSingle`, `callSingle`, `operational` fields), `TrustedExternEntry`, `TrustedRegistry` (with `toRuntimeRegistry`, `runtime_lookup_exists`, and the `operationalSafe` bridge proving `RegistryOperationalSafe` from `entry.spec.operational`), `TrustedRegistryAgreesWithReachable`, and reachability-domain inductives + navigation theorems.
- `ExternBoundaryProofs.lean` - Proof-heavy adapters and reachability integration theorems split off from `ExternBoundary.lean` (kept above it in the import graph). Resolution variants of `TrustedRegistryAgreesWithReachable`, captured-environment/QTyp reachability namespaces, and call-boundary integration. Consumers needing these proof bodies (e.g. `FaultRobustnessProofs.lean`, `StepFRApp.lean`) import this file in addition to `ExternBoundary.lean`.
- `ExternProofs.lean` - Concrete trusted entries for the shipped externs: the complete `ExternBoundarySpec`s (`builtinMax10Spec`, `builtinMax11CapturesSpec`, `builtinAbsSpec`, `builtinSetErrSpec`, `builtinErrnoSpec`, `builtinMemDerefSpec`, …), the generic `pfn` and `extern ref` declaration-boundary machinery, and the `set_err` program/registry agreement witness (`setErrProg`, `setErrRegistry`, `setErr_agreesWithProgram`). Everything lives in the `ExternProofs` namespace; implementations are shared definitionally with the interpreter via `LeanPoison/ExternBuiltins.lean`.
- `ExternRegimeInt.lean` - Extern-regime typechecking lemmas plus the program-level FR capstones that instantiate the top-level theorem at concrete trusted registries (`setErrWriteEffect_FR`, `errnoExternRef_FR`, `errnoScenario_FR`, all in the `ExternRegimeInt` namespace). Imports `FaultRobustnessProofs` and `ExternProofs`, so it sits above the whole general proof stack; only the per-builtin capstone modules below import it.
- `AbsFR.lean`, `MaxCurriedFR.lean`, `MemReadCapturesFR.lean`, `GuardedCapturesFR.lean` - Program-level FR capstones for the shipped builtins (`abs_FR`, `maxCurried_FR` / `appliedMaxCurried_FR`, `memReadCaptures_FR` / `appliedMemReadCaptures_FR`, `guardedCaptures_FR`): each places the builtin's `ExternBoundarySpec` in a concrete `TrustedRegistry` and instantiates the top-level theorem. Leaves of the import graph.
- `CaptureJoinConjunction.lean` - Branch-join behaviour of extern `captures:` contracts (`mergedParrow_apply_captures_conjunction`): merged closure members keep their captures verbatim, and applying the merged type requires every member's contract. Imports only `TypeSafety`; illustrative, not on the FR proof path.

**Main properties:**
- `RegimeConsistency.lean` - Regime-consistency definitions (tag meaning, guard descriptors) plus the masked-regime / `tagEnvConsistentWithRegime*` machinery (definitions, insert/invalidate/join lemmas) shared by `StepFR` and downstream FR proofs. `PredSatLaws predSat tm β` states the laws on the relation `predSat` under a view `β : BindVals`, the values a run gives to binding numbers (`ViewAgreesOn`: the variables a guard reads hold the values the view gives their numbers)
- `TagFrame.lean` - Program tables of typing runs. Every typing run records the guards it allocates (`TypeResult.tagLog'`, a list of `TagAlloc`); this module defines `LogIn`, `LogFresh`, `WithinLog`, `programTable` and `TagFrame` (a lawful table containing the current table and every allocation of the run), `ExternBatchTagMeaningExtension`, the frame algebra used by the per-operator proofs (`TagFrame.left/right/next/skip/of_join`), and `typecheck_tagLog_fresh` (every successful run allocates distinct fresh tags). Imports `TypeSafety` and `RegimeConsistency`; imported by `ExternTagMeaning`, `TypecheckInduction`, `StepFR` and `FaultRobustness`.
- `ExternCallSteps.lean` - The steps of a typed run and the extern calls made at them: `Step` (typing context, expression, typing fuel, start configuration), `SubStep` / `Reach` (the decomposition the step proof recurses along; the body of a called closure is entered through a member of the function type only if the member's captured types type the closure's captured environment), `ExternCallAt` (a step whose run calls an extern member, with the member result, call entry, final configuration and returned value), the per-call conditions `CallMatches` / `CallAgrees` (each with a field for the returned value and one for the cells the call writes, `EffectCell`: an effect `!v` whose target is a reference to a single location in the body context, at the address `v` holds at the call), `ExternValAt` (a step that declares an `extern val`, read as a constant extern function) with the condition `ValMatches` on the declared value, the theorem's premises `ExternCallsMatch` (a structure with a field `calls` and a field `vals`) and `ExternCallsAgree` (a structure with the field `calls`; agreement of an `extern val` is not a premise, it is proved by the entry's author in `declFR`), the premise `TestsAgreeWithView β root` (at every reachable conditional that `matchGuard` matches to a tag with an entry in the regime, the variables the guards of that tag read hold the values the view `β` gives their binding numbers) with its step form `TestsAgreeWithViewOn`, the step-level bundle `ExternStepPremises` (match and the premise on tests for each run, with that run's relation and view; agreement for the pair), and `ExternCallsMatch.of_registry_none` / `ExternCallsAgree.of_registry_none` (a run under a registry without entries makes no extern call and declares no extern value). Imports `RegimeConsistency`; imported by `StepFR` and `FaultRobustness`.
- `FaultRobustness.lean` - Top-level fault-robustness definitions (`FaultRobustnessSpecForCtx`, `FaultRobustnessSpecForRegistry`, `agreeOnClean`, `agreeValueUnder`, etc.). The pointwise statement takes the typing fuel and, for each of the two runs, a relation `predSat` and a view `β` with `PredSatLaws` on the starting tag meaning and on the program table, `ExternCallsMatch` and `TestsAgreeWithView` on the run's root step; and `ExternCallsAgree` for the pair of root steps.
- `StepFR.lean` - Shared step-based machinery (`StepFR`, `StepFR_IH`, `resultAgreesIfClean`, `consistentRegimeSpec_implies_consistentWithRegime` bridge lemma, and helper lemmas for value/captured/closure consistency) used by every per-operator FR proof. Its heavy IH-free clusters were factored out into the hub-split support modules below (`ExternTagMeaning`, `TypecheckInduction`); `StepFR` re-imports them.
- `ExternTagMeaning.lean` - extern-tagMeaning cluster factored out of `StepFR` (hub split): `resolveSyntaxPred`, `surfaceSpec`, `typecheckExternVal`, `applyFnTClosure_extern`, `applyExternEffect`, `forIn_effects`, and the captured-extern `QTypRespectsTagMeaning` origin lemmas. Sits below `StepFR`; imported by `StepFR` (re-export) and `TypecheckInduction.lean`.
- `TypecheckInduction.lean` - the heavy `typecheckExpr`-preservation structural inductions factored out of `StepFR` (hub split): `typecheckExpr_preserves_regimeConsistentWithCtx` (+ masked / `MaskedTagsAbsent` variants), `typecheck_preserves_predSatLaws`, the `*_byIH` closure-application bridges, and the clean lookup-origin cluster. Sits below `StepFR`; imports `ExternTagMeaning.lean`.
- `StepFRClosureApply.lean` - App-only closure-application machinery factored out of `StepFR` (hub split): the `applyFnTClosure` / `applyPFnTClosure` / `applyClosuresThreaded` structural family and their feeders. Imports `StepFR`; imported only by `StepFRApp.lean` and `ExternCallBoundarySides.lean`.
- `ExternCallBoundarySides.lean` - parametrized extern-call boundary-contract / Side family relocated out of `StepFRApp` (hub split): the `ExternCallBoundary{Fn,Pfn}StaticSource` provenance inductives + navigation theorems, the `ExternCallBoundarySingle{Fn,Pfn}Contract` single-run contracts (+ `of_trustedReachable`), the `ExternCallBoundaryFR{Fn,Pfn}{Run,Side0,Side1}` contracts/providers, the `ExternCall{No,Impossible,Trusted}EntryKey` discriminators, and `TrustedRegistryAgreesWithProgramLocal`. These take the per-run results as hypotheses rather than referencing the application case proof (so the family is downward-closed). Sits below `StepFRApp` (which imports it; the `Single{Fn,Pfn}Contract`s are also consumed transitively by `FaultRobustnessProofs`).
- `JoinMemberTransport.lean` - Shared join-member transport machinery: lemmas about how `joinTypeResults` transports per-member properties (`valueConsistentWithRegime`, `agreeOnClean`, etyp signatures, member-of-arrow/parrow, ref membership, internal-poison) to the joined result. Imported by `StepFRApp` and `StepFRIte` so per-operator FR proof modules stay mutually independent
- **Per-expression case proofs** (each file contains the corresponding `stepFR_*` / masked single-run lemmas; shared imports from `StepFR`; `StepFRApp` and `StepFRIte` additionally import `JoinMemberTransport`; each per-operator lemma threads `(hOp : RegistryOperationalSafe registry)` to discharge `wfConfig_preserved` / `terminatesTo_nextAddr_mono` calls):
  - `StepFRApp.lean` - function application
  - `StepFRAssign.lean` - assignment
  - `StepFRLiteral.lean`, `StepFRVar.lean`, `StepFROp.lean` - literals, variables, primitive operators
  - `StepFRFnPfn.lean` - `fn` / `pfn` forms
  - `StepFRIte.lean` - conditional
  - `StepFRDeref.lean`, `StepFRNewRef.lean` - memory operations
  - `StepFRSeq.lean` - sequencing
  - `StepFRVlet.lean` - `vlet`
- `FaultRobustnessProofs.lean` - Orchestration: imports all `StepFR*` case modules and proves the step theorem (the private `TypeSystemEnforcesFaultRobustness_step_*` family), the bridge from the step theorem to the specification (`faultRobustnessSpec_of_step`), the per-context theorem `TypeSystemEnforcesFaultRobustness_at` with its all-context corollary `TypeSystemEnforcesFaultRobustness_allCtx`, and the top-level statement (`FaultRobustnessSpec`, `TypeSystemEnforcesFaultRobustness`). The public top-level theorem derives `RegistryOperationalSafe` internally via `TrustedRegistry.operationalSafe tr` — no separate public operational-safety hypothesis.
- `Progress.lean` - Statement of the progress property (well-typed expressions evaluate or diverge, never get stuck). Definition only; the repository contains no proof of it.
- `PredSatLawsWitness.lean` - Satisfiability witness for `PredSatLaws`: a tag meaning with a matchable guard (`v => v`), a satisfaction relation that meets both laws (`predSatLaws_idSat`), and a context in which `matchGuard` selects that guard. Imports `StepFRIte` for `matchGuard_ok_matched_owner`; a leaf of the import graph, not on the FR proof path.
- `ExternCallsWitnessBase.lean`, `ExternCallsWitness.lean`, `ExternCallsWitnessClosed.lean` - The premises on extern calls at small programs that call a pure extern `read` (the identity, result guarded by `w => w >= 0`). `ExternCallsWitnessBase` holds the shared pieces (`terminatesTo_det`, `pin_ge`, the lawful relation `geSat`, `SubStep` / `ExternCallAt` inversion, the registry and the run of a call of `read`). `ExternCallsWitness` proves *match* for the values the runs compute and refutes it for other values (`Wrapper`: one call site run twice; `Skipped`: a skipped branch also calls), and proves or refutes *agreement* (`TwoRuns.agree_iff`, `TwoCalls.two_calls_case`: two tagged calls per run, (5, 7)/(5, 7) agree, (5, 7)/(5, 8) do not). `ExternCallsWitnessClosed` gives the trusted entry of `read` (`readSpec`, its call contracts proved from the premises, through the facts about a typed call of any pure extern with a simple `int` return: `SimplePfnCallFacts`, `simplePfnCall_facts`, `valueConsistent_of_callMatches`, `resultAgreesIfClean_of_callAgrees`), `closed_of` (every other premise proved for these programs) and the four closed instances (`wrapper_closed`, `skipped_closed`, `twoRuns_closed`, `twoCalls_closed`). Imports `ExternProofs`, `FaultRobustnessProofs` and `ExternCallsWitness`; imported only by other witness modules, not on the FR proof path.
- `ExternCallsWitnessCell.lean` - The premises on extern calls at `rd (ref x)`, with `rd` an `extern fn` in the shape of `lp55xx_read` (reference argument, guarded return, an effect on the argument's cell with a guard of the same tag; the implementation writes `n / 2` to the cell holding `n`). `ExternCallAt.fn_inv` (inversion of an impure extern call), `cell_found` (the call writes the cell at address 0, stored as `poisoned { 0 }`), `match_of`, `agree_iff` (agreement holds exactly when the two runs leave the same content in the cell: inputs 4 and 5 agree, 4 and 6 do not), `callAgrees_refl` and the summary `cell_case`. Imports `ExternCallsWitnessBase`; imported only by `ExternCallsWitnessCellClosed`, not on the FR proof path.
- `ExternCallsWitnessCellClosed.lean` - A trusted entry for `rd` and the theorem applied to programs that call it, with every premise proved (namespace `ExternCallsWitness.Cell`). The call contracts `rd_callSingle`, `rd_callFR` (the two-run contract uses the clause of agreement for cells, in `cell_agree`; a target with several locations, a poisoned reference or a poisoned pc leaves the cell poisoned without a predicate), the declaration contracts `rd_declSingle`, `rd_declFR`, the boundary spec `rdSpec` and the registry `rdReg`; `cell_closed` / `cell_closed_4_5` (the theorem at `rd (ref x)`, nothing observed); `ReadBack` (`let c = ref x in let ret = rd c in if ret >= 0 then !c else 0`, the returned `int` observed): `readBack_case` (match in every run, agreement for inputs 4 and 5 but not 4 and 6), `same_return` (two runs whose calls leave the same content in the cell return the same value) and `run_prog`. The cell's guard has no predicate, so the clause of match for cells is not used. Imports `ExternCallsWitnessCell` and `ExternCallsWitnessClosed`; a leaf of the import graph, not on the FR proof path.
- `ExternCallsWitnessVal.lean` - A trusted entry for a guarded `extern val` and the theorem applied to a program that declares it, under both values of its tag (namespace `ExternCallsWitness.Val`). The declaration `vDecl` (`extern val @250 : (int :> poisoned { 0, w => w >= 0 })`, implementation `vI m`), the declaration contracts `v_declSingle` and `v_declFR` (agreement of the declared value proved inside `declFR`: both runs read the one implementation), the boundary spec `vSpec` (its call contracts hold because no call is typed against a declaration of kind `val`) and the registry `vReg`; the program `prog` (`let v = extern val @250 : ... in if v >= 0 then v else 0`) typed under `polV b`, which gives every tag of `@250` the value `b`, a clean `int` for both `b`; `match_iff` (match holds exactly when `0 ≤ m ↔ b = true`), `agree` (agreement holds for every pair of runs, which make no extern call), `val_case` (match for the tag true with `m = 5` and the tag false with `m = -3`, refuted for the two other pairs), `same_return` (under an assignment the value matches, two runs from any poisoned `x`, which the program does not read, return the same value) and the instances `true_5`, `false_neg3`. The proofs of the entry are specific to `@250`: one guard, on an `int`. Imports `ExternCallsWitnessBase` and `FaultRobustnessProofs`; a leaf of the import graph, not on the FR proof path.
- `ExternCallsWitnessInt.lean` - A trusted entry for an `extern val` whose guard reads a `let`-bound integer, and the theorem applied to a program that tests the value against it (namespace `ExternCallsWitness.IntGuard`). The declaration `extern val @250 : (int :> poisoned { 0, v => v >= lo })`, its declaration contracts `lo_declSingle` and `lo_declFR`, the boundary spec `loSpec` and the registry `loReg m` (the implementation is the value `m`); the program `let lo = 3 in let y = extern val @250 : ... in if y >= lo then 1 else x`, typed as a clean `int` in the context `K` (a poisoned `x`, every tag of `@250` true); the relation `loSat β` (the checked value is at least the value the view gives the binding number of `lo`) with `loSat_lawful` and, over any captured environment of the guard that holds `lo`, `loSat_lawful_cap`, and over any table whose entries are all that guard, `loSat_lawful_tbl`; `pin_lo` / `pin_lo_cap` / `pin_lo_tbl` (the laws fix a relation at the guard's tag: under a view that gives the number of `lo` the value `c`, it holds of an integer `n` exactly when `c ≤ n`); the view `βm m`, `tests` (`TestsAgreeWithView` holds for it) and `view_needed` (a view must give the number of `lo` the value 3); `match_iff_lawful` (match holds exactly when `3 ≤ m`), `same_return` (for `3 ≤ m`, two runs from any `x` return the same value, with every premise proved), the instance `true_5`, and `fails_0` / `no_premises_lt` (for `m < 3` the program is typed clean, the runs differ, and no relation and view meet the laws, the premise on tests and match). Also the premises about `K` shared with the modules below. Imports `ExternCallsWitnessBase` and `FaultRobustnessProofs`; imported only by other witness modules, not on the FR proof path.
- `ExternCallsWitnessIntCall.lean` - The integer guard on the result of a call of an extern function: `let lo = 3 in let g = extern pfn @250 n : (int :> clean {}) -> ((int :> poisoned { 0, v => v >= lo })) in let y = g 5 in if y >= lo then 1 else x` (namespace `ExternCallsWitness.IntCall`). The trusted entry `gSpec` in the registry `gReg m` (the implementation returns `m` whatever the argument), with its call contracts proved from `CallMatches` / `CallAgrees` and the facts of `ExternCallsWitnessClosed` on a pure extern with a simple `int` return. The call allocates the guard's tag, and the guard records `lo` with the number it has at its `let`. `typed_clean`, `programTable_eq`, `laws_program`, the view `βc m n`, `tests`, `view_needed`, `call_reached` (a run reaches the call, which returns `m`), `match_iff` (match, through the call, holds exactly when `3 ≤ m`), `match_iff_lawful`, `no_premises_lt`, `agree`, `same_return`, `true_5`, `fails_0`. Imports `ExternCallsWitnessInt` and `ExternCallsWitnessClosed`; a leaf of the import graph, not on the FR proof path.

**Helper modules:** `Auxiliary.lean`, `Equality.lean`, `VarEnvPreservation.lean`

**Dependency graph (extern boundary stack):**

```
Semantics → ExternRuntime → SemanticsProperties → StepFR → ExternBoundary → ExternBoundaryProofs
                                                                │                     ↓
                                                                │     FaultRobustnessProofs (orchestration)
                                                                ↓                     ↓
                                                          ExternProofs  →  ExternRegimeInt (program capstones)
                                                                                      ↓
                                              AbsFR, MaxCurriedFR, MemReadCapturesFR, GuardedCapturesFR
```

The split puts runtime extern event predicates and `RegistryOperationalSafe` *below* `StepFR` so `SemanticsProperties.lean` can consume them without an import cycle. FR-shaped contracts (`StepFRPost`-producing) live above `StepFR` in `ExternBoundary.lean`.

**Hub-split modules.** To decouple builds, `StepFR`'s heavy IH-free clusters and `StepFRApp`'s boundary-contract family were factored into dedicated modules without statement changes. Below `StepFR` (re-imported by it): `SemanticsProperties → ExternTagMeaning → TypecheckInduction → StepFR` (the extern-tagMeaning and `typecheckExpr`-preservation/lookup-origin clusters). Between `StepFR` and `StepFRApp`: `StepFR → StepFRClosureApply → ExternCallBoundarySides → StepFRApp` (closure-application machinery, then the parametrized Side / boundary-contract family). Editing any of these no longer rebuilds the other per-operator files.

**Module visibility / `private` discipline:** declarations used only within their declaring file are marked `private`. The `private` keyword scopes the binding to the file, which keeps the public surface of each module small and gives reviewers a quick read of "what is this module's API." When adding a new helper, default to `private` until another file actually needs it.

**Per-operator independence rule:** the `StepFR{App,Assign,Ite,Deref,NewRef,Seq,Vlet,Literal,Var,Op,FnPfn}.lean` files MUST NOT import each other. Any helper that two of them need belongs in a shared module (`StepFR.lean` for general step machinery, or `JoinMemberTransport.lean` for join-member transport). Because these files are mutually independent, edits to different per-operator files may be delegated to sub-agents in parallel — but run `lake build` sequentially afterwards (lake cannot build shared-dependency files concurrently).

### Other Components

- `Main.lean` - Interpreter entry point with CLI
- `parser/` - Tree-sitter grammar for `.poison` files
- `poison-lang-spec/` - Ott specification (`poison-lang.ott`)
- `examples/` - Test suite (`.poison` files with `.output` or `.fail` golden files)

## Specification and documentation

**Ott** (`poison-lang-spec/poison-lang.ott`): When syntax or typing rules change, keep **`doc/poison-lang-description.tex`** and **`examples/`** consistent (update tests and prose as needed).

**Narrative docs** (`doc/`): Describe the **current** language. Avoid changelog-style phrasing (for example, "we now support …").

**Markdown** (usually working notes under `doc/`): After editing, validate with `npx markdownlint-cli` (pass the file path or `doc/` as needed).

**Builds:** Use the targets in **Build Commands** above (`make poison-lang-spec`, `make doc`, `make parser`, etc.).

## Working with Implementation (LeanPoison/)

### Adding Language Features

When adding new expression types or operations:
1. Update `Syntax.lean` - add to `Expr` or `Op` inductive types
2. Update `BigStep.lean` - add evaluation case to `beval`
3. Update `Typecheck.lean` - add type checking rule
4. Update `poison-lang-spec/poison-lang.ott` - formal semantics
5. **Add test cases** in `examples/` with expected `.output` or `.fail` files
6. Run `make test` to verify correctness
7. Update proofs in `LeanProofs/` if needed

### Testing Implementation Changes

**Tests apply only to LeanPoison/, not LeanProofs/.**

The test suite (`scripts/run_tests.sh`) compares interpreter output against golden files:
- `.poison` + `.output` = expect successful execution with matching output
- `.poison` + `.fail` = expect non-zero exit code with matching error

To add a test:
1. Create `examples/testname.poison`
2. Run: `make run POISON=examples/testname.poison > examples/testname.output`
3. Review output, commit if correct

## Working with Proofs (LeanProofs/)

### Proof Development Guidelines

- **No testing**: Proofs are verified by compilation, not runtime tests
- **Predicate laws**: The fault-robustness specification assumes `PredSatLaws` for the starting tag meaning and for the program table of the typing run (`programTable` in `TagFrame.lean`); the step theorems receive a `TagFrame` for the allocations of their sub-run. Keep this premise about the one table of the program being typed, consistent with `RegimeConsistency` / typechecking. Each run has its own relation and its own view `β : BindVals` (the values the run gives to binding numbers); the laws are stated under the view, and the specification also assumes `TestsAgreeWithView` for each run (`ExternCallSteps.lean`)
- **Extern calls**: Values returned by extern calls are treated as inputs. The specification assumes `ExternCallsMatch` in each run and `ExternCallsAgree` for the pair (`ExternCallSteps.lean`), stated on the steps of the typing run; the step theorems carry them as `ExternStepPremises` for the current step, and the call contracts of a trusted entry receive `CallMatches` / `CallAgrees` for the call they are about (the returned value and the cells it writes through its effects), and the declaration contracts receive `ValMatches` for an `extern val` (agreement of the declared value in two runs is an obligation of the entry's author inside `declFR`). One runtime call typed against several members of a function type asks the conditions for each member
- **Conservative `sorry` use**: When you are proving deliberately, use `sorry` sparingly. The goal is to **decrease** the number of `sorry` statements (shrinking proof surface), not increase them. Adding more `sorry` goes in the wrong direction
- **Specification style**: Prefer **declarative / logical** specifications over functional encodings when both are reasonable (for example, membership predicates instead of `filter`-style definitions)
- **Inductive predicates**: For proof-relevant properties, prefer **inductive predicates** over `Bool` helpers so inversion is straightforward

Example (style preference):

```lean
-- Prefer: inductive predicate
inductive IsMember (x : α) : List α → Prop where
  | head : IsMember x (x :: _)
  | tail : IsMember x xs → IsMember x (_ :: xs)

-- Less convenient for proofs: functional encoding
def isMember (x : α) (xs : List α) : Bool :=
  xs.any (· = x)
```

- **Proof techniques**: Many proofs use structural induction on fuel or expression structure
- **Lean LSP tooling**: Use `lean-lsp` MCP tool to examine proof goals, errors, and search for lemmas
- **Bounded falsification check**: When a lemma looks suspicious, try 2–3 quick
  counterexample attempts before committing to a long proof. If you find a
  concrete counterexample, or a precise obstruction showing the statement cannot
  hold as written, stop and report it instead of forcing the proof.

## Lean 4 Workflows

`lean4` skills (`prove`, `autoprove`, `review`, `golf`, etc.) if available could be used.

### When Implementation Changes

When modifying type rules or evaluation in `LeanPoison/`:
1. Check that proofs in `LeanProofs/` still compile
2. Fix broken proofs if possible
3. Use `sorry` only if proof is complex and fixing it is not immediately feasible
4. Document any new `sorry` statements and plan to eliminate them

## Git and GitHub

- **Repository**: Project hosted on GitHub as `vzaliva/poison-lang`
- **Read-only git operations**: You may use `git` commands to review commit history, compare branches, and inspect changes
- **No repository modifications**: Never execute commands that modify the repository (e.g., `git commit`, `git push`, `git merge`)
- **GitHub CLI**: You may use `gh` commands to view or create issues or sub-issues (e.g. `gh sub-issue add <parent-issue-url> <sub-issue-url-or-number>`) but be wary of shell backtick handling (you may want to use `--body-file` to avoid issues with them)
- **Approval required**: Always request user approval before creating or modifying GitHub issues
